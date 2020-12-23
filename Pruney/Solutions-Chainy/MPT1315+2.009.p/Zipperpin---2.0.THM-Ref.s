%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aL9pM96xca

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:34 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 699 expanded)
%              Number of leaves         :   35 ( 214 expanded)
%              Depth                    :   16
%              Number of atoms          :  853 (8586 expanded)
%              Number of equality atoms :   39 ( 338 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

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
    ~ ( v4_pre_topc @ sk_D_3 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_D_3 = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ~ ( v4_pre_topc @ sk_B @ sk_C_1 ) ),
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
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X2 @ X4 @ X3 )
        = ( k9_subset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_pre_topc @ X32 @ X33 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X32 ) @ X35 @ ( k2_struct_0 @ X32 ) )
       != X34 )
      | ~ ( v4_pre_topc @ X35 @ X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( v4_pre_topc @ X34 @ X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t43_pre_topc])).

thf('14',plain,(
    ! [X32: $i,X33: $i,X35: $i] :
      ( ~ ( l1_pre_topc @ X33 )
      | ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X32 ) @ X35 @ ( k2_struct_0 @ X32 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X32 ) @ X35 @ ( k2_struct_0 @ X32 ) ) @ X32 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( v4_pre_topc @ X35 @ X33 )
      | ~ ( m1_pre_topc @ X32 @ X33 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k3_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( v4_pre_topc @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_C_1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('16',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X6 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('17',plain,(
    ! [X5: $i] :
      ( ( k2_subset_1 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('18',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X2 @ X4 @ X3 )
        = ( k9_subset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k9_subset_1 @ X0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k9_subset_1 @ X9 @ X7 @ X8 )
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_subset_1 @ X0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('26',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X28 @ X29 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('27',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('29',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( l1_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(demod,[status(thm)],['27','32'])).

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

thf('34',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_pre_topc @ X23 @ X24 )
      | ( r1_tarski @ ( k2_struct_0 @ X23 ) @ ( k2_struct_0 @ X24 ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['30','31'])).

thf('37',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( X17
       != ( k1_pre_topc @ X16 @ X15 ) )
      | ( ( k2_struct_0 @ X17 )
        = X15 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ~ ( v1_pre_topc @ X17 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d10_pre_topc])).

thf('40',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X16 @ X15 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X16 @ X15 ) @ X16 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
      = sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('43',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('44',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['30','31'])).

thf('46',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['30','31'])).

thf('48',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
      = sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['41','46','47'])).

thf('49',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(demod,[status(thm)],['27','32'])).

thf('50',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(demod,[status(thm)],['27','32'])).

thf('52',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( l1_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['30','31'])).

thf('55',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    r1_tarski @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['37','50','55'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('57',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k9_subset_1 @ X9 @ X7 @ X8 )
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C_1 ) )
    = ( k3_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['24','60'])).

thf('62',plain,(
    r1_tarski @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['37','50','55'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('64',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C_1 ) )
    = sk_B ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( sk_B
    = ( k3_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ sk_B ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('68',plain,
    ( sk_B
    = ( k3_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ sk_B ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( v4_pre_topc @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v4_pre_topc @ sk_B @ sk_C_1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['15','65','66','67','68'])).

thf('70',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_C_1 )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v4_pre_topc @ sk_B @ sk_C_1 ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['2','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aL9pM96xca
% 0.10/0.32  % Computer   : n011.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % DateTime   : Tue Dec  1 18:01:12 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  % Running portfolio for 600 s
% 0.10/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.10/0.32  % Number of cores: 8
% 0.17/0.32  % Python version: Python 3.6.8
% 0.17/0.33  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 285 iterations in 0.160s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.59  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.41/0.59  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.41/0.59  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.41/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.59  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.41/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.41/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.41/0.59  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.41/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.59  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.41/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.41/0.59  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.41/0.59  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.41/0.59  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.41/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.41/0.59  thf(t34_tops_2, conjecture,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( l1_pre_topc @ A ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.59           ( ![C:$i]:
% 0.41/0.59             ( ( m1_pre_topc @ C @ A ) =>
% 0.41/0.59               ( ( v4_pre_topc @ B @ A ) =>
% 0.41/0.59                 ( ![D:$i]:
% 0.41/0.59                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.41/0.59                     ( ( ( D ) = ( B ) ) => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.59    (~( ![A:$i]:
% 0.41/0.59        ( ( l1_pre_topc @ A ) =>
% 0.41/0.59          ( ![B:$i]:
% 0.41/0.59            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.59              ( ![C:$i]:
% 0.41/0.59                ( ( m1_pre_topc @ C @ A ) =>
% 0.41/0.59                  ( ( v4_pre_topc @ B @ A ) =>
% 0.41/0.59                    ( ![D:$i]:
% 0.41/0.59                      ( ( m1_subset_1 @
% 0.41/0.59                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.41/0.59                        ( ( ( D ) = ( B ) ) => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.41/0.59    inference('cnf.neg', [status(esa)], [t34_tops_2])).
% 0.41/0.59  thf('0', plain, (~ (v4_pre_topc @ sk_D_3 @ sk_C_1)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('1', plain, (((sk_D_3) = (sk_B))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('2', plain, (~ (v4_pre_topc @ sk_B @ sk_C_1)),
% 0.41/0.59      inference('demod', [status(thm)], ['0', '1'])).
% 0.41/0.59  thf('3', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('4', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('5', plain, (((sk_D_3) = (sk_B))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('6', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.41/0.59      inference('demod', [status(thm)], ['4', '5'])).
% 0.41/0.59  thf(commutativity_k9_subset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.59       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.41/0.59  thf('7', plain,
% 0.41/0.59      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.59         (((k9_subset_1 @ X2 @ X4 @ X3) = (k9_subset_1 @ X2 @ X3 @ X4))
% 0.41/0.59          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.41/0.59      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.41/0.59  thf('8', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ X0 @ sk_B)
% 0.41/0.59           = (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.41/0.59  thf('9', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.41/0.59      inference('demod', [status(thm)], ['4', '5'])).
% 0.41/0.59  thf(redefinition_k9_subset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.59       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.41/0.59  thf('10', plain,
% 0.41/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.41/0.59         (((k9_subset_1 @ X9 @ X7 @ X8) = (k3_xboole_0 @ X7 @ X8))
% 0.41/0.59          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.41/0.59      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.41/0.59  thf('11', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ X0 @ sk_B)
% 0.41/0.59           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.41/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.41/0.59  thf('12', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k3_xboole_0 @ X0 @ sk_B)
% 0.41/0.59           = (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ X0))),
% 0.41/0.59      inference('demod', [status(thm)], ['8', '11'])).
% 0.41/0.59  thf(t43_pre_topc, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( l1_pre_topc @ A ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( m1_pre_topc @ B @ A ) =>
% 0.41/0.59           ( ![C:$i]:
% 0.41/0.59             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.41/0.59               ( ( v4_pre_topc @ C @ B ) <=>
% 0.41/0.59                 ( ?[D:$i]:
% 0.41/0.59                   ( ( ( k9_subset_1 @
% 0.41/0.59                         ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) =
% 0.41/0.59                       ( C ) ) & 
% 0.41/0.59                     ( v4_pre_topc @ D @ A ) & 
% 0.41/0.59                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.59  thf('13', plain,
% 0.41/0.59      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.41/0.59         (~ (m1_pre_topc @ X32 @ X33)
% 0.41/0.59          | ((k9_subset_1 @ (u1_struct_0 @ X32) @ X35 @ (k2_struct_0 @ X32))
% 0.41/0.59              != (X34))
% 0.41/0.59          | ~ (v4_pre_topc @ X35 @ X33)
% 0.41/0.59          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.41/0.59          | (v4_pre_topc @ X34 @ X32)
% 0.41/0.59          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.41/0.59          | ~ (l1_pre_topc @ X33))),
% 0.41/0.59      inference('cnf', [status(esa)], [t43_pre_topc])).
% 0.41/0.59  thf('14', plain,
% 0.41/0.59      (![X32 : $i, X33 : $i, X35 : $i]:
% 0.41/0.59         (~ (l1_pre_topc @ X33)
% 0.41/0.59          | ~ (m1_subset_1 @ 
% 0.41/0.59               (k9_subset_1 @ (u1_struct_0 @ X32) @ X35 @ (k2_struct_0 @ X32)) @ 
% 0.41/0.59               (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.41/0.59          | (v4_pre_topc @ 
% 0.41/0.59             (k9_subset_1 @ (u1_struct_0 @ X32) @ X35 @ (k2_struct_0 @ X32)) @ 
% 0.41/0.59             X32)
% 0.41/0.59          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.41/0.59          | ~ (v4_pre_topc @ X35 @ X33)
% 0.41/0.59          | ~ (m1_pre_topc @ X32 @ X33))),
% 0.41/0.59      inference('simplify', [status(thm)], ['13'])).
% 0.41/0.59  thf('15', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ (k3_xboole_0 @ (k2_struct_0 @ sk_C_1) @ sk_B) @ 
% 0.41/0.59             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.41/0.59          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.41/0.59          | ~ (v4_pre_topc @ sk_B @ X0)
% 0.41/0.59          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.41/0.59          | (v4_pre_topc @ 
% 0.41/0.59             (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ 
% 0.41/0.59              (k2_struct_0 @ sk_C_1)) @ 
% 0.41/0.59             sk_C_1)
% 0.41/0.59          | ~ (l1_pre_topc @ X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['12', '14'])).
% 0.41/0.59  thf(dt_k2_subset_1, axiom,
% 0.41/0.59    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.41/0.59  thf('16', plain,
% 0.41/0.59      (![X6 : $i]: (m1_subset_1 @ (k2_subset_1 @ X6) @ (k1_zfmisc_1 @ X6))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.41/0.59  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.41/0.59  thf('17', plain, (![X5 : $i]: ((k2_subset_1 @ X5) = (X5))),
% 0.41/0.59      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.41/0.59  thf('18', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.41/0.59      inference('demod', [status(thm)], ['16', '17'])).
% 0.41/0.59  thf('19', plain,
% 0.41/0.59      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.41/0.59         (((k9_subset_1 @ X2 @ X4 @ X3) = (k9_subset_1 @ X2 @ X3 @ X4))
% 0.41/0.59          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.41/0.59      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.41/0.59  thf('20', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((k9_subset_1 @ X0 @ X1 @ X0) = (k9_subset_1 @ X0 @ X0 @ X1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.59  thf('21', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.41/0.59      inference('demod', [status(thm)], ['16', '17'])).
% 0.41/0.59  thf('22', plain,
% 0.41/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.41/0.59         (((k9_subset_1 @ X9 @ X7 @ X8) = (k3_xboole_0 @ X7 @ X8))
% 0.41/0.59          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.41/0.59      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.41/0.59  thf('23', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.59  thf('24', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((k3_xboole_0 @ X1 @ X0) = (k9_subset_1 @ X0 @ X0 @ X1))),
% 0.41/0.59      inference('demod', [status(thm)], ['20', '23'])).
% 0.41/0.59  thf('25', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.41/0.59      inference('demod', [status(thm)], ['4', '5'])).
% 0.41/0.59  thf(dt_k1_pre_topc, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( l1_pre_topc @ A ) & 
% 0.41/0.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.41/0.59       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.41/0.59         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.41/0.59  thf('26', plain,
% 0.41/0.59      (![X28 : $i, X29 : $i]:
% 0.41/0.59         (~ (l1_pre_topc @ X28)
% 0.41/0.59          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.41/0.59          | (m1_pre_topc @ (k1_pre_topc @ X28 @ X29) @ X28))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.41/0.59  thf('27', plain,
% 0.41/0.59      (((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)
% 0.41/0.59        | ~ (l1_pre_topc @ sk_C_1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['25', '26'])).
% 0.41/0.59  thf('28', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(dt_m1_pre_topc, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( l1_pre_topc @ A ) =>
% 0.41/0.59       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.41/0.59  thf('29', plain,
% 0.41/0.59      (![X30 : $i, X31 : $i]:
% 0.41/0.59         (~ (m1_pre_topc @ X30 @ X31)
% 0.41/0.59          | (l1_pre_topc @ X30)
% 0.41/0.59          | ~ (l1_pre_topc @ X31))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.41/0.59  thf('30', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['28', '29'])).
% 0.41/0.59  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('32', plain, ((l1_pre_topc @ sk_C_1)),
% 0.41/0.59      inference('demod', [status(thm)], ['30', '31'])).
% 0.41/0.59  thf('33', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.41/0.59      inference('demod', [status(thm)], ['27', '32'])).
% 0.41/0.59  thf(d9_pre_topc, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( l1_pre_topc @ A ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( l1_pre_topc @ B ) =>
% 0.41/0.59           ( ( m1_pre_topc @ B @ A ) <=>
% 0.41/0.59             ( ( ![C:$i]:
% 0.41/0.59                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.41/0.59                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.41/0.59                     ( ?[D:$i]:
% 0.41/0.59                       ( ( m1_subset_1 @
% 0.41/0.59                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.41/0.59                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.41/0.59                         ( ( C ) =
% 0.41/0.59                           ( k9_subset_1 @
% 0.41/0.59                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 0.41/0.59               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 0.41/0.59  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.41/0.59  thf(zf_stmt_2, axiom,
% 0.41/0.59    (![D:$i,C:$i,B:$i,A:$i]:
% 0.41/0.59     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.41/0.59       ( ( ( C ) =
% 0.41/0.59           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 0.41/0.59         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.41/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.41/0.59  thf(zf_stmt_3, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( l1_pre_topc @ A ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( l1_pre_topc @ B ) =>
% 0.41/0.59           ( ( m1_pre_topc @ B @ A ) <=>
% 0.41/0.59             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 0.41/0.59               ( ![C:$i]:
% 0.41/0.59                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.41/0.59                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.41/0.59                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.59  thf('34', plain,
% 0.41/0.59      (![X23 : $i, X24 : $i]:
% 0.41/0.59         (~ (l1_pre_topc @ X23)
% 0.41/0.59          | ~ (m1_pre_topc @ X23 @ X24)
% 0.41/0.59          | (r1_tarski @ (k2_struct_0 @ X23) @ (k2_struct_0 @ X24))
% 0.41/0.59          | ~ (l1_pre_topc @ X24))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.41/0.59  thf('35', plain,
% 0.41/0.59      ((~ (l1_pre_topc @ sk_C_1)
% 0.41/0.59        | (r1_tarski @ (k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) @ 
% 0.41/0.59           (k2_struct_0 @ sk_C_1))
% 0.41/0.59        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.41/0.59  thf('36', plain, ((l1_pre_topc @ sk_C_1)),
% 0.41/0.59      inference('demod', [status(thm)], ['30', '31'])).
% 0.41/0.59  thf('37', plain,
% 0.41/0.59      (((r1_tarski @ (k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) @ 
% 0.41/0.59         (k2_struct_0 @ sk_C_1))
% 0.41/0.59        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 0.41/0.59      inference('demod', [status(thm)], ['35', '36'])).
% 0.41/0.59  thf('38', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.41/0.59      inference('demod', [status(thm)], ['4', '5'])).
% 0.41/0.59  thf(d10_pre_topc, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ( l1_pre_topc @ A ) =>
% 0.41/0.59       ( ![B:$i]:
% 0.41/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.41/0.59           ( ![C:$i]:
% 0.41/0.59             ( ( ( v1_pre_topc @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.41/0.59               ( ( ( C ) = ( k1_pre_topc @ A @ B ) ) <=>
% 0.41/0.59                 ( ( k2_struct_0 @ C ) = ( B ) ) ) ) ) ) ) ))).
% 0.41/0.59  thf('39', plain,
% 0.41/0.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.41/0.59          | ((X17) != (k1_pre_topc @ X16 @ X15))
% 0.41/0.59          | ((k2_struct_0 @ X17) = (X15))
% 0.41/0.59          | ~ (m1_pre_topc @ X17 @ X16)
% 0.41/0.59          | ~ (v1_pre_topc @ X17)
% 0.41/0.59          | ~ (l1_pre_topc @ X16))),
% 0.41/0.59      inference('cnf', [status(esa)], [d10_pre_topc])).
% 0.41/0.59  thf('40', plain,
% 0.41/0.59      (![X15 : $i, X16 : $i]:
% 0.41/0.59         (~ (l1_pre_topc @ X16)
% 0.41/0.59          | ~ (v1_pre_topc @ (k1_pre_topc @ X16 @ X15))
% 0.41/0.59          | ~ (m1_pre_topc @ (k1_pre_topc @ X16 @ X15) @ X16)
% 0.41/0.59          | ((k2_struct_0 @ (k1_pre_topc @ X16 @ X15)) = (X15))
% 0.41/0.59          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16))))),
% 0.41/0.59      inference('simplify', [status(thm)], ['39'])).
% 0.41/0.59  thf('41', plain,
% 0.41/0.59      ((((k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) = (sk_B))
% 0.41/0.59        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)
% 0.41/0.59        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))
% 0.41/0.59        | ~ (l1_pre_topc @ sk_C_1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['38', '40'])).
% 0.41/0.59  thf('42', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.41/0.59      inference('demod', [status(thm)], ['4', '5'])).
% 0.41/0.59  thf('43', plain,
% 0.41/0.59      (![X28 : $i, X29 : $i]:
% 0.41/0.59         (~ (l1_pre_topc @ X28)
% 0.41/0.59          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.41/0.59          | (v1_pre_topc @ (k1_pre_topc @ X28 @ X29)))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.41/0.59  thf('44', plain,
% 0.41/0.59      (((v1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))
% 0.41/0.59        | ~ (l1_pre_topc @ sk_C_1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['42', '43'])).
% 0.41/0.59  thf('45', plain, ((l1_pre_topc @ sk_C_1)),
% 0.41/0.59      inference('demod', [status(thm)], ['30', '31'])).
% 0.41/0.59  thf('46', plain, ((v1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))),
% 0.41/0.59      inference('demod', [status(thm)], ['44', '45'])).
% 0.41/0.59  thf('47', plain, ((l1_pre_topc @ sk_C_1)),
% 0.41/0.59      inference('demod', [status(thm)], ['30', '31'])).
% 0.41/0.59  thf('48', plain,
% 0.41/0.59      ((((k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) = (sk_B))
% 0.41/0.59        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.41/0.59      inference('demod', [status(thm)], ['41', '46', '47'])).
% 0.41/0.59  thf('49', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.41/0.59      inference('demod', [status(thm)], ['27', '32'])).
% 0.41/0.59  thf('50', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) = (sk_B))),
% 0.41/0.59      inference('demod', [status(thm)], ['48', '49'])).
% 0.41/0.59  thf('51', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.41/0.59      inference('demod', [status(thm)], ['27', '32'])).
% 0.41/0.59  thf('52', plain,
% 0.41/0.59      (![X30 : $i, X31 : $i]:
% 0.41/0.59         (~ (m1_pre_topc @ X30 @ X31)
% 0.41/0.59          | (l1_pre_topc @ X30)
% 0.41/0.59          | ~ (l1_pre_topc @ X31))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.41/0.59  thf('53', plain,
% 0.41/0.59      ((~ (l1_pre_topc @ sk_C_1)
% 0.41/0.59        | (l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['51', '52'])).
% 0.41/0.59  thf('54', plain, ((l1_pre_topc @ sk_C_1)),
% 0.41/0.59      inference('demod', [status(thm)], ['30', '31'])).
% 0.41/0.59  thf('55', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))),
% 0.41/0.59      inference('demod', [status(thm)], ['53', '54'])).
% 0.41/0.59  thf('56', plain, ((r1_tarski @ sk_B @ (k2_struct_0 @ sk_C_1))),
% 0.41/0.59      inference('demod', [status(thm)], ['37', '50', '55'])).
% 0.41/0.59  thf(t3_subset, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.41/0.59  thf('57', plain,
% 0.41/0.59      (![X12 : $i, X14 : $i]:
% 0.41/0.59         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.41/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.59  thf('58', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C_1)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['56', '57'])).
% 0.41/0.59  thf('59', plain,
% 0.41/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.41/0.59         (((k9_subset_1 @ X9 @ X7 @ X8) = (k3_xboole_0 @ X7 @ X8))
% 0.41/0.59          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.41/0.59      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.41/0.59  thf('60', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k9_subset_1 @ (k2_struct_0 @ sk_C_1) @ X0 @ sk_B)
% 0.41/0.59           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.41/0.59      inference('sup-', [status(thm)], ['58', '59'])).
% 0.41/0.59  thf('61', plain,
% 0.41/0.59      (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C_1))
% 0.41/0.59         = (k3_xboole_0 @ (k2_struct_0 @ sk_C_1) @ sk_B))),
% 0.41/0.59      inference('sup+', [status(thm)], ['24', '60'])).
% 0.41/0.59  thf('62', plain, ((r1_tarski @ sk_B @ (k2_struct_0 @ sk_C_1))),
% 0.41/0.59      inference('demod', [status(thm)], ['37', '50', '55'])).
% 0.41/0.59  thf(t28_xboole_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.59  thf('63', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.41/0.59      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.59  thf('64', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C_1)) = (sk_B))),
% 0.41/0.59      inference('sup-', [status(thm)], ['62', '63'])).
% 0.41/0.59  thf('65', plain, (((sk_B) = (k3_xboole_0 @ (k2_struct_0 @ sk_C_1) @ sk_B))),
% 0.41/0.59      inference('demod', [status(thm)], ['61', '64'])).
% 0.41/0.59  thf('66', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.41/0.59      inference('demod', [status(thm)], ['4', '5'])).
% 0.41/0.59  thf('67', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         ((k3_xboole_0 @ X0 @ sk_B)
% 0.41/0.59           = (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ X0))),
% 0.41/0.59      inference('demod', [status(thm)], ['8', '11'])).
% 0.41/0.59  thf('68', plain, (((sk_B) = (k3_xboole_0 @ (k2_struct_0 @ sk_C_1) @ sk_B))),
% 0.41/0.59      inference('demod', [status(thm)], ['61', '64'])).
% 0.41/0.59  thf('69', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.41/0.59          | ~ (v4_pre_topc @ sk_B @ X0)
% 0.41/0.59          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.41/0.59          | (v4_pre_topc @ sk_B @ sk_C_1)
% 0.41/0.59          | ~ (l1_pre_topc @ X0))),
% 0.41/0.59      inference('demod', [status(thm)], ['15', '65', '66', '67', '68'])).
% 0.41/0.59  thf('70', plain,
% 0.41/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.41/0.59        | (v4_pre_topc @ sk_B @ sk_C_1)
% 0.41/0.59        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.41/0.59        | ~ (m1_pre_topc @ sk_C_1 @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['3', '69'])).
% 0.41/0.59  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('72', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('73', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('74', plain, ((v4_pre_topc @ sk_B @ sk_C_1)),
% 0.41/0.59      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.41/0.59  thf('75', plain, ($false), inference('demod', [status(thm)], ['2', '74'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.41/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
