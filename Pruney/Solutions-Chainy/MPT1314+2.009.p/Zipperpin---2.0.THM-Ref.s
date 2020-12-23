%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MP1u4JWc9D

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:32 EST 2020

% Result     : Theorem 5.95s
% Output     : Refutation 5.95s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 386 expanded)
%              Number of leaves         :   36 ( 127 expanded)
%              Depth                    :   16
%              Number of atoms          :  808 (4635 expanded)
%              Number of equality atoms :   29 ( 172 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

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

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_D_3 = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X23 @ X24 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('9',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('11',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( l1_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(demod,[status(thm)],['9','14'])).

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

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X19 )
      | ( r1_tarski @ ( k2_struct_0 @ X18 ) @ ( k2_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('17',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('19',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

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

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( X11
       != ( k1_pre_topc @ X10 @ X9 ) )
      | ( ( k2_struct_0 @ X11 )
        = X9 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ~ ( v1_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_pre_topc])).

thf('22',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X10 @ X9 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X10 @ X9 ) @ X10 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X10 @ X9 ) )
        = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
      = sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('25',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('26',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('28',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('30',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
      = sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['23','28','29'])).

thf('31',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(demod,[status(thm)],['9','14'])).

thf('32',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(demod,[status(thm)],['9','14'])).

thf('34',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( l1_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('37',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['19','32','37'])).

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
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C_1 ) )
    = sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('42',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X28 ) @ X31 @ ( k2_struct_0 @ X28 ) )
       != X30 )
      | ~ ( v3_pre_topc @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v3_pre_topc @ X30 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t32_tops_2])).

thf('43',plain,(
    ! [X28: $i,X29: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X28 ) @ X31 @ ( k2_struct_0 @ X28 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X28 ) @ X31 @ ( k2_struct_0 @ X28 ) ) @ X28 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v3_pre_topc @ X31 @ X29 )
      | ~ ( m1_pre_topc @ X28 @ X29 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k9_subset_1 @ ( k2_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( v3_pre_topc @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('45',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('46',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('47',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('48',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k9_subset_1 @ X6 @ X4 @ X5 )
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( v3_pre_topc @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(demod,[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( l1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['40','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('53',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('54',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('55',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','55'])).

thf('57',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','56'])).

thf('58',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_C_1 ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,
    ( ( v3_pre_topc @ ( k9_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['3','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('64',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C_1 ) )
    = sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('65',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['53','54'])).

thf('66',plain,(
    v3_pre_topc @ sk_B @ sk_C_1 ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['2','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MP1u4JWc9D
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:37:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.95/6.15  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.95/6.15  % Solved by: fo/fo7.sh
% 5.95/6.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.95/6.15  % done 6066 iterations in 5.698s
% 5.95/6.15  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.95/6.15  % SZS output start Refutation
% 5.95/6.15  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.95/6.15  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.95/6.15  thf(sk_C_1_type, type, sk_C_1: $i).
% 5.95/6.15  thf(sk_D_3_type, type, sk_D_3: $i).
% 5.95/6.15  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.95/6.15  thf(sk_A_type, type, sk_A: $i).
% 5.95/6.15  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 5.95/6.15  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 5.95/6.15  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 5.95/6.15  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 5.95/6.15  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 5.95/6.15  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 5.95/6.15  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 5.95/6.15  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.95/6.15  thf(sk_B_type, type, sk_B: $i).
% 5.95/6.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.95/6.15  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 5.95/6.15  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 5.95/6.15  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 5.95/6.15  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.95/6.15  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 5.95/6.15  thf(t33_tops_2, conjecture,
% 5.95/6.15    (![A:$i]:
% 5.95/6.15     ( ( l1_pre_topc @ A ) =>
% 5.95/6.15       ( ![B:$i]:
% 5.95/6.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.95/6.15           ( ![C:$i]:
% 5.95/6.15             ( ( m1_pre_topc @ C @ A ) =>
% 5.95/6.15               ( ( v3_pre_topc @ B @ A ) =>
% 5.95/6.15                 ( ![D:$i]:
% 5.95/6.15                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 5.95/6.15                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 5.95/6.15  thf(zf_stmt_0, negated_conjecture,
% 5.95/6.15    (~( ![A:$i]:
% 5.95/6.15        ( ( l1_pre_topc @ A ) =>
% 5.95/6.15          ( ![B:$i]:
% 5.95/6.15            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.95/6.15              ( ![C:$i]:
% 5.95/6.15                ( ( m1_pre_topc @ C @ A ) =>
% 5.95/6.15                  ( ( v3_pre_topc @ B @ A ) =>
% 5.95/6.15                    ( ![D:$i]:
% 5.95/6.15                      ( ( m1_subset_1 @
% 5.95/6.15                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 5.95/6.15                        ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 5.95/6.15    inference('cnf.neg', [status(esa)], [t33_tops_2])).
% 5.95/6.15  thf('0', plain, (~ (v3_pre_topc @ sk_D_3 @ sk_C_1)),
% 5.95/6.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.95/6.15  thf('1', plain, (((sk_D_3) = (sk_B))),
% 5.95/6.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.95/6.15  thf('2', plain, (~ (v3_pre_topc @ sk_B @ sk_C_1)),
% 5.95/6.15      inference('demod', [status(thm)], ['0', '1'])).
% 5.95/6.15  thf(d3_struct_0, axiom,
% 5.95/6.15    (![A:$i]:
% 5.95/6.15     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 5.95/6.15  thf('3', plain,
% 5.95/6.15      (![X12 : $i]:
% 5.95/6.15         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 5.95/6.15      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.95/6.15  thf('4', plain,
% 5.95/6.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.95/6.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.95/6.15  thf('5', plain,
% 5.95/6.15      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 5.95/6.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.95/6.15  thf('6', plain, (((sk_D_3) = (sk_B))),
% 5.95/6.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.95/6.15  thf('7', plain,
% 5.95/6.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 5.95/6.15      inference('demod', [status(thm)], ['5', '6'])).
% 5.95/6.15  thf(dt_k1_pre_topc, axiom,
% 5.95/6.15    (![A:$i,B:$i]:
% 5.95/6.15     ( ( ( l1_pre_topc @ A ) & 
% 5.95/6.15         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.95/6.15       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 5.95/6.15         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 5.95/6.15  thf('8', plain,
% 5.95/6.15      (![X23 : $i, X24 : $i]:
% 5.95/6.15         (~ (l1_pre_topc @ X23)
% 5.95/6.15          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 5.95/6.15          | (m1_pre_topc @ (k1_pre_topc @ X23 @ X24) @ X23))),
% 5.95/6.15      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 5.95/6.15  thf('9', plain,
% 5.95/6.15      (((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)
% 5.95/6.15        | ~ (l1_pre_topc @ sk_C_1))),
% 5.95/6.15      inference('sup-', [status(thm)], ['7', '8'])).
% 5.95/6.15  thf('10', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 5.95/6.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.95/6.15  thf(dt_m1_pre_topc, axiom,
% 5.95/6.15    (![A:$i]:
% 5.95/6.15     ( ( l1_pre_topc @ A ) =>
% 5.95/6.15       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 5.95/6.15  thf('11', plain,
% 5.95/6.15      (![X26 : $i, X27 : $i]:
% 5.95/6.15         (~ (m1_pre_topc @ X26 @ X27)
% 5.95/6.15          | (l1_pre_topc @ X26)
% 5.95/6.15          | ~ (l1_pre_topc @ X27))),
% 5.95/6.15      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 5.95/6.15  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 5.95/6.15      inference('sup-', [status(thm)], ['10', '11'])).
% 5.95/6.15  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 5.95/6.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.95/6.15  thf('14', plain, ((l1_pre_topc @ sk_C_1)),
% 5.95/6.15      inference('demod', [status(thm)], ['12', '13'])).
% 5.95/6.15  thf('15', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)),
% 5.95/6.15      inference('demod', [status(thm)], ['9', '14'])).
% 5.95/6.15  thf(d9_pre_topc, axiom,
% 5.95/6.15    (![A:$i]:
% 5.95/6.15     ( ( l1_pre_topc @ A ) =>
% 5.95/6.15       ( ![B:$i]:
% 5.95/6.15         ( ( l1_pre_topc @ B ) =>
% 5.95/6.15           ( ( m1_pre_topc @ B @ A ) <=>
% 5.95/6.15             ( ( ![C:$i]:
% 5.95/6.15                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 5.95/6.15                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 5.95/6.15                     ( ?[D:$i]:
% 5.95/6.15                       ( ( m1_subset_1 @
% 5.95/6.15                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 5.95/6.15                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 5.95/6.15                         ( ( C ) =
% 5.95/6.15                           ( k9_subset_1 @
% 5.95/6.15                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 5.95/6.15               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 5.95/6.15  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 5.95/6.15  thf(zf_stmt_2, axiom,
% 5.95/6.15    (![D:$i,C:$i,B:$i,A:$i]:
% 5.95/6.15     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 5.95/6.15       ( ( ( C ) =
% 5.95/6.15           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 5.95/6.15         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 5.95/6.15         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 5.95/6.15  thf(zf_stmt_3, axiom,
% 5.95/6.15    (![A:$i]:
% 5.95/6.15     ( ( l1_pre_topc @ A ) =>
% 5.95/6.15       ( ![B:$i]:
% 5.95/6.15         ( ( l1_pre_topc @ B ) =>
% 5.95/6.15           ( ( m1_pre_topc @ B @ A ) <=>
% 5.95/6.15             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 5.95/6.15               ( ![C:$i]:
% 5.95/6.15                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 5.95/6.15                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 5.95/6.15                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 5.95/6.15  thf('16', plain,
% 5.95/6.15      (![X18 : $i, X19 : $i]:
% 5.95/6.15         (~ (l1_pre_topc @ X18)
% 5.95/6.15          | ~ (m1_pre_topc @ X18 @ X19)
% 5.95/6.15          | (r1_tarski @ (k2_struct_0 @ X18) @ (k2_struct_0 @ X19))
% 5.95/6.15          | ~ (l1_pre_topc @ X19))),
% 5.95/6.15      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.95/6.15  thf('17', plain,
% 5.95/6.15      ((~ (l1_pre_topc @ sk_C_1)
% 5.95/6.15        | (r1_tarski @ (k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) @ 
% 5.95/6.15           (k2_struct_0 @ sk_C_1))
% 5.95/6.15        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 5.95/6.15      inference('sup-', [status(thm)], ['15', '16'])).
% 5.95/6.15  thf('18', plain, ((l1_pre_topc @ sk_C_1)),
% 5.95/6.15      inference('demod', [status(thm)], ['12', '13'])).
% 5.95/6.15  thf('19', plain,
% 5.95/6.15      (((r1_tarski @ (k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) @ 
% 5.95/6.15         (k2_struct_0 @ sk_C_1))
% 5.95/6.15        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 5.95/6.15      inference('demod', [status(thm)], ['17', '18'])).
% 5.95/6.15  thf('20', plain,
% 5.95/6.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 5.95/6.15      inference('demod', [status(thm)], ['5', '6'])).
% 5.95/6.15  thf(d10_pre_topc, axiom,
% 5.95/6.15    (![A:$i]:
% 5.95/6.15     ( ( l1_pre_topc @ A ) =>
% 5.95/6.15       ( ![B:$i]:
% 5.95/6.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.95/6.15           ( ![C:$i]:
% 5.95/6.15             ( ( ( v1_pre_topc @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 5.95/6.15               ( ( ( C ) = ( k1_pre_topc @ A @ B ) ) <=>
% 5.95/6.15                 ( ( k2_struct_0 @ C ) = ( B ) ) ) ) ) ) ) ))).
% 5.95/6.15  thf('21', plain,
% 5.95/6.15      (![X9 : $i, X10 : $i, X11 : $i]:
% 5.95/6.15         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 5.95/6.15          | ((X11) != (k1_pre_topc @ X10 @ X9))
% 5.95/6.15          | ((k2_struct_0 @ X11) = (X9))
% 5.95/6.15          | ~ (m1_pre_topc @ X11 @ X10)
% 5.95/6.15          | ~ (v1_pre_topc @ X11)
% 5.95/6.15          | ~ (l1_pre_topc @ X10))),
% 5.95/6.15      inference('cnf', [status(esa)], [d10_pre_topc])).
% 5.95/6.15  thf('22', plain,
% 5.95/6.15      (![X9 : $i, X10 : $i]:
% 5.95/6.15         (~ (l1_pre_topc @ X10)
% 5.95/6.15          | ~ (v1_pre_topc @ (k1_pre_topc @ X10 @ X9))
% 5.95/6.15          | ~ (m1_pre_topc @ (k1_pre_topc @ X10 @ X9) @ X10)
% 5.95/6.15          | ((k2_struct_0 @ (k1_pre_topc @ X10 @ X9)) = (X9))
% 5.95/6.15          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 5.95/6.15      inference('simplify', [status(thm)], ['21'])).
% 5.95/6.15  thf('23', plain,
% 5.95/6.15      ((((k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) = (sk_B))
% 5.95/6.15        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)
% 5.95/6.15        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))
% 5.95/6.15        | ~ (l1_pre_topc @ sk_C_1))),
% 5.95/6.15      inference('sup-', [status(thm)], ['20', '22'])).
% 5.95/6.15  thf('24', plain,
% 5.95/6.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 5.95/6.15      inference('demod', [status(thm)], ['5', '6'])).
% 5.95/6.15  thf('25', plain,
% 5.95/6.15      (![X23 : $i, X24 : $i]:
% 5.95/6.15         (~ (l1_pre_topc @ X23)
% 5.95/6.15          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 5.95/6.15          | (v1_pre_topc @ (k1_pre_topc @ X23 @ X24)))),
% 5.95/6.15      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 5.95/6.15  thf('26', plain,
% 5.95/6.15      (((v1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))
% 5.95/6.15        | ~ (l1_pre_topc @ sk_C_1))),
% 5.95/6.15      inference('sup-', [status(thm)], ['24', '25'])).
% 5.95/6.15  thf('27', plain, ((l1_pre_topc @ sk_C_1)),
% 5.95/6.15      inference('demod', [status(thm)], ['12', '13'])).
% 5.95/6.15  thf('28', plain, ((v1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))),
% 5.95/6.15      inference('demod', [status(thm)], ['26', '27'])).
% 5.95/6.15  thf('29', plain, ((l1_pre_topc @ sk_C_1)),
% 5.95/6.15      inference('demod', [status(thm)], ['12', '13'])).
% 5.95/6.15  thf('30', plain,
% 5.95/6.15      ((((k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) = (sk_B))
% 5.95/6.15        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1))),
% 5.95/6.15      inference('demod', [status(thm)], ['23', '28', '29'])).
% 5.95/6.15  thf('31', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)),
% 5.95/6.15      inference('demod', [status(thm)], ['9', '14'])).
% 5.95/6.15  thf('32', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) = (sk_B))),
% 5.95/6.15      inference('demod', [status(thm)], ['30', '31'])).
% 5.95/6.15  thf('33', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)),
% 5.95/6.15      inference('demod', [status(thm)], ['9', '14'])).
% 5.95/6.15  thf('34', plain,
% 5.95/6.15      (![X26 : $i, X27 : $i]:
% 5.95/6.15         (~ (m1_pre_topc @ X26 @ X27)
% 5.95/6.15          | (l1_pre_topc @ X26)
% 5.95/6.15          | ~ (l1_pre_topc @ X27))),
% 5.95/6.15      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 5.95/6.15  thf('35', plain,
% 5.95/6.15      ((~ (l1_pre_topc @ sk_C_1)
% 5.95/6.15        | (l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 5.95/6.15      inference('sup-', [status(thm)], ['33', '34'])).
% 5.95/6.15  thf('36', plain, ((l1_pre_topc @ sk_C_1)),
% 5.95/6.15      inference('demod', [status(thm)], ['12', '13'])).
% 5.95/6.15  thf('37', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))),
% 5.95/6.15      inference('demod', [status(thm)], ['35', '36'])).
% 5.95/6.15  thf('38', plain, ((r1_tarski @ sk_B @ (k2_struct_0 @ sk_C_1))),
% 5.95/6.15      inference('demod', [status(thm)], ['19', '32', '37'])).
% 5.95/6.15  thf(t28_xboole_1, axiom,
% 5.95/6.15    (![A:$i,B:$i]:
% 5.95/6.15     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 5.95/6.15  thf('39', plain,
% 5.95/6.15      (![X0 : $i, X1 : $i]:
% 5.95/6.15         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 5.95/6.15      inference('cnf', [status(esa)], [t28_xboole_1])).
% 5.95/6.15  thf('40', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C_1)) = (sk_B))),
% 5.95/6.15      inference('sup-', [status(thm)], ['38', '39'])).
% 5.95/6.15  thf('41', plain,
% 5.95/6.15      (![X12 : $i]:
% 5.95/6.15         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 5.95/6.15      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.95/6.15  thf(t32_tops_2, axiom,
% 5.95/6.15    (![A:$i]:
% 5.95/6.15     ( ( l1_pre_topc @ A ) =>
% 5.95/6.15       ( ![B:$i]:
% 5.95/6.15         ( ( m1_pre_topc @ B @ A ) =>
% 5.95/6.15           ( ![C:$i]:
% 5.95/6.15             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 5.95/6.15               ( ( v3_pre_topc @ C @ B ) <=>
% 5.95/6.15                 ( ?[D:$i]:
% 5.95/6.15                   ( ( ( k9_subset_1 @
% 5.95/6.15                         ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) =
% 5.95/6.15                       ( C ) ) & 
% 5.95/6.15                     ( v3_pre_topc @ D @ A ) & 
% 5.95/6.15                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 5.95/6.15  thf('42', plain,
% 5.95/6.15      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 5.95/6.15         (~ (m1_pre_topc @ X28 @ X29)
% 5.95/6.15          | ((k9_subset_1 @ (u1_struct_0 @ X28) @ X31 @ (k2_struct_0 @ X28))
% 5.95/6.15              != (X30))
% 5.95/6.15          | ~ (v3_pre_topc @ X31 @ X29)
% 5.95/6.15          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 5.95/6.15          | (v3_pre_topc @ X30 @ X28)
% 5.95/6.15          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 5.95/6.15          | ~ (l1_pre_topc @ X29))),
% 5.95/6.15      inference('cnf', [status(esa)], [t32_tops_2])).
% 5.95/6.15  thf('43', plain,
% 5.95/6.15      (![X28 : $i, X29 : $i, X31 : $i]:
% 5.95/6.15         (~ (l1_pre_topc @ X29)
% 5.95/6.15          | ~ (m1_subset_1 @ 
% 5.95/6.15               (k9_subset_1 @ (u1_struct_0 @ X28) @ X31 @ (k2_struct_0 @ X28)) @ 
% 5.95/6.15               (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 5.95/6.15          | (v3_pre_topc @ 
% 5.95/6.15             (k9_subset_1 @ (u1_struct_0 @ X28) @ X31 @ (k2_struct_0 @ X28)) @ 
% 5.95/6.15             X28)
% 5.95/6.15          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 5.95/6.15          | ~ (v3_pre_topc @ X31 @ X29)
% 5.95/6.15          | ~ (m1_pre_topc @ X28 @ X29))),
% 5.95/6.15      inference('simplify', [status(thm)], ['42'])).
% 5.95/6.15  thf('44', plain,
% 5.95/6.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.95/6.15         (~ (m1_subset_1 @ 
% 5.95/6.15             (k9_subset_1 @ (k2_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ 
% 5.95/6.15             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 5.95/6.15          | ~ (l1_struct_0 @ X0)
% 5.95/6.15          | ~ (m1_pre_topc @ X0 @ X2)
% 5.95/6.15          | ~ (v3_pre_topc @ X1 @ X2)
% 5.95/6.15          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 5.95/6.15          | (v3_pre_topc @ 
% 5.95/6.15             (k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ X0)
% 5.95/6.15          | ~ (l1_pre_topc @ X2))),
% 5.95/6.15      inference('sup-', [status(thm)], ['41', '43'])).
% 5.95/6.15  thf(dt_k2_subset_1, axiom,
% 5.95/6.15    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 5.95/6.15  thf('45', plain,
% 5.95/6.15      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 5.95/6.15      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 5.95/6.15  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 5.95/6.15  thf('46', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 5.95/6.15      inference('cnf', [status(esa)], [d4_subset_1])).
% 5.95/6.15  thf('47', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 5.95/6.15      inference('demod', [status(thm)], ['45', '46'])).
% 5.95/6.15  thf(redefinition_k9_subset_1, axiom,
% 5.95/6.15    (![A:$i,B:$i,C:$i]:
% 5.95/6.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 5.95/6.15       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 5.95/6.15  thf('48', plain,
% 5.95/6.15      (![X4 : $i, X5 : $i, X6 : $i]:
% 5.95/6.15         (((k9_subset_1 @ X6 @ X4 @ X5) = (k3_xboole_0 @ X4 @ X5))
% 5.95/6.15          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 5.95/6.15      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 5.95/6.15  thf('49', plain,
% 5.95/6.15      (![X0 : $i, X1 : $i]:
% 5.95/6.15         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 5.95/6.15      inference('sup-', [status(thm)], ['47', '48'])).
% 5.95/6.15  thf('50', plain,
% 5.95/6.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.95/6.15         (~ (m1_subset_1 @ (k3_xboole_0 @ X1 @ (k2_struct_0 @ X0)) @ 
% 5.95/6.15             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 5.95/6.15          | ~ (l1_struct_0 @ X0)
% 5.95/6.15          | ~ (m1_pre_topc @ X0 @ X2)
% 5.95/6.15          | ~ (v3_pre_topc @ X1 @ X2)
% 5.95/6.15          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 5.95/6.15          | (v3_pre_topc @ 
% 5.95/6.15             (k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ X0)
% 5.95/6.15          | ~ (l1_pre_topc @ X2))),
% 5.95/6.15      inference('demod', [status(thm)], ['44', '49'])).
% 5.95/6.15  thf('51', plain,
% 5.95/6.15      (![X0 : $i]:
% 5.95/6.15         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 5.95/6.15          | ~ (l1_pre_topc @ X0)
% 5.95/6.15          | (v3_pre_topc @ 
% 5.95/6.15             (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ 
% 5.95/6.15              (k2_struct_0 @ sk_C_1)) @ 
% 5.95/6.15             sk_C_1)
% 5.95/6.15          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 5.95/6.15          | ~ (v3_pre_topc @ sk_B @ X0)
% 5.95/6.15          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 5.95/6.15          | ~ (l1_struct_0 @ sk_C_1))),
% 5.95/6.15      inference('sup-', [status(thm)], ['40', '50'])).
% 5.95/6.15  thf('52', plain,
% 5.95/6.15      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 5.95/6.15      inference('demod', [status(thm)], ['5', '6'])).
% 5.95/6.15  thf('53', plain, ((l1_pre_topc @ sk_C_1)),
% 5.95/6.15      inference('demod', [status(thm)], ['12', '13'])).
% 5.95/6.15  thf(dt_l1_pre_topc, axiom,
% 5.95/6.15    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 5.95/6.15  thf('54', plain,
% 5.95/6.15      (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 5.95/6.15      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 5.95/6.15  thf('55', plain, ((l1_struct_0 @ sk_C_1)),
% 5.95/6.15      inference('sup-', [status(thm)], ['53', '54'])).
% 5.95/6.15  thf('56', plain,
% 5.95/6.15      (![X0 : $i]:
% 5.95/6.15         (~ (l1_pre_topc @ X0)
% 5.95/6.15          | (v3_pre_topc @ 
% 5.95/6.15             (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ 
% 5.95/6.15              (k2_struct_0 @ sk_C_1)) @ 
% 5.95/6.15             sk_C_1)
% 5.95/6.15          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 5.95/6.15          | ~ (v3_pre_topc @ sk_B @ X0)
% 5.95/6.15          | ~ (m1_pre_topc @ sk_C_1 @ X0))),
% 5.95/6.15      inference('demod', [status(thm)], ['51', '52', '55'])).
% 5.95/6.15  thf('57', plain,
% 5.95/6.15      ((~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 5.95/6.15        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 5.95/6.15        | (v3_pre_topc @ 
% 5.95/6.15           (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ 
% 5.95/6.15            (k2_struct_0 @ sk_C_1)) @ 
% 5.95/6.15           sk_C_1)
% 5.95/6.15        | ~ (l1_pre_topc @ sk_A))),
% 5.95/6.15      inference('sup-', [status(thm)], ['4', '56'])).
% 5.95/6.15  thf('58', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 5.95/6.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.95/6.15  thf('59', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 5.95/6.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.95/6.15  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 5.95/6.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.95/6.15  thf('61', plain,
% 5.95/6.15      ((v3_pre_topc @ 
% 5.95/6.15        (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ (k2_struct_0 @ sk_C_1)) @ 
% 5.95/6.15        sk_C_1)),
% 5.95/6.15      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 5.95/6.15  thf('62', plain,
% 5.95/6.15      (((v3_pre_topc @ 
% 5.95/6.15         (k9_subset_1 @ (k2_struct_0 @ sk_C_1) @ sk_B @ (k2_struct_0 @ sk_C_1)) @ 
% 5.95/6.15         sk_C_1)
% 5.95/6.15        | ~ (l1_struct_0 @ sk_C_1))),
% 5.95/6.15      inference('sup+', [status(thm)], ['3', '61'])).
% 5.95/6.15  thf('63', plain,
% 5.95/6.15      (![X0 : $i, X1 : $i]:
% 5.95/6.15         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 5.95/6.15      inference('sup-', [status(thm)], ['47', '48'])).
% 5.95/6.15  thf('64', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C_1)) = (sk_B))),
% 5.95/6.15      inference('sup-', [status(thm)], ['38', '39'])).
% 5.95/6.15  thf('65', plain, ((l1_struct_0 @ sk_C_1)),
% 5.95/6.15      inference('sup-', [status(thm)], ['53', '54'])).
% 5.95/6.15  thf('66', plain, ((v3_pre_topc @ sk_B @ sk_C_1)),
% 5.95/6.15      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 5.95/6.15  thf('67', plain, ($false), inference('demod', [status(thm)], ['2', '66'])).
% 5.95/6.15  
% 5.95/6.15  % SZS output end Refutation
% 5.95/6.15  
% 5.95/6.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
