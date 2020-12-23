%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qQkrdGY2ug

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:35 EST 2020

% Result     : Theorem 6.13s
% Output     : Refutation 6.13s
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

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

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

thf('42',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X28 ) @ X31 @ ( k2_struct_0 @ X28 ) )
       != X30 )
      | ~ ( v4_pre_topc @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( v4_pre_topc @ X30 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t43_pre_topc])).

thf('43',plain,(
    ! [X28: $i,X29: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X29 )
      | ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X28 ) @ X31 @ ( k2_struct_0 @ X28 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X28 ) @ X31 @ ( k2_struct_0 @ X28 ) ) @ X28 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v4_pre_topc @ X31 @ X29 )
      | ~ ( m1_pre_topc @ X28 @ X29 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k9_subset_1 @ ( k2_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( v4_pre_topc @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ X0 )
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
      | ~ ( v4_pre_topc @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(demod,[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v4_pre_topc @ sk_B @ X0 )
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
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v4_pre_topc @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52','55'])).

thf('57',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','56'])).

thf('58',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_C_1 ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,
    ( ( v4_pre_topc @ ( k9_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_C_1 )
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
    v4_pre_topc @ sk_B @ sk_C_1 ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['2','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qQkrdGY2ug
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:19:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.13/6.34  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.13/6.34  % Solved by: fo/fo7.sh
% 6.13/6.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.13/6.34  % done 6066 iterations in 5.891s
% 6.13/6.34  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.13/6.34  % SZS output start Refutation
% 6.13/6.34  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.13/6.34  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.13/6.34  thf(sk_C_1_type, type, sk_C_1: $i).
% 6.13/6.34  thf(sk_D_3_type, type, sk_D_3: $i).
% 6.13/6.34  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.13/6.34  thf(sk_A_type, type, sk_A: $i).
% 6.13/6.34  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.13/6.34  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 6.13/6.34  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 6.13/6.34  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 6.13/6.34  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 6.13/6.34  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 6.13/6.34  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 6.13/6.34  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 6.13/6.34  thf(sk_B_type, type, sk_B: $i).
% 6.13/6.34  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.13/6.34  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 6.13/6.34  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 6.13/6.34  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 6.13/6.34  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.13/6.34  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 6.13/6.34  thf(t34_tops_2, conjecture,
% 6.13/6.34    (![A:$i]:
% 6.13/6.34     ( ( l1_pre_topc @ A ) =>
% 6.13/6.34       ( ![B:$i]:
% 6.13/6.34         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.13/6.34           ( ![C:$i]:
% 6.13/6.34             ( ( m1_pre_topc @ C @ A ) =>
% 6.13/6.34               ( ( v4_pre_topc @ B @ A ) =>
% 6.13/6.34                 ( ![D:$i]:
% 6.13/6.34                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 6.13/6.34                     ( ( ( D ) = ( B ) ) => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 6.13/6.34  thf(zf_stmt_0, negated_conjecture,
% 6.13/6.34    (~( ![A:$i]:
% 6.13/6.34        ( ( l1_pre_topc @ A ) =>
% 6.13/6.34          ( ![B:$i]:
% 6.13/6.34            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.13/6.34              ( ![C:$i]:
% 6.13/6.34                ( ( m1_pre_topc @ C @ A ) =>
% 6.13/6.34                  ( ( v4_pre_topc @ B @ A ) =>
% 6.13/6.34                    ( ![D:$i]:
% 6.13/6.34                      ( ( m1_subset_1 @
% 6.13/6.34                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 6.13/6.34                        ( ( ( D ) = ( B ) ) => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 6.13/6.34    inference('cnf.neg', [status(esa)], [t34_tops_2])).
% 6.13/6.34  thf('0', plain, (~ (v4_pre_topc @ sk_D_3 @ sk_C_1)),
% 6.13/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.34  thf('1', plain, (((sk_D_3) = (sk_B))),
% 6.13/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.34  thf('2', plain, (~ (v4_pre_topc @ sk_B @ sk_C_1)),
% 6.13/6.34      inference('demod', [status(thm)], ['0', '1'])).
% 6.13/6.34  thf(d3_struct_0, axiom,
% 6.13/6.34    (![A:$i]:
% 6.13/6.34     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 6.13/6.34  thf('3', plain,
% 6.13/6.34      (![X12 : $i]:
% 6.13/6.34         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 6.13/6.34      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.13/6.34  thf('4', plain,
% 6.13/6.34      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 6.13/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.34  thf('5', plain,
% 6.13/6.34      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 6.13/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.34  thf('6', plain, (((sk_D_3) = (sk_B))),
% 6.13/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.34  thf('7', plain,
% 6.13/6.34      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 6.13/6.34      inference('demod', [status(thm)], ['5', '6'])).
% 6.13/6.34  thf(dt_k1_pre_topc, axiom,
% 6.13/6.34    (![A:$i,B:$i]:
% 6.13/6.34     ( ( ( l1_pre_topc @ A ) & 
% 6.13/6.34         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.13/6.34       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 6.13/6.34         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 6.13/6.34  thf('8', plain,
% 6.13/6.34      (![X23 : $i, X24 : $i]:
% 6.13/6.34         (~ (l1_pre_topc @ X23)
% 6.13/6.34          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 6.13/6.34          | (m1_pre_topc @ (k1_pre_topc @ X23 @ X24) @ X23))),
% 6.13/6.34      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 6.13/6.34  thf('9', plain,
% 6.13/6.34      (((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)
% 6.13/6.34        | ~ (l1_pre_topc @ sk_C_1))),
% 6.13/6.34      inference('sup-', [status(thm)], ['7', '8'])).
% 6.13/6.34  thf('10', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 6.13/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.34  thf(dt_m1_pre_topc, axiom,
% 6.13/6.34    (![A:$i]:
% 6.13/6.34     ( ( l1_pre_topc @ A ) =>
% 6.13/6.34       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 6.13/6.34  thf('11', plain,
% 6.13/6.34      (![X26 : $i, X27 : $i]:
% 6.13/6.34         (~ (m1_pre_topc @ X26 @ X27)
% 6.13/6.34          | (l1_pre_topc @ X26)
% 6.13/6.34          | ~ (l1_pre_topc @ X27))),
% 6.13/6.34      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 6.13/6.34  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 6.13/6.34      inference('sup-', [status(thm)], ['10', '11'])).
% 6.13/6.34  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 6.13/6.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.34  thf('14', plain, ((l1_pre_topc @ sk_C_1)),
% 6.13/6.34      inference('demod', [status(thm)], ['12', '13'])).
% 6.13/6.34  thf('15', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)),
% 6.13/6.34      inference('demod', [status(thm)], ['9', '14'])).
% 6.13/6.34  thf(d9_pre_topc, axiom,
% 6.13/6.34    (![A:$i]:
% 6.13/6.34     ( ( l1_pre_topc @ A ) =>
% 6.13/6.34       ( ![B:$i]:
% 6.13/6.34         ( ( l1_pre_topc @ B ) =>
% 6.13/6.35           ( ( m1_pre_topc @ B @ A ) <=>
% 6.13/6.35             ( ( ![C:$i]:
% 6.13/6.35                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 6.13/6.35                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 6.13/6.35                     ( ?[D:$i]:
% 6.13/6.35                       ( ( m1_subset_1 @
% 6.13/6.35                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 6.13/6.35                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 6.13/6.35                         ( ( C ) =
% 6.13/6.35                           ( k9_subset_1 @
% 6.13/6.35                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 6.13/6.35               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 6.13/6.35  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 6.13/6.35  thf(zf_stmt_2, axiom,
% 6.13/6.35    (![D:$i,C:$i,B:$i,A:$i]:
% 6.13/6.35     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 6.13/6.35       ( ( ( C ) =
% 6.13/6.35           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 6.13/6.35         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 6.13/6.35         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 6.13/6.35  thf(zf_stmt_3, axiom,
% 6.13/6.35    (![A:$i]:
% 6.13/6.35     ( ( l1_pre_topc @ A ) =>
% 6.13/6.35       ( ![B:$i]:
% 6.13/6.35         ( ( l1_pre_topc @ B ) =>
% 6.13/6.35           ( ( m1_pre_topc @ B @ A ) <=>
% 6.13/6.35             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 6.13/6.35               ( ![C:$i]:
% 6.13/6.35                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 6.13/6.35                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 6.13/6.35                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 6.13/6.35  thf('16', plain,
% 6.13/6.35      (![X18 : $i, X19 : $i]:
% 6.13/6.35         (~ (l1_pre_topc @ X18)
% 6.13/6.35          | ~ (m1_pre_topc @ X18 @ X19)
% 6.13/6.35          | (r1_tarski @ (k2_struct_0 @ X18) @ (k2_struct_0 @ X19))
% 6.13/6.35          | ~ (l1_pre_topc @ X19))),
% 6.13/6.35      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.13/6.35  thf('17', plain,
% 6.13/6.35      ((~ (l1_pre_topc @ sk_C_1)
% 6.13/6.35        | (r1_tarski @ (k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) @ 
% 6.13/6.35           (k2_struct_0 @ sk_C_1))
% 6.13/6.35        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 6.13/6.35      inference('sup-', [status(thm)], ['15', '16'])).
% 6.13/6.35  thf('18', plain, ((l1_pre_topc @ sk_C_1)),
% 6.13/6.35      inference('demod', [status(thm)], ['12', '13'])).
% 6.13/6.35  thf('19', plain,
% 6.13/6.35      (((r1_tarski @ (k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) @ 
% 6.13/6.35         (k2_struct_0 @ sk_C_1))
% 6.13/6.35        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 6.13/6.35      inference('demod', [status(thm)], ['17', '18'])).
% 6.13/6.35  thf('20', plain,
% 6.13/6.35      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 6.13/6.35      inference('demod', [status(thm)], ['5', '6'])).
% 6.13/6.35  thf(d10_pre_topc, axiom,
% 6.13/6.35    (![A:$i]:
% 6.13/6.35     ( ( l1_pre_topc @ A ) =>
% 6.13/6.35       ( ![B:$i]:
% 6.13/6.35         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.13/6.35           ( ![C:$i]:
% 6.13/6.35             ( ( ( v1_pre_topc @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 6.13/6.35               ( ( ( C ) = ( k1_pre_topc @ A @ B ) ) <=>
% 6.13/6.35                 ( ( k2_struct_0 @ C ) = ( B ) ) ) ) ) ) ) ))).
% 6.13/6.35  thf('21', plain,
% 6.13/6.35      (![X9 : $i, X10 : $i, X11 : $i]:
% 6.13/6.35         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 6.13/6.35          | ((X11) != (k1_pre_topc @ X10 @ X9))
% 6.13/6.35          | ((k2_struct_0 @ X11) = (X9))
% 6.13/6.35          | ~ (m1_pre_topc @ X11 @ X10)
% 6.13/6.35          | ~ (v1_pre_topc @ X11)
% 6.13/6.35          | ~ (l1_pre_topc @ X10))),
% 6.13/6.35      inference('cnf', [status(esa)], [d10_pre_topc])).
% 6.13/6.35  thf('22', plain,
% 6.13/6.35      (![X9 : $i, X10 : $i]:
% 6.13/6.35         (~ (l1_pre_topc @ X10)
% 6.13/6.35          | ~ (v1_pre_topc @ (k1_pre_topc @ X10 @ X9))
% 6.13/6.35          | ~ (m1_pre_topc @ (k1_pre_topc @ X10 @ X9) @ X10)
% 6.13/6.35          | ((k2_struct_0 @ (k1_pre_topc @ X10 @ X9)) = (X9))
% 6.13/6.35          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 6.13/6.35      inference('simplify', [status(thm)], ['21'])).
% 6.13/6.35  thf('23', plain,
% 6.13/6.35      ((((k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) = (sk_B))
% 6.13/6.35        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)
% 6.13/6.35        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))
% 6.13/6.35        | ~ (l1_pre_topc @ sk_C_1))),
% 6.13/6.35      inference('sup-', [status(thm)], ['20', '22'])).
% 6.13/6.35  thf('24', plain,
% 6.13/6.35      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 6.13/6.35      inference('demod', [status(thm)], ['5', '6'])).
% 6.13/6.35  thf('25', plain,
% 6.13/6.35      (![X23 : $i, X24 : $i]:
% 6.13/6.35         (~ (l1_pre_topc @ X23)
% 6.13/6.35          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 6.13/6.35          | (v1_pre_topc @ (k1_pre_topc @ X23 @ X24)))),
% 6.13/6.35      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 6.13/6.35  thf('26', plain,
% 6.13/6.35      (((v1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))
% 6.13/6.35        | ~ (l1_pre_topc @ sk_C_1))),
% 6.13/6.35      inference('sup-', [status(thm)], ['24', '25'])).
% 6.13/6.35  thf('27', plain, ((l1_pre_topc @ sk_C_1)),
% 6.13/6.35      inference('demod', [status(thm)], ['12', '13'])).
% 6.13/6.35  thf('28', plain, ((v1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))),
% 6.13/6.35      inference('demod', [status(thm)], ['26', '27'])).
% 6.13/6.35  thf('29', plain, ((l1_pre_topc @ sk_C_1)),
% 6.13/6.35      inference('demod', [status(thm)], ['12', '13'])).
% 6.13/6.35  thf('30', plain,
% 6.13/6.35      ((((k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) = (sk_B))
% 6.13/6.35        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1))),
% 6.13/6.35      inference('demod', [status(thm)], ['23', '28', '29'])).
% 6.13/6.35  thf('31', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)),
% 6.13/6.35      inference('demod', [status(thm)], ['9', '14'])).
% 6.13/6.35  thf('32', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) = (sk_B))),
% 6.13/6.35      inference('demod', [status(thm)], ['30', '31'])).
% 6.13/6.35  thf('33', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)),
% 6.13/6.35      inference('demod', [status(thm)], ['9', '14'])).
% 6.13/6.35  thf('34', plain,
% 6.13/6.35      (![X26 : $i, X27 : $i]:
% 6.13/6.35         (~ (m1_pre_topc @ X26 @ X27)
% 6.13/6.35          | (l1_pre_topc @ X26)
% 6.13/6.35          | ~ (l1_pre_topc @ X27))),
% 6.13/6.35      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 6.13/6.35  thf('35', plain,
% 6.13/6.35      ((~ (l1_pre_topc @ sk_C_1)
% 6.13/6.35        | (l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 6.13/6.35      inference('sup-', [status(thm)], ['33', '34'])).
% 6.13/6.35  thf('36', plain, ((l1_pre_topc @ sk_C_1)),
% 6.13/6.35      inference('demod', [status(thm)], ['12', '13'])).
% 6.13/6.35  thf('37', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))),
% 6.13/6.35      inference('demod', [status(thm)], ['35', '36'])).
% 6.13/6.35  thf('38', plain, ((r1_tarski @ sk_B @ (k2_struct_0 @ sk_C_1))),
% 6.13/6.35      inference('demod', [status(thm)], ['19', '32', '37'])).
% 6.13/6.35  thf(t28_xboole_1, axiom,
% 6.13/6.35    (![A:$i,B:$i]:
% 6.13/6.35     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 6.13/6.35  thf('39', plain,
% 6.13/6.35      (![X0 : $i, X1 : $i]:
% 6.13/6.35         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 6.13/6.35      inference('cnf', [status(esa)], [t28_xboole_1])).
% 6.13/6.35  thf('40', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C_1)) = (sk_B))),
% 6.13/6.35      inference('sup-', [status(thm)], ['38', '39'])).
% 6.13/6.35  thf('41', plain,
% 6.13/6.35      (![X12 : $i]:
% 6.13/6.35         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 6.13/6.35      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.13/6.35  thf(t43_pre_topc, axiom,
% 6.13/6.35    (![A:$i]:
% 6.13/6.35     ( ( l1_pre_topc @ A ) =>
% 6.13/6.35       ( ![B:$i]:
% 6.13/6.35         ( ( m1_pre_topc @ B @ A ) =>
% 6.13/6.35           ( ![C:$i]:
% 6.13/6.35             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 6.13/6.35               ( ( v4_pre_topc @ C @ B ) <=>
% 6.13/6.35                 ( ?[D:$i]:
% 6.13/6.35                   ( ( ( k9_subset_1 @
% 6.13/6.35                         ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) =
% 6.13/6.35                       ( C ) ) & 
% 6.13/6.35                     ( v4_pre_topc @ D @ A ) & 
% 6.13/6.35                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 6.13/6.35  thf('42', plain,
% 6.13/6.35      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 6.13/6.35         (~ (m1_pre_topc @ X28 @ X29)
% 6.13/6.35          | ((k9_subset_1 @ (u1_struct_0 @ X28) @ X31 @ (k2_struct_0 @ X28))
% 6.13/6.35              != (X30))
% 6.13/6.35          | ~ (v4_pre_topc @ X31 @ X29)
% 6.13/6.35          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 6.13/6.35          | (v4_pre_topc @ X30 @ X28)
% 6.13/6.35          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 6.13/6.35          | ~ (l1_pre_topc @ X29))),
% 6.13/6.35      inference('cnf', [status(esa)], [t43_pre_topc])).
% 6.13/6.35  thf('43', plain,
% 6.13/6.35      (![X28 : $i, X29 : $i, X31 : $i]:
% 6.13/6.35         (~ (l1_pre_topc @ X29)
% 6.13/6.35          | ~ (m1_subset_1 @ 
% 6.13/6.35               (k9_subset_1 @ (u1_struct_0 @ X28) @ X31 @ (k2_struct_0 @ X28)) @ 
% 6.13/6.35               (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 6.13/6.35          | (v4_pre_topc @ 
% 6.13/6.35             (k9_subset_1 @ (u1_struct_0 @ X28) @ X31 @ (k2_struct_0 @ X28)) @ 
% 6.13/6.35             X28)
% 6.13/6.35          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 6.13/6.35          | ~ (v4_pre_topc @ X31 @ X29)
% 6.13/6.35          | ~ (m1_pre_topc @ X28 @ X29))),
% 6.13/6.35      inference('simplify', [status(thm)], ['42'])).
% 6.13/6.35  thf('44', plain,
% 6.13/6.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.13/6.35         (~ (m1_subset_1 @ 
% 6.13/6.35             (k9_subset_1 @ (k2_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ 
% 6.13/6.35             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 6.13/6.35          | ~ (l1_struct_0 @ X0)
% 6.13/6.35          | ~ (m1_pre_topc @ X0 @ X2)
% 6.13/6.35          | ~ (v4_pre_topc @ X1 @ X2)
% 6.13/6.35          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 6.13/6.35          | (v4_pre_topc @ 
% 6.13/6.35             (k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ X0)
% 6.13/6.35          | ~ (l1_pre_topc @ X2))),
% 6.13/6.35      inference('sup-', [status(thm)], ['41', '43'])).
% 6.13/6.35  thf(dt_k2_subset_1, axiom,
% 6.13/6.35    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 6.13/6.35  thf('45', plain,
% 6.13/6.35      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 6.13/6.35      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 6.13/6.35  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 6.13/6.35  thf('46', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 6.13/6.35      inference('cnf', [status(esa)], [d4_subset_1])).
% 6.13/6.35  thf('47', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 6.13/6.35      inference('demod', [status(thm)], ['45', '46'])).
% 6.13/6.35  thf(redefinition_k9_subset_1, axiom,
% 6.13/6.35    (![A:$i,B:$i,C:$i]:
% 6.13/6.35     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 6.13/6.35       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 6.13/6.35  thf('48', plain,
% 6.13/6.35      (![X4 : $i, X5 : $i, X6 : $i]:
% 6.13/6.35         (((k9_subset_1 @ X6 @ X4 @ X5) = (k3_xboole_0 @ X4 @ X5))
% 6.13/6.35          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 6.13/6.35      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 6.13/6.35  thf('49', plain,
% 6.13/6.35      (![X0 : $i, X1 : $i]:
% 6.13/6.35         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 6.13/6.35      inference('sup-', [status(thm)], ['47', '48'])).
% 6.13/6.35  thf('50', plain,
% 6.13/6.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.13/6.35         (~ (m1_subset_1 @ (k3_xboole_0 @ X1 @ (k2_struct_0 @ X0)) @ 
% 6.13/6.35             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 6.13/6.35          | ~ (l1_struct_0 @ X0)
% 6.13/6.35          | ~ (m1_pre_topc @ X0 @ X2)
% 6.13/6.35          | ~ (v4_pre_topc @ X1 @ X2)
% 6.13/6.35          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 6.13/6.35          | (v4_pre_topc @ 
% 6.13/6.35             (k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ X0)
% 6.13/6.35          | ~ (l1_pre_topc @ X2))),
% 6.13/6.35      inference('demod', [status(thm)], ['44', '49'])).
% 6.13/6.35  thf('51', plain,
% 6.13/6.35      (![X0 : $i]:
% 6.13/6.35         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 6.13/6.35          | ~ (l1_pre_topc @ X0)
% 6.13/6.35          | (v4_pre_topc @ 
% 6.13/6.35             (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ 
% 6.13/6.35              (k2_struct_0 @ sk_C_1)) @ 
% 6.13/6.35             sk_C_1)
% 6.13/6.35          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 6.13/6.35          | ~ (v4_pre_topc @ sk_B @ X0)
% 6.13/6.35          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 6.13/6.35          | ~ (l1_struct_0 @ sk_C_1))),
% 6.13/6.35      inference('sup-', [status(thm)], ['40', '50'])).
% 6.13/6.35  thf('52', plain,
% 6.13/6.35      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 6.13/6.35      inference('demod', [status(thm)], ['5', '6'])).
% 6.13/6.35  thf('53', plain, ((l1_pre_topc @ sk_C_1)),
% 6.13/6.35      inference('demod', [status(thm)], ['12', '13'])).
% 6.13/6.35  thf(dt_l1_pre_topc, axiom,
% 6.13/6.35    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 6.13/6.35  thf('54', plain,
% 6.13/6.35      (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 6.13/6.35      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 6.13/6.35  thf('55', plain, ((l1_struct_0 @ sk_C_1)),
% 6.13/6.35      inference('sup-', [status(thm)], ['53', '54'])).
% 6.13/6.35  thf('56', plain,
% 6.13/6.35      (![X0 : $i]:
% 6.13/6.35         (~ (l1_pre_topc @ X0)
% 6.13/6.35          | (v4_pre_topc @ 
% 6.13/6.35             (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ 
% 6.13/6.35              (k2_struct_0 @ sk_C_1)) @ 
% 6.13/6.35             sk_C_1)
% 6.13/6.35          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 6.13/6.35          | ~ (v4_pre_topc @ sk_B @ X0)
% 6.13/6.35          | ~ (m1_pre_topc @ sk_C_1 @ X0))),
% 6.13/6.35      inference('demod', [status(thm)], ['51', '52', '55'])).
% 6.13/6.35  thf('57', plain,
% 6.13/6.35      ((~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 6.13/6.35        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 6.13/6.35        | (v4_pre_topc @ 
% 6.13/6.35           (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ 
% 6.13/6.35            (k2_struct_0 @ sk_C_1)) @ 
% 6.13/6.35           sk_C_1)
% 6.13/6.35        | ~ (l1_pre_topc @ sk_A))),
% 6.13/6.35      inference('sup-', [status(thm)], ['4', '56'])).
% 6.13/6.35  thf('58', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 6.13/6.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.35  thf('59', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 6.13/6.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.35  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 6.13/6.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.13/6.35  thf('61', plain,
% 6.13/6.35      ((v4_pre_topc @ 
% 6.13/6.35        (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ (k2_struct_0 @ sk_C_1)) @ 
% 6.13/6.35        sk_C_1)),
% 6.13/6.35      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 6.13/6.35  thf('62', plain,
% 6.13/6.35      (((v4_pre_topc @ 
% 6.13/6.35         (k9_subset_1 @ (k2_struct_0 @ sk_C_1) @ sk_B @ (k2_struct_0 @ sk_C_1)) @ 
% 6.13/6.35         sk_C_1)
% 6.13/6.35        | ~ (l1_struct_0 @ sk_C_1))),
% 6.13/6.35      inference('sup+', [status(thm)], ['3', '61'])).
% 6.13/6.35  thf('63', plain,
% 6.13/6.35      (![X0 : $i, X1 : $i]:
% 6.13/6.35         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 6.13/6.35      inference('sup-', [status(thm)], ['47', '48'])).
% 6.13/6.35  thf('64', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C_1)) = (sk_B))),
% 6.13/6.35      inference('sup-', [status(thm)], ['38', '39'])).
% 6.13/6.35  thf('65', plain, ((l1_struct_0 @ sk_C_1)),
% 6.13/6.35      inference('sup-', [status(thm)], ['53', '54'])).
% 6.13/6.35  thf('66', plain, ((v4_pre_topc @ sk_B @ sk_C_1)),
% 6.13/6.35      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 6.13/6.35  thf('67', plain, ($false), inference('demod', [status(thm)], ['2', '66'])).
% 6.13/6.35  
% 6.13/6.35  % SZS output end Refutation
% 6.13/6.35  
% 6.13/6.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
