%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5WuV2yZ22P

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:32 EST 2020

% Result     : Theorem 10.31s
% Output     : Refutation 10.31s
% Verified   : 
% Statistics : Number of formulae       :  191 (1105 expanded)
%              Number of leaves         :   34 ( 338 expanded)
%              Depth                    :   26
%              Number of atoms          : 1688 (13266 expanded)
%              Number of equality atoms :   49 ( 412 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X22 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('8',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('10',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( l1_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('11',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(demod,[status(thm)],['8','13'])).

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

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ( r1_tarski @ ( k2_struct_0 @ X17 ) @ ( k2_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('18',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(demod,[status(thm)],['8','13'])).

thf('20',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( l1_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('23',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['18','23'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('26',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) @ ( k2_struct_0 @ sk_C_1 ) )
    = ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
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

thf('28',plain,(
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

thf('29',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X10 @ X9 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X10 @ X9 ) @ X10 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X10 @ X9 ) )
        = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
      = sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(demod,[status(thm)],['8','13'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('33',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('34',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('36',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('38',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['30','31','36','37'])).

thf('39',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['30','31','36','37'])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C_1 ) )
    = sk_B ),
    inference(demod,[status(thm)],['26','38','39'])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('41',plain,(
    ! [X24: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('42',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X22 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('44',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X24: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('47',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('52',plain,(
    ! [X24: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('53',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X10 @ X9 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X10 @ X9 ) @ X10 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X10 @ X9 ) )
        = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X24: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('64',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( l1_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ) ),
    inference(clc,[status(thm)],['62','68'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('70',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('74',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k9_subset_1 @ X6 @ X4 @ X5 )
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

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

thf('76',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_pre_topc @ X31 @ X32 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X31 ) @ X34 @ ( k2_struct_0 @ X31 ) )
       != X33 )
      | ~ ( v3_pre_topc @ X34 @ X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v3_pre_topc @ X33 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t32_tops_2])).

thf('77',plain,(
    ! [X31: $i,X32: $i,X34: $i] :
      ( ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X31 ) @ X34 @ ( k2_struct_0 @ X31 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X31 ) @ X34 @ ( k2_struct_0 @ X31 ) ) @ X31 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v3_pre_topc @ X34 @ X32 )
      | ~ ( m1_pre_topc @ X31 @ X32 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( v3_pre_topc @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( l1_pre_topc @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['40','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('81',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X24: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('83',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('88',plain,(
    ! [X25: $i] :
      ( ( l1_struct_0 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('89',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86','89'])).

thf('91',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X10 @ X9 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X10 @ X9 ) @ X10 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X10 @ X9 ) )
        = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('92',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) )
      = ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) )
      = ( k2_struct_0 @ sk_C_1 ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86','89'])).

thf('96',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X22 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('97',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_A ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86','89'])).

thf('101',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('102',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['94','99','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('108',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_pre_topc @ X17 @ X18 )
      | ( r1_tarski @ ( k2_struct_0 @ X17 ) @ ( k2_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['106','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k3_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ( k3_xboole_0 @ ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) ) @ ( k2_struct_0 @ sk_C_1 ) )
      = ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) ) )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['105','116'])).

thf('118',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['94','99','104'])).

thf('119',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['94','99','104'])).

thf('120',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_A ),
    inference(demod,[status(thm)],['97','98'])).

thf('121',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_pre_topc @ X26 @ X27 )
      | ( l1_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('122',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['117','118','119','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k3_xboole_0 @ ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['126','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k3_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('134',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['132','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ( m1_subset_1 @ ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['131','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k3_xboole_0 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['125','141'])).

thf('143',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('144',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k9_subset_1 @ X6 @ X4 @ X5 )
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ X0 @ ( k2_struct_0 @ sk_C_1 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C_1 ) )
    = sk_B ),
    inference(demod,[status(thm)],['26','38','39'])).

thf('148',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ sk_B @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['79','80','146','147','148'])).

thf('150',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ( v3_pre_topc @ sk_B @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['3','149'])).

thf('151',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v3_pre_topc @ sk_B @ sk_C_1 ),
    inference(demod,[status(thm)],['150','151','152','153'])).

thf('155',plain,(
    $false ),
    inference(demod,[status(thm)],['2','154'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5WuV2yZ22P
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 10.31/10.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 10.31/10.56  % Solved by: fo/fo7.sh
% 10.31/10.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.31/10.56  % done 5930 iterations in 10.102s
% 10.31/10.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 10.31/10.56  % SZS output start Refutation
% 10.31/10.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.31/10.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 10.31/10.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 10.31/10.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 10.31/10.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 10.31/10.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 10.31/10.56  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 10.31/10.56  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 10.31/10.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 10.31/10.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 10.31/10.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.31/10.56  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 10.31/10.56  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 10.31/10.56  thf(sk_D_3_type, type, sk_D_3: $i).
% 10.31/10.56  thf(sk_A_type, type, sk_A: $i).
% 10.31/10.56  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 10.31/10.56  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 10.31/10.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.31/10.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 10.31/10.56  thf(sk_B_type, type, sk_B: $i).
% 10.31/10.56  thf(t33_tops_2, conjecture,
% 10.31/10.56    (![A:$i]:
% 10.31/10.56     ( ( l1_pre_topc @ A ) =>
% 10.31/10.56       ( ![B:$i]:
% 10.31/10.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.31/10.56           ( ![C:$i]:
% 10.31/10.56             ( ( m1_pre_topc @ C @ A ) =>
% 10.31/10.56               ( ( v3_pre_topc @ B @ A ) =>
% 10.31/10.56                 ( ![D:$i]:
% 10.31/10.56                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 10.31/10.56                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 10.31/10.56  thf(zf_stmt_0, negated_conjecture,
% 10.31/10.56    (~( ![A:$i]:
% 10.31/10.56        ( ( l1_pre_topc @ A ) =>
% 10.31/10.56          ( ![B:$i]:
% 10.31/10.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.31/10.56              ( ![C:$i]:
% 10.31/10.56                ( ( m1_pre_topc @ C @ A ) =>
% 10.31/10.56                  ( ( v3_pre_topc @ B @ A ) =>
% 10.31/10.56                    ( ![D:$i]:
% 10.31/10.56                      ( ( m1_subset_1 @
% 10.31/10.56                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 10.31/10.56                        ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 10.31/10.56    inference('cnf.neg', [status(esa)], [t33_tops_2])).
% 10.31/10.56  thf('0', plain, (~ (v3_pre_topc @ sk_D_3 @ sk_C_1)),
% 10.31/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.56  thf('1', plain, (((sk_D_3) = (sk_B))),
% 10.31/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.56  thf('2', plain, (~ (v3_pre_topc @ sk_B @ sk_C_1)),
% 10.31/10.56      inference('demod', [status(thm)], ['0', '1'])).
% 10.31/10.56  thf('3', plain,
% 10.31/10.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.31/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.56  thf('4', plain,
% 10.31/10.56      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 10.31/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.56  thf('5', plain, (((sk_D_3) = (sk_B))),
% 10.31/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.56  thf('6', plain,
% 10.31/10.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 10.31/10.56      inference('demod', [status(thm)], ['4', '5'])).
% 10.31/10.56  thf(dt_k1_pre_topc, axiom,
% 10.31/10.56    (![A:$i,B:$i]:
% 10.31/10.56     ( ( ( l1_pre_topc @ A ) & 
% 10.31/10.56         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 10.31/10.56       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 10.31/10.56         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 10.31/10.56  thf('7', plain,
% 10.31/10.56      (![X22 : $i, X23 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X22)
% 10.31/10.56          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 10.31/10.56          | (m1_pre_topc @ (k1_pre_topc @ X22 @ X23) @ X22))),
% 10.31/10.56      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 10.31/10.56  thf('8', plain,
% 10.31/10.56      (((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)
% 10.31/10.56        | ~ (l1_pre_topc @ sk_C_1))),
% 10.31/10.56      inference('sup-', [status(thm)], ['6', '7'])).
% 10.31/10.56  thf('9', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 10.31/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.56  thf(dt_m1_pre_topc, axiom,
% 10.31/10.56    (![A:$i]:
% 10.31/10.56     ( ( l1_pre_topc @ A ) =>
% 10.31/10.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 10.31/10.56  thf('10', plain,
% 10.31/10.56      (![X26 : $i, X27 : $i]:
% 10.31/10.56         (~ (m1_pre_topc @ X26 @ X27)
% 10.31/10.56          | (l1_pre_topc @ X26)
% 10.31/10.56          | ~ (l1_pre_topc @ X27))),
% 10.31/10.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 10.31/10.56  thf('11', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 10.31/10.56      inference('sup-', [status(thm)], ['9', '10'])).
% 10.31/10.56  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 10.31/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.56  thf('13', plain, ((l1_pre_topc @ sk_C_1)),
% 10.31/10.56      inference('demod', [status(thm)], ['11', '12'])).
% 10.31/10.56  thf('14', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)),
% 10.31/10.56      inference('demod', [status(thm)], ['8', '13'])).
% 10.31/10.56  thf(d9_pre_topc, axiom,
% 10.31/10.56    (![A:$i]:
% 10.31/10.56     ( ( l1_pre_topc @ A ) =>
% 10.31/10.56       ( ![B:$i]:
% 10.31/10.56         ( ( l1_pre_topc @ B ) =>
% 10.31/10.56           ( ( m1_pre_topc @ B @ A ) <=>
% 10.31/10.56             ( ( ![C:$i]:
% 10.31/10.56                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 10.31/10.56                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 10.31/10.56                     ( ?[D:$i]:
% 10.31/10.56                       ( ( m1_subset_1 @
% 10.31/10.56                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 10.31/10.56                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 10.31/10.56                         ( ( C ) =
% 10.31/10.56                           ( k9_subset_1 @
% 10.31/10.56                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 10.31/10.56               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 10.31/10.56  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 10.31/10.56  thf(zf_stmt_2, axiom,
% 10.31/10.56    (![D:$i,C:$i,B:$i,A:$i]:
% 10.31/10.56     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 10.31/10.56       ( ( ( C ) =
% 10.31/10.56           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 10.31/10.56         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 10.31/10.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 10.31/10.56  thf(zf_stmt_3, axiom,
% 10.31/10.56    (![A:$i]:
% 10.31/10.56     ( ( l1_pre_topc @ A ) =>
% 10.31/10.56       ( ![B:$i]:
% 10.31/10.56         ( ( l1_pre_topc @ B ) =>
% 10.31/10.56           ( ( m1_pre_topc @ B @ A ) <=>
% 10.31/10.56             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 10.31/10.56               ( ![C:$i]:
% 10.31/10.56                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 10.31/10.56                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 10.31/10.56                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 10.31/10.56  thf('15', plain,
% 10.31/10.56      (![X17 : $i, X18 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X17)
% 10.31/10.56          | ~ (m1_pre_topc @ X17 @ X18)
% 10.31/10.56          | (r1_tarski @ (k2_struct_0 @ X17) @ (k2_struct_0 @ X18))
% 10.31/10.56          | ~ (l1_pre_topc @ X18))),
% 10.31/10.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 10.31/10.56  thf('16', plain,
% 10.31/10.56      ((~ (l1_pre_topc @ sk_C_1)
% 10.31/10.56        | (r1_tarski @ (k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) @ 
% 10.31/10.56           (k2_struct_0 @ sk_C_1))
% 10.31/10.56        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 10.31/10.56      inference('sup-', [status(thm)], ['14', '15'])).
% 10.31/10.56  thf('17', plain, ((l1_pre_topc @ sk_C_1)),
% 10.31/10.56      inference('demod', [status(thm)], ['11', '12'])).
% 10.31/10.56  thf('18', plain,
% 10.31/10.56      (((r1_tarski @ (k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) @ 
% 10.31/10.56         (k2_struct_0 @ sk_C_1))
% 10.31/10.56        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 10.31/10.56      inference('demod', [status(thm)], ['16', '17'])).
% 10.31/10.56  thf('19', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)),
% 10.31/10.56      inference('demod', [status(thm)], ['8', '13'])).
% 10.31/10.56  thf('20', plain,
% 10.31/10.56      (![X26 : $i, X27 : $i]:
% 10.31/10.56         (~ (m1_pre_topc @ X26 @ X27)
% 10.31/10.56          | (l1_pre_topc @ X26)
% 10.31/10.56          | ~ (l1_pre_topc @ X27))),
% 10.31/10.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 10.31/10.56  thf('21', plain,
% 10.31/10.56      ((~ (l1_pre_topc @ sk_C_1)
% 10.31/10.56        | (l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 10.31/10.56      inference('sup-', [status(thm)], ['19', '20'])).
% 10.31/10.56  thf('22', plain, ((l1_pre_topc @ sk_C_1)),
% 10.31/10.56      inference('demod', [status(thm)], ['11', '12'])).
% 10.31/10.56  thf('23', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))),
% 10.31/10.56      inference('demod', [status(thm)], ['21', '22'])).
% 10.31/10.56  thf('24', plain,
% 10.31/10.56      ((r1_tarski @ (k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) @ 
% 10.31/10.56        (k2_struct_0 @ sk_C_1))),
% 10.31/10.56      inference('demod', [status(thm)], ['18', '23'])).
% 10.31/10.56  thf(t28_xboole_1, axiom,
% 10.31/10.56    (![A:$i,B:$i]:
% 10.31/10.56     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 10.31/10.56  thf('25', plain,
% 10.31/10.56      (![X0 : $i, X1 : $i]:
% 10.31/10.56         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 10.31/10.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 10.31/10.56  thf('26', plain,
% 10.31/10.56      (((k3_xboole_0 @ (k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) @ 
% 10.31/10.56         (k2_struct_0 @ sk_C_1))
% 10.31/10.56         = (k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 10.31/10.56      inference('sup-', [status(thm)], ['24', '25'])).
% 10.31/10.56  thf('27', plain,
% 10.31/10.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 10.31/10.56      inference('demod', [status(thm)], ['4', '5'])).
% 10.31/10.56  thf(d10_pre_topc, axiom,
% 10.31/10.56    (![A:$i]:
% 10.31/10.56     ( ( l1_pre_topc @ A ) =>
% 10.31/10.56       ( ![B:$i]:
% 10.31/10.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.31/10.56           ( ![C:$i]:
% 10.31/10.56             ( ( ( v1_pre_topc @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 10.31/10.56               ( ( ( C ) = ( k1_pre_topc @ A @ B ) ) <=>
% 10.31/10.56                 ( ( k2_struct_0 @ C ) = ( B ) ) ) ) ) ) ) ))).
% 10.31/10.56  thf('28', plain,
% 10.31/10.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 10.31/10.56         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 10.31/10.56          | ((X11) != (k1_pre_topc @ X10 @ X9))
% 10.31/10.56          | ((k2_struct_0 @ X11) = (X9))
% 10.31/10.56          | ~ (m1_pre_topc @ X11 @ X10)
% 10.31/10.56          | ~ (v1_pre_topc @ X11)
% 10.31/10.56          | ~ (l1_pre_topc @ X10))),
% 10.31/10.56      inference('cnf', [status(esa)], [d10_pre_topc])).
% 10.31/10.56  thf('29', plain,
% 10.31/10.56      (![X9 : $i, X10 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X10)
% 10.31/10.56          | ~ (v1_pre_topc @ (k1_pre_topc @ X10 @ X9))
% 10.31/10.56          | ~ (m1_pre_topc @ (k1_pre_topc @ X10 @ X9) @ X10)
% 10.31/10.56          | ((k2_struct_0 @ (k1_pre_topc @ X10 @ X9)) = (X9))
% 10.31/10.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 10.31/10.56      inference('simplify', [status(thm)], ['28'])).
% 10.31/10.56  thf('30', plain,
% 10.31/10.56      ((((k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) = (sk_B))
% 10.31/10.56        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)
% 10.31/10.56        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))
% 10.31/10.56        | ~ (l1_pre_topc @ sk_C_1))),
% 10.31/10.56      inference('sup-', [status(thm)], ['27', '29'])).
% 10.31/10.56  thf('31', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)),
% 10.31/10.56      inference('demod', [status(thm)], ['8', '13'])).
% 10.31/10.56  thf('32', plain,
% 10.31/10.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 10.31/10.56      inference('demod', [status(thm)], ['4', '5'])).
% 10.31/10.56  thf('33', plain,
% 10.31/10.56      (![X22 : $i, X23 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X22)
% 10.31/10.56          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 10.31/10.56          | (v1_pre_topc @ (k1_pre_topc @ X22 @ X23)))),
% 10.31/10.56      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 10.31/10.56  thf('34', plain,
% 10.31/10.56      (((v1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))
% 10.31/10.56        | ~ (l1_pre_topc @ sk_C_1))),
% 10.31/10.56      inference('sup-', [status(thm)], ['32', '33'])).
% 10.31/10.56  thf('35', plain, ((l1_pre_topc @ sk_C_1)),
% 10.31/10.56      inference('demod', [status(thm)], ['11', '12'])).
% 10.31/10.56  thf('36', plain, ((v1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))),
% 10.31/10.56      inference('demod', [status(thm)], ['34', '35'])).
% 10.31/10.56  thf('37', plain, ((l1_pre_topc @ sk_C_1)),
% 10.31/10.56      inference('demod', [status(thm)], ['11', '12'])).
% 10.31/10.56  thf('38', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) = (sk_B))),
% 10.31/10.56      inference('demod', [status(thm)], ['30', '31', '36', '37'])).
% 10.31/10.56  thf('39', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) = (sk_B))),
% 10.31/10.56      inference('demod', [status(thm)], ['30', '31', '36', '37'])).
% 10.31/10.56  thf('40', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C_1)) = (sk_B))),
% 10.31/10.56      inference('demod', [status(thm)], ['26', '38', '39'])).
% 10.31/10.56  thf(dt_k2_struct_0, axiom,
% 10.31/10.56    (![A:$i]:
% 10.31/10.56     ( ( l1_struct_0 @ A ) =>
% 10.31/10.56       ( m1_subset_1 @
% 10.31/10.56         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 10.31/10.56  thf('41', plain,
% 10.31/10.56      (![X24 : $i]:
% 10.31/10.56         ((m1_subset_1 @ (k2_struct_0 @ X24) @ 
% 10.31/10.56           (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 10.31/10.56          | ~ (l1_struct_0 @ X24))),
% 10.31/10.56      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 10.31/10.56  thf('42', plain,
% 10.31/10.56      (![X22 : $i, X23 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X22)
% 10.31/10.56          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 10.31/10.56          | (m1_pre_topc @ (k1_pre_topc @ X22 @ X23) @ X22))),
% 10.31/10.56      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 10.31/10.56  thf('43', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_struct_0 @ X0)
% 10.31/10.56          | (m1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ X0)
% 10.31/10.56          | ~ (l1_pre_topc @ X0))),
% 10.31/10.56      inference('sup-', [status(thm)], ['41', '42'])).
% 10.31/10.56  thf(dt_l1_pre_topc, axiom,
% 10.31/10.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 10.31/10.56  thf('44', plain,
% 10.31/10.56      (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 10.31/10.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 10.31/10.56  thf('45', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | (m1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ X0))),
% 10.31/10.56      inference('clc', [status(thm)], ['43', '44'])).
% 10.31/10.56  thf('46', plain,
% 10.31/10.56      (![X24 : $i]:
% 10.31/10.56         ((m1_subset_1 @ (k2_struct_0 @ X24) @ 
% 10.31/10.56           (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 10.31/10.56          | ~ (l1_struct_0 @ X24))),
% 10.31/10.56      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 10.31/10.56  thf('47', plain,
% 10.31/10.56      (![X22 : $i, X23 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X22)
% 10.31/10.56          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 10.31/10.56          | (v1_pre_topc @ (k1_pre_topc @ X22 @ X23)))),
% 10.31/10.56      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 10.31/10.56  thf('48', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_struct_0 @ X0)
% 10.31/10.56          | (v1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 10.31/10.56          | ~ (l1_pre_topc @ X0))),
% 10.31/10.56      inference('sup-', [status(thm)], ['46', '47'])).
% 10.31/10.56  thf('49', plain,
% 10.31/10.56      (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 10.31/10.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 10.31/10.56  thf('50', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | (v1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))))),
% 10.31/10.56      inference('clc', [status(thm)], ['48', '49'])).
% 10.31/10.56  thf('51', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | (m1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ X0))),
% 10.31/10.56      inference('clc', [status(thm)], ['43', '44'])).
% 10.31/10.56  thf('52', plain,
% 10.31/10.56      (![X24 : $i]:
% 10.31/10.56         ((m1_subset_1 @ (k2_struct_0 @ X24) @ 
% 10.31/10.56           (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 10.31/10.56          | ~ (l1_struct_0 @ X24))),
% 10.31/10.56      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 10.31/10.56  thf('53', plain,
% 10.31/10.56      (![X9 : $i, X10 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X10)
% 10.31/10.56          | ~ (v1_pre_topc @ (k1_pre_topc @ X10 @ X9))
% 10.31/10.56          | ~ (m1_pre_topc @ (k1_pre_topc @ X10 @ X9) @ X10)
% 10.31/10.56          | ((k2_struct_0 @ (k1_pre_topc @ X10 @ X9)) = (X9))
% 10.31/10.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 10.31/10.56      inference('simplify', [status(thm)], ['28'])).
% 10.31/10.56  thf('54', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_struct_0 @ X0)
% 10.31/10.56          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 10.31/10.56              = (k2_struct_0 @ X0))
% 10.31/10.56          | ~ (m1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ X0)
% 10.31/10.56          | ~ (v1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 10.31/10.56          | ~ (l1_pre_topc @ X0))),
% 10.31/10.56      inference('sup-', [status(thm)], ['52', '53'])).
% 10.31/10.56  thf('55', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | ~ (l1_pre_topc @ X0)
% 10.31/10.56          | ~ (v1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 10.31/10.56          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 10.31/10.56              = (k2_struct_0 @ X0))
% 10.31/10.56          | ~ (l1_struct_0 @ X0))),
% 10.31/10.56      inference('sup-', [status(thm)], ['51', '54'])).
% 10.31/10.56  thf('56', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_struct_0 @ X0)
% 10.31/10.56          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 10.31/10.56              = (k2_struct_0 @ X0))
% 10.31/10.56          | ~ (v1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 10.31/10.56          | ~ (l1_pre_topc @ X0))),
% 10.31/10.56      inference('simplify', [status(thm)], ['55'])).
% 10.31/10.56  thf('57', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | ~ (l1_pre_topc @ X0)
% 10.31/10.56          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 10.31/10.56              = (k2_struct_0 @ X0))
% 10.31/10.56          | ~ (l1_struct_0 @ X0))),
% 10.31/10.56      inference('sup-', [status(thm)], ['50', '56'])).
% 10.31/10.56  thf('58', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_struct_0 @ X0)
% 10.31/10.56          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 10.31/10.56              = (k2_struct_0 @ X0))
% 10.31/10.56          | ~ (l1_pre_topc @ X0))),
% 10.31/10.56      inference('simplify', [status(thm)], ['57'])).
% 10.31/10.56  thf('59', plain,
% 10.31/10.56      (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 10.31/10.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 10.31/10.56  thf('60', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 10.31/10.56              = (k2_struct_0 @ X0)))),
% 10.31/10.56      inference('clc', [status(thm)], ['58', '59'])).
% 10.31/10.56  thf('61', plain,
% 10.31/10.56      (![X24 : $i]:
% 10.31/10.56         ((m1_subset_1 @ (k2_struct_0 @ X24) @ 
% 10.31/10.56           (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 10.31/10.56          | ~ (l1_struct_0 @ X24))),
% 10.31/10.56      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 10.31/10.56  thf('62', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         ((m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 10.31/10.56           (k1_zfmisc_1 @ 
% 10.31/10.56            (u1_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))))
% 10.31/10.56          | ~ (l1_pre_topc @ X0)
% 10.31/10.56          | ~ (l1_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))))),
% 10.31/10.56      inference('sup+', [status(thm)], ['60', '61'])).
% 10.31/10.56  thf('63', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | (m1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ X0))),
% 10.31/10.56      inference('clc', [status(thm)], ['43', '44'])).
% 10.31/10.56  thf('64', plain,
% 10.31/10.56      (![X26 : $i, X27 : $i]:
% 10.31/10.56         (~ (m1_pre_topc @ X26 @ X27)
% 10.31/10.56          | (l1_pre_topc @ X26)
% 10.31/10.56          | ~ (l1_pre_topc @ X27))),
% 10.31/10.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 10.31/10.56  thf('65', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | ~ (l1_pre_topc @ X0)
% 10.31/10.56          | (l1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))))),
% 10.31/10.56      inference('sup-', [status(thm)], ['63', '64'])).
% 10.31/10.56  thf('66', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         ((l1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 10.31/10.56          | ~ (l1_pre_topc @ X0))),
% 10.31/10.56      inference('simplify', [status(thm)], ['65'])).
% 10.31/10.56  thf('67', plain,
% 10.31/10.56      (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 10.31/10.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 10.31/10.56  thf('68', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | (l1_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))))),
% 10.31/10.56      inference('sup-', [status(thm)], ['66', '67'])).
% 10.31/10.56  thf('69', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 10.31/10.56             (k1_zfmisc_1 @ 
% 10.31/10.56              (u1_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))))))),
% 10.31/10.56      inference('clc', [status(thm)], ['62', '68'])).
% 10.31/10.56  thf(t39_pre_topc, axiom,
% 10.31/10.56    (![A:$i]:
% 10.31/10.56     ( ( l1_pre_topc @ A ) =>
% 10.31/10.56       ( ![B:$i]:
% 10.31/10.56         ( ( m1_pre_topc @ B @ A ) =>
% 10.31/10.56           ( ![C:$i]:
% 10.31/10.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 10.31/10.56               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 10.31/10.56  thf('70', plain,
% 10.31/10.56      (![X28 : $i, X29 : $i, X30 : $i]:
% 10.31/10.56         (~ (m1_pre_topc @ X28 @ X29)
% 10.31/10.56          | (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 10.31/10.56          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 10.31/10.56          | ~ (l1_pre_topc @ X29))),
% 10.31/10.56      inference('cnf', [status(esa)], [t39_pre_topc])).
% 10.31/10.56  thf('71', plain,
% 10.31/10.56      (![X0 : $i, X1 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | ~ (l1_pre_topc @ X1)
% 10.31/10.56          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 10.31/10.56             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 10.31/10.56          | ~ (m1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ X1))),
% 10.31/10.56      inference('sup-', [status(thm)], ['69', '70'])).
% 10.31/10.56  thf('72', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 10.31/10.56             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 10.31/10.56          | ~ (l1_pre_topc @ X0)
% 10.31/10.56          | ~ (l1_pre_topc @ X0))),
% 10.31/10.56      inference('sup-', [status(thm)], ['45', '71'])).
% 10.31/10.56  thf('73', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         ((m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 10.31/10.56           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 10.31/10.56          | ~ (l1_pre_topc @ X0))),
% 10.31/10.56      inference('simplify', [status(thm)], ['72'])).
% 10.31/10.56  thf(redefinition_k9_subset_1, axiom,
% 10.31/10.56    (![A:$i,B:$i,C:$i]:
% 10.31/10.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 10.31/10.56       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 10.31/10.56  thf('74', plain,
% 10.31/10.56      (![X4 : $i, X5 : $i, X6 : $i]:
% 10.31/10.56         (((k9_subset_1 @ X6 @ X4 @ X5) = (k3_xboole_0 @ X4 @ X5))
% 10.31/10.56          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 10.31/10.56      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 10.31/10.56  thf('75', plain,
% 10.31/10.56      (![X0 : $i, X1 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0))
% 10.31/10.56              = (k3_xboole_0 @ X1 @ (k2_struct_0 @ X0))))),
% 10.31/10.56      inference('sup-', [status(thm)], ['73', '74'])).
% 10.31/10.56  thf(t32_tops_2, axiom,
% 10.31/10.56    (![A:$i]:
% 10.31/10.56     ( ( l1_pre_topc @ A ) =>
% 10.31/10.56       ( ![B:$i]:
% 10.31/10.56         ( ( m1_pre_topc @ B @ A ) =>
% 10.31/10.56           ( ![C:$i]:
% 10.31/10.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 10.31/10.56               ( ( v3_pre_topc @ C @ B ) <=>
% 10.31/10.56                 ( ?[D:$i]:
% 10.31/10.56                   ( ( ( k9_subset_1 @
% 10.31/10.56                         ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) =
% 10.31/10.56                       ( C ) ) & 
% 10.31/10.56                     ( v3_pre_topc @ D @ A ) & 
% 10.31/10.56                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 10.31/10.56  thf('76', plain,
% 10.31/10.56      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 10.31/10.56         (~ (m1_pre_topc @ X31 @ X32)
% 10.31/10.56          | ((k9_subset_1 @ (u1_struct_0 @ X31) @ X34 @ (k2_struct_0 @ X31))
% 10.31/10.56              != (X33))
% 10.31/10.56          | ~ (v3_pre_topc @ X34 @ X32)
% 10.31/10.56          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 10.31/10.56          | (v3_pre_topc @ X33 @ X31)
% 10.31/10.56          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 10.31/10.56          | ~ (l1_pre_topc @ X32))),
% 10.31/10.56      inference('cnf', [status(esa)], [t32_tops_2])).
% 10.31/10.56  thf('77', plain,
% 10.31/10.56      (![X31 : $i, X32 : $i, X34 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X32)
% 10.31/10.56          | ~ (m1_subset_1 @ 
% 10.31/10.56               (k9_subset_1 @ (u1_struct_0 @ X31) @ X34 @ (k2_struct_0 @ X31)) @ 
% 10.31/10.56               (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 10.31/10.56          | (v3_pre_topc @ 
% 10.31/10.56             (k9_subset_1 @ (u1_struct_0 @ X31) @ X34 @ (k2_struct_0 @ X31)) @ 
% 10.31/10.56             X31)
% 10.31/10.56          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 10.31/10.56          | ~ (v3_pre_topc @ X34 @ X32)
% 10.31/10.56          | ~ (m1_pre_topc @ X31 @ X32))),
% 10.31/10.56      inference('simplify', [status(thm)], ['76'])).
% 10.31/10.56  thf('78', plain,
% 10.31/10.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.31/10.56         (~ (m1_subset_1 @ (k3_xboole_0 @ X1 @ (k2_struct_0 @ X0)) @ 
% 10.31/10.56             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 10.31/10.56          | ~ (l1_pre_topc @ X0)
% 10.31/10.56          | ~ (m1_pre_topc @ X0 @ X2)
% 10.31/10.56          | ~ (v3_pre_topc @ X1 @ X2)
% 10.31/10.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 10.31/10.56          | (v3_pre_topc @ 
% 10.31/10.56             (k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ X0)
% 10.31/10.56          | ~ (l1_pre_topc @ X2))),
% 10.31/10.56      inference('sup-', [status(thm)], ['75', '77'])).
% 10.31/10.56  thf('79', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 10.31/10.56          | ~ (l1_pre_topc @ X0)
% 10.31/10.56          | (v3_pre_topc @ 
% 10.31/10.56             (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ 
% 10.31/10.56              (k2_struct_0 @ sk_C_1)) @ 
% 10.31/10.56             sk_C_1)
% 10.31/10.56          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 10.31/10.56          | ~ (v3_pre_topc @ sk_B @ X0)
% 10.31/10.56          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 10.31/10.56          | ~ (l1_pre_topc @ sk_C_1))),
% 10.31/10.56      inference('sup-', [status(thm)], ['40', '78'])).
% 10.31/10.56  thf('80', plain,
% 10.31/10.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 10.31/10.56      inference('demod', [status(thm)], ['4', '5'])).
% 10.31/10.56  thf('81', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 10.31/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.56  thf('82', plain,
% 10.31/10.56      (![X24 : $i]:
% 10.31/10.56         ((m1_subset_1 @ (k2_struct_0 @ X24) @ 
% 10.31/10.56           (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 10.31/10.56          | ~ (l1_struct_0 @ X24))),
% 10.31/10.56      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 10.31/10.56  thf('83', plain,
% 10.31/10.56      (![X28 : $i, X29 : $i, X30 : $i]:
% 10.31/10.56         (~ (m1_pre_topc @ X28 @ X29)
% 10.31/10.56          | (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 10.31/10.56          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 10.31/10.56          | ~ (l1_pre_topc @ X29))),
% 10.31/10.56      inference('cnf', [status(esa)], [t39_pre_topc])).
% 10.31/10.56  thf('84', plain,
% 10.31/10.56      (![X0 : $i, X1 : $i]:
% 10.31/10.56         (~ (l1_struct_0 @ X0)
% 10.31/10.56          | ~ (l1_pre_topc @ X1)
% 10.31/10.56          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 10.31/10.56             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 10.31/10.56          | ~ (m1_pre_topc @ X0 @ X1))),
% 10.31/10.56      inference('sup-', [status(thm)], ['82', '83'])).
% 10.31/10.56  thf('85', plain,
% 10.31/10.56      (((m1_subset_1 @ (k2_struct_0 @ sk_C_1) @ 
% 10.31/10.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 10.31/10.56        | ~ (l1_pre_topc @ sk_A)
% 10.31/10.56        | ~ (l1_struct_0 @ sk_C_1))),
% 10.31/10.56      inference('sup-', [status(thm)], ['81', '84'])).
% 10.31/10.56  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 10.31/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.56  thf('87', plain, ((l1_pre_topc @ sk_C_1)),
% 10.31/10.56      inference('demod', [status(thm)], ['11', '12'])).
% 10.31/10.56  thf('88', plain,
% 10.31/10.56      (![X25 : $i]: ((l1_struct_0 @ X25) | ~ (l1_pre_topc @ X25))),
% 10.31/10.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 10.31/10.56  thf('89', plain, ((l1_struct_0 @ sk_C_1)),
% 10.31/10.56      inference('sup-', [status(thm)], ['87', '88'])).
% 10.31/10.56  thf('90', plain,
% 10.31/10.56      ((m1_subset_1 @ (k2_struct_0 @ sk_C_1) @ 
% 10.31/10.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.31/10.56      inference('demod', [status(thm)], ['85', '86', '89'])).
% 10.31/10.56  thf('91', plain,
% 10.31/10.56      (![X9 : $i, X10 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X10)
% 10.31/10.56          | ~ (v1_pre_topc @ (k1_pre_topc @ X10 @ X9))
% 10.31/10.56          | ~ (m1_pre_topc @ (k1_pre_topc @ X10 @ X9) @ X10)
% 10.31/10.56          | ((k2_struct_0 @ (k1_pre_topc @ X10 @ X9)) = (X9))
% 10.31/10.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 10.31/10.56      inference('simplify', [status(thm)], ['28'])).
% 10.31/10.56  thf('92', plain,
% 10.31/10.56      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))
% 10.31/10.56          = (k2_struct_0 @ sk_C_1))
% 10.31/10.56        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)) @ sk_A)
% 10.31/10.56        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))
% 10.31/10.56        | ~ (l1_pre_topc @ sk_A))),
% 10.31/10.56      inference('sup-', [status(thm)], ['90', '91'])).
% 10.31/10.56  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 10.31/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.56  thf('94', plain,
% 10.31/10.56      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))
% 10.31/10.56          = (k2_struct_0 @ sk_C_1))
% 10.31/10.56        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)) @ sk_A)
% 10.31/10.56        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1))))),
% 10.31/10.56      inference('demod', [status(thm)], ['92', '93'])).
% 10.31/10.56  thf('95', plain,
% 10.31/10.56      ((m1_subset_1 @ (k2_struct_0 @ sk_C_1) @ 
% 10.31/10.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.31/10.56      inference('demod', [status(thm)], ['85', '86', '89'])).
% 10.31/10.56  thf('96', plain,
% 10.31/10.56      (![X22 : $i, X23 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X22)
% 10.31/10.56          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 10.31/10.56          | (m1_pre_topc @ (k1_pre_topc @ X22 @ X23) @ X22))),
% 10.31/10.56      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 10.31/10.56  thf('97', plain,
% 10.31/10.56      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)) @ sk_A)
% 10.31/10.56        | ~ (l1_pre_topc @ sk_A))),
% 10.31/10.56      inference('sup-', [status(thm)], ['95', '96'])).
% 10.31/10.56  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 10.31/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.56  thf('99', plain,
% 10.31/10.56      ((m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)) @ sk_A)),
% 10.31/10.56      inference('demod', [status(thm)], ['97', '98'])).
% 10.31/10.56  thf('100', plain,
% 10.31/10.56      ((m1_subset_1 @ (k2_struct_0 @ sk_C_1) @ 
% 10.31/10.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 10.31/10.56      inference('demod', [status(thm)], ['85', '86', '89'])).
% 10.31/10.56  thf('101', plain,
% 10.31/10.56      (![X22 : $i, X23 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X22)
% 10.31/10.56          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 10.31/10.56          | (v1_pre_topc @ (k1_pre_topc @ X22 @ X23)))),
% 10.31/10.56      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 10.31/10.56  thf('102', plain,
% 10.31/10.56      (((v1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))
% 10.31/10.56        | ~ (l1_pre_topc @ sk_A))),
% 10.31/10.56      inference('sup-', [status(thm)], ['100', '101'])).
% 10.31/10.56  thf('103', plain, ((l1_pre_topc @ sk_A)),
% 10.31/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.56  thf('104', plain,
% 10.31/10.56      ((v1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))),
% 10.31/10.56      inference('demod', [status(thm)], ['102', '103'])).
% 10.31/10.56  thf('105', plain,
% 10.31/10.56      (((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))
% 10.31/10.56         = (k2_struct_0 @ sk_C_1))),
% 10.31/10.56      inference('demod', [status(thm)], ['94', '99', '104'])).
% 10.31/10.56  thf('106', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 10.31/10.56              = (k2_struct_0 @ X0)))),
% 10.31/10.56      inference('clc', [status(thm)], ['58', '59'])).
% 10.31/10.56  thf('107', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | (m1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ X0))),
% 10.31/10.56      inference('clc', [status(thm)], ['43', '44'])).
% 10.31/10.56  thf('108', plain,
% 10.31/10.56      (![X17 : $i, X18 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X17)
% 10.31/10.56          | ~ (m1_pre_topc @ X17 @ X18)
% 10.31/10.56          | (r1_tarski @ (k2_struct_0 @ X17) @ (k2_struct_0 @ X18))
% 10.31/10.56          | ~ (l1_pre_topc @ X18))),
% 10.31/10.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 10.31/10.56  thf('109', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | ~ (l1_pre_topc @ X0)
% 10.31/10.56          | (r1_tarski @ 
% 10.31/10.56             (k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))) @ 
% 10.31/10.56             (k2_struct_0 @ X0))
% 10.31/10.56          | ~ (l1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))))),
% 10.31/10.56      inference('sup-', [status(thm)], ['107', '108'])).
% 10.31/10.56  thf('110', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 10.31/10.56          | (r1_tarski @ 
% 10.31/10.56             (k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))) @ 
% 10.31/10.56             (k2_struct_0 @ X0))
% 10.31/10.56          | ~ (l1_pre_topc @ X0))),
% 10.31/10.56      inference('simplify', [status(thm)], ['109'])).
% 10.31/10.56  thf('111', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         ((l1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 10.31/10.56          | ~ (l1_pre_topc @ X0))),
% 10.31/10.56      inference('simplify', [status(thm)], ['65'])).
% 10.31/10.56  thf('112', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | (r1_tarski @ 
% 10.31/10.56             (k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))) @ 
% 10.31/10.56             (k2_struct_0 @ X0)))),
% 10.31/10.56      inference('clc', [status(thm)], ['110', '111'])).
% 10.31/10.56  thf('113', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         ((r1_tarski @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 10.31/10.56          | ~ (l1_pre_topc @ X0)
% 10.31/10.56          | ~ (l1_pre_topc @ X0))),
% 10.31/10.56      inference('sup+', [status(thm)], ['106', '112'])).
% 10.31/10.56  thf('114', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | (r1_tarski @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0)))),
% 10.31/10.56      inference('simplify', [status(thm)], ['113'])).
% 10.31/10.56  thf('115', plain,
% 10.31/10.56      (![X0 : $i, X1 : $i]:
% 10.31/10.56         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 10.31/10.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 10.31/10.56  thf('116', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | ((k3_xboole_0 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 10.31/10.56              = (k2_struct_0 @ X0)))),
% 10.31/10.56      inference('sup-', [status(thm)], ['114', '115'])).
% 10.31/10.56  thf('117', plain,
% 10.31/10.56      ((((k3_xboole_0 @ 
% 10.31/10.56          (k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1))) @ 
% 10.31/10.56          (k2_struct_0 @ sk_C_1))
% 10.31/10.56          = (k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1))))
% 10.31/10.56        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1))))),
% 10.31/10.56      inference('sup+', [status(thm)], ['105', '116'])).
% 10.31/10.56  thf('118', plain,
% 10.31/10.56      (((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))
% 10.31/10.56         = (k2_struct_0 @ sk_C_1))),
% 10.31/10.56      inference('demod', [status(thm)], ['94', '99', '104'])).
% 10.31/10.56  thf('119', plain,
% 10.31/10.56      (((k2_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))
% 10.31/10.56         = (k2_struct_0 @ sk_C_1))),
% 10.31/10.56      inference('demod', [status(thm)], ['94', '99', '104'])).
% 10.31/10.56  thf('120', plain,
% 10.31/10.56      ((m1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)) @ sk_A)),
% 10.31/10.56      inference('demod', [status(thm)], ['97', '98'])).
% 10.31/10.56  thf('121', plain,
% 10.31/10.56      (![X26 : $i, X27 : $i]:
% 10.31/10.56         (~ (m1_pre_topc @ X26 @ X27)
% 10.31/10.56          | (l1_pre_topc @ X26)
% 10.31/10.56          | ~ (l1_pre_topc @ X27))),
% 10.31/10.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 10.31/10.56  thf('122', plain,
% 10.31/10.56      ((~ (l1_pre_topc @ sk_A)
% 10.31/10.56        | (l1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1))))),
% 10.31/10.56      inference('sup-', [status(thm)], ['120', '121'])).
% 10.31/10.56  thf('123', plain, ((l1_pre_topc @ sk_A)),
% 10.31/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.56  thf('124', plain,
% 10.31/10.56      ((l1_pre_topc @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))),
% 10.31/10.56      inference('demod', [status(thm)], ['122', '123'])).
% 10.31/10.56  thf('125', plain,
% 10.31/10.56      (((k3_xboole_0 @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_C_1))
% 10.31/10.56         = (k2_struct_0 @ sk_C_1))),
% 10.31/10.56      inference('demod', [status(thm)], ['117', '118', '119', '124'])).
% 10.31/10.56  thf('126', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | ((k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 10.31/10.56              = (k2_struct_0 @ X0)))),
% 10.31/10.56      inference('clc', [status(thm)], ['58', '59'])).
% 10.31/10.56  thf('127', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | (r1_tarski @ 
% 10.31/10.56             (k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))) @ 
% 10.31/10.56             (k2_struct_0 @ X0)))),
% 10.31/10.56      inference('clc', [status(thm)], ['110', '111'])).
% 10.31/10.56  thf('128', plain,
% 10.31/10.56      (![X0 : $i, X1 : $i]:
% 10.31/10.56         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 10.31/10.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 10.31/10.56  thf('129', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | ((k3_xboole_0 @ 
% 10.31/10.56              (k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))) @ 
% 10.31/10.56              (k2_struct_0 @ X0))
% 10.31/10.56              = (k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))))),
% 10.31/10.56      inference('sup-', [status(thm)], ['127', '128'])).
% 10.31/10.56  thf('130', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (((k3_xboole_0 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 10.31/10.56            = (k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))))
% 10.31/10.56          | ~ (l1_pre_topc @ X0)
% 10.31/10.56          | ~ (l1_pre_topc @ X0))),
% 10.31/10.56      inference('sup+', [status(thm)], ['126', '129'])).
% 10.31/10.56  thf('131', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | ((k3_xboole_0 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 10.31/10.56              = (k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))))),
% 10.31/10.56      inference('simplify', [status(thm)], ['130'])).
% 10.31/10.56  thf('132', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | (m1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ X0))),
% 10.31/10.56      inference('clc', [status(thm)], ['43', '44'])).
% 10.31/10.56  thf('133', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         ((m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 10.31/10.56           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 10.31/10.56          | ~ (l1_pre_topc @ X0))),
% 10.31/10.56      inference('simplify', [status(thm)], ['72'])).
% 10.31/10.56  thf('134', plain,
% 10.31/10.56      (![X28 : $i, X29 : $i, X30 : $i]:
% 10.31/10.56         (~ (m1_pre_topc @ X28 @ X29)
% 10.31/10.56          | (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 10.31/10.56          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 10.31/10.56          | ~ (l1_pre_topc @ X29))),
% 10.31/10.56      inference('cnf', [status(esa)], [t39_pre_topc])).
% 10.31/10.56  thf('135', plain,
% 10.31/10.56      (![X0 : $i, X1 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | ~ (l1_pre_topc @ X1)
% 10.31/10.56          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 10.31/10.56             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 10.31/10.56          | ~ (m1_pre_topc @ X0 @ X1))),
% 10.31/10.56      inference('sup-', [status(thm)], ['133', '134'])).
% 10.31/10.56  thf('136', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | (m1_subset_1 @ 
% 10.31/10.56             (k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))) @ 
% 10.31/10.56             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 10.31/10.56          | ~ (l1_pre_topc @ X0)
% 10.31/10.56          | ~ (l1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))))),
% 10.31/10.56      inference('sup-', [status(thm)], ['132', '135'])).
% 10.31/10.56  thf('137', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 10.31/10.56          | (m1_subset_1 @ 
% 10.31/10.56             (k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))) @ 
% 10.31/10.56             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 10.31/10.56          | ~ (l1_pre_topc @ X0))),
% 10.31/10.56      inference('simplify', [status(thm)], ['136'])).
% 10.31/10.56  thf('138', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         ((l1_pre_topc @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 10.31/10.56          | ~ (l1_pre_topc @ X0))),
% 10.31/10.56      inference('simplify', [status(thm)], ['65'])).
% 10.31/10.56  thf('139', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | (m1_subset_1 @ 
% 10.31/10.56             (k2_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0))) @ 
% 10.31/10.56             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 10.31/10.56      inference('clc', [status(thm)], ['137', '138'])).
% 10.31/10.56  thf('140', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         ((m1_subset_1 @ 
% 10.31/10.56           (k3_xboole_0 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0)) @ 
% 10.31/10.56           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 10.31/10.56          | ~ (l1_pre_topc @ X0)
% 10.31/10.56          | ~ (l1_pre_topc @ X0))),
% 10.31/10.56      inference('sup+', [status(thm)], ['131', '139'])).
% 10.31/10.56  thf('141', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | (m1_subset_1 @ 
% 10.31/10.56             (k3_xboole_0 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0)) @ 
% 10.31/10.56             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 10.31/10.56      inference('simplify', [status(thm)], ['140'])).
% 10.31/10.56  thf('142', plain,
% 10.31/10.56      (((m1_subset_1 @ (k2_struct_0 @ sk_C_1) @ 
% 10.31/10.56         (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 10.31/10.56        | ~ (l1_pre_topc @ sk_C_1))),
% 10.31/10.56      inference('sup+', [status(thm)], ['125', '141'])).
% 10.31/10.56  thf('143', plain, ((l1_pre_topc @ sk_C_1)),
% 10.31/10.56      inference('demod', [status(thm)], ['11', '12'])).
% 10.31/10.56  thf('144', plain,
% 10.31/10.56      ((m1_subset_1 @ (k2_struct_0 @ sk_C_1) @ 
% 10.31/10.56        (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 10.31/10.56      inference('demod', [status(thm)], ['142', '143'])).
% 10.31/10.56  thf('145', plain,
% 10.31/10.56      (![X4 : $i, X5 : $i, X6 : $i]:
% 10.31/10.56         (((k9_subset_1 @ X6 @ X4 @ X5) = (k3_xboole_0 @ X4 @ X5))
% 10.31/10.56          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 10.31/10.56      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 10.31/10.56  thf('146', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         ((k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ X0 @ (k2_struct_0 @ sk_C_1))
% 10.31/10.56           = (k3_xboole_0 @ X0 @ (k2_struct_0 @ sk_C_1)))),
% 10.31/10.56      inference('sup-', [status(thm)], ['144', '145'])).
% 10.31/10.56  thf('147', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C_1)) = (sk_B))),
% 10.31/10.56      inference('demod', [status(thm)], ['26', '38', '39'])).
% 10.31/10.56  thf('148', plain, ((l1_pre_topc @ sk_C_1)),
% 10.31/10.56      inference('demod', [status(thm)], ['11', '12'])).
% 10.31/10.56  thf('149', plain,
% 10.31/10.56      (![X0 : $i]:
% 10.31/10.56         (~ (l1_pre_topc @ X0)
% 10.31/10.56          | (v3_pre_topc @ sk_B @ sk_C_1)
% 10.31/10.56          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 10.31/10.56          | ~ (v3_pre_topc @ sk_B @ X0)
% 10.31/10.56          | ~ (m1_pre_topc @ sk_C_1 @ X0))),
% 10.31/10.56      inference('demod', [status(thm)], ['79', '80', '146', '147', '148'])).
% 10.31/10.56  thf('150', plain,
% 10.31/10.56      ((~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 10.31/10.56        | ~ (v3_pre_topc @ sk_B @ sk_A)
% 10.31/10.56        | (v3_pre_topc @ sk_B @ sk_C_1)
% 10.31/10.56        | ~ (l1_pre_topc @ sk_A))),
% 10.31/10.56      inference('sup-', [status(thm)], ['3', '149'])).
% 10.31/10.56  thf('151', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 10.31/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.56  thf('152', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 10.31/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.56  thf('153', plain, ((l1_pre_topc @ sk_A)),
% 10.31/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.31/10.56  thf('154', plain, ((v3_pre_topc @ sk_B @ sk_C_1)),
% 10.31/10.56      inference('demod', [status(thm)], ['150', '151', '152', '153'])).
% 10.31/10.56  thf('155', plain, ($false), inference('demod', [status(thm)], ['2', '154'])).
% 10.31/10.56  
% 10.31/10.56  % SZS output end Refutation
% 10.31/10.56  
% 10.31/10.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
