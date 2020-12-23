%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lLllJfCNUo

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:35 EST 2020

% Result     : Theorem 14.02s
% Output     : Refutation 14.02s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 642 expanded)
%              Number of leaves         :   37 ( 207 expanded)
%              Depth                    :   18
%              Number of atoms          : 1108 (6899 expanded)
%              Number of equality atoms :   51 ( 312 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

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
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X20 @ X21 ) @ X20 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( l1_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X16 )
      | ( r1_tarski @ ( k2_struct_0 @ X15 ) @ ( k2_struct_0 @ X16 ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('19',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('20',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('21',plain,(
    ! [X2: $i] :
      ( ( k2_subset_1 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('22',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('23',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X26 @ X25 ) )
        = X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('26',plain,(
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('29',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('30',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X26 @ X25 ) )
        = X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X0 @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('38',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X26 @ X25 ) )
        = X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('41',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
      = sk_B )
    | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['36','41'])).

thf('43',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(demod,[status(thm)],['8','13'])).

thf('44',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( l1_pre_topc @ X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('47',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_C_1 @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['42','47'])).

thf('49',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('50',plain,(
    r1_tarski @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['18','48','49'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('52',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C_1 ) )
    = sk_B ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
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

thf('54',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_pre_topc @ X30 @ X31 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X30 ) @ X33 @ ( k2_struct_0 @ X30 ) )
       != X32 )
      | ~ ( v4_pre_topc @ X33 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( v4_pre_topc @ X32 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t43_pre_topc])).

thf('55',plain,(
    ! [X30: $i,X31: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X30 ) @ X33 @ ( k2_struct_0 @ X30 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X30 ) @ X33 @ ( k2_struct_0 @ X30 ) ) @ X30 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v4_pre_topc @ X33 @ X31 )
      | ~ ( m1_pre_topc @ X30 @ X31 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k9_subset_1 @ ( k2_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( v4_pre_topc @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('58',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k9_subset_1 @ X6 @ X4 @ X5 )
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( v4_pre_topc @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v4_pre_topc @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( l1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['52','60'])).

thf('62',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('63',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t39_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('65',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X26 @ X25 ) )
        = X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('71',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) )
      = ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ ( u1_struct_0 @ sk_C_1 ) ) )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) )
      = ( u1_struct_0 @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['62','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('76',plain,(
    ! [X22: $i] :
      ( ( l1_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('77',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) )
    = ( u1_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['74','77'])).

thf('79',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('82',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X27 @ X28 )
      | ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t39_pre_topc])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( m1_pre_topc @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,
    ( ~ ( l1_pre_topc @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X26 @ X25 ) )
        = X25 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('90',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) )
      = ( k2_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ ( k2_struct_0 @ sk_C_1 ) ) )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['78','92'])).

thf('94',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('96',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C_1 ) ) )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['75','76'])).

thf('98',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( u1_struct_0 @ sk_C_1 )
    = ( k2_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['78','92'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('101',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C_1 ) )
    = sk_B ),
    inference('sup-',[status(thm)],['50','51'])).

thf('102',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['75','76'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ sk_B @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v4_pre_topc @ sk_B @ X0 )
      | ~ ( m1_pre_topc @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['61','93','98','99','100','101','102'])).

thf('104',plain,
    ( ~ ( m1_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_C_1 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['3','103'])).

thf('105',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v4_pre_topc @ sk_B @ sk_C_1 ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,(
    $false ),
    inference(demod,[status(thm)],['2','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lLllJfCNUo
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:09:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 14.02/14.18  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 14.02/14.18  % Solved by: fo/fo7.sh
% 14.02/14.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.02/14.18  % done 7562 iterations in 13.695s
% 14.02/14.18  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 14.02/14.18  % SZS output start Refutation
% 14.02/14.18  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 14.02/14.18  thf(sk_B_type, type, sk_B: $i).
% 14.02/14.18  thf(sk_C_1_type, type, sk_C_1: $i).
% 14.02/14.18  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 14.02/14.18  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 14.02/14.18  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 14.02/14.18  thf(sk_A_type, type, sk_A: $i).
% 14.02/14.18  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 14.02/14.18  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 14.02/14.18  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 14.02/14.18  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 14.02/14.18  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 14.02/14.18  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 14.02/14.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 14.02/14.18  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 14.02/14.18  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 14.02/14.18  thf(sk_D_3_type, type, sk_D_3: $i).
% 14.02/14.18  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 14.02/14.18  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 14.02/14.18  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 14.02/14.18  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 14.02/14.18  thf(t34_tops_2, conjecture,
% 14.02/14.18    (![A:$i]:
% 14.02/14.18     ( ( l1_pre_topc @ A ) =>
% 14.02/14.18       ( ![B:$i]:
% 14.02/14.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 14.02/14.18           ( ![C:$i]:
% 14.02/14.18             ( ( m1_pre_topc @ C @ A ) =>
% 14.02/14.18               ( ( v4_pre_topc @ B @ A ) =>
% 14.02/14.18                 ( ![D:$i]:
% 14.02/14.18                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 14.02/14.18                     ( ( ( D ) = ( B ) ) => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 14.02/14.18  thf(zf_stmt_0, negated_conjecture,
% 14.02/14.18    (~( ![A:$i]:
% 14.02/14.18        ( ( l1_pre_topc @ A ) =>
% 14.02/14.18          ( ![B:$i]:
% 14.02/14.18            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 14.02/14.18              ( ![C:$i]:
% 14.02/14.18                ( ( m1_pre_topc @ C @ A ) =>
% 14.02/14.18                  ( ( v4_pre_topc @ B @ A ) =>
% 14.02/14.18                    ( ![D:$i]:
% 14.02/14.18                      ( ( m1_subset_1 @
% 14.02/14.18                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 14.02/14.18                        ( ( ( D ) = ( B ) ) => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 14.02/14.18    inference('cnf.neg', [status(esa)], [t34_tops_2])).
% 14.02/14.18  thf('0', plain, (~ (v4_pre_topc @ sk_D_3 @ sk_C_1)),
% 14.02/14.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.02/14.18  thf('1', plain, (((sk_D_3) = (sk_B))),
% 14.02/14.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.02/14.18  thf('2', plain, (~ (v4_pre_topc @ sk_B @ sk_C_1)),
% 14.02/14.18      inference('demod', [status(thm)], ['0', '1'])).
% 14.02/14.18  thf('3', plain,
% 14.02/14.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.02/14.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.02/14.18  thf('4', plain,
% 14.02/14.18      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 14.02/14.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.02/14.18  thf('5', plain, (((sk_D_3) = (sk_B))),
% 14.02/14.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.02/14.18  thf('6', plain,
% 14.02/14.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 14.02/14.18      inference('demod', [status(thm)], ['4', '5'])).
% 14.02/14.18  thf(dt_k1_pre_topc, axiom,
% 14.02/14.18    (![A:$i,B:$i]:
% 14.02/14.18     ( ( ( l1_pre_topc @ A ) & 
% 14.02/14.18         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 14.02/14.18       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 14.02/14.18         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 14.02/14.18  thf('7', plain,
% 14.02/14.18      (![X20 : $i, X21 : $i]:
% 14.02/14.18         (~ (l1_pre_topc @ X20)
% 14.02/14.18          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 14.02/14.18          | (m1_pre_topc @ (k1_pre_topc @ X20 @ X21) @ X20))),
% 14.02/14.18      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 14.02/14.18  thf('8', plain,
% 14.02/14.18      (((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)
% 14.02/14.18        | ~ (l1_pre_topc @ sk_C_1))),
% 14.02/14.18      inference('sup-', [status(thm)], ['6', '7'])).
% 14.02/14.18  thf('9', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 14.02/14.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.02/14.18  thf(dt_m1_pre_topc, axiom,
% 14.02/14.18    (![A:$i]:
% 14.02/14.18     ( ( l1_pre_topc @ A ) =>
% 14.02/14.18       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 14.02/14.18  thf('10', plain,
% 14.02/14.18      (![X23 : $i, X24 : $i]:
% 14.02/14.18         (~ (m1_pre_topc @ X23 @ X24)
% 14.02/14.18          | (l1_pre_topc @ X23)
% 14.02/14.18          | ~ (l1_pre_topc @ X24))),
% 14.02/14.18      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 14.02/14.18  thf('11', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 14.02/14.18      inference('sup-', [status(thm)], ['9', '10'])).
% 14.02/14.18  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 14.02/14.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.02/14.18  thf('13', plain, ((l1_pre_topc @ sk_C_1)),
% 14.02/14.18      inference('demod', [status(thm)], ['11', '12'])).
% 14.02/14.18  thf('14', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)),
% 14.02/14.18      inference('demod', [status(thm)], ['8', '13'])).
% 14.02/14.18  thf(d9_pre_topc, axiom,
% 14.02/14.18    (![A:$i]:
% 14.02/14.18     ( ( l1_pre_topc @ A ) =>
% 14.02/14.18       ( ![B:$i]:
% 14.02/14.18         ( ( l1_pre_topc @ B ) =>
% 14.02/14.18           ( ( m1_pre_topc @ B @ A ) <=>
% 14.02/14.18             ( ( ![C:$i]:
% 14.02/14.18                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 14.02/14.18                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 14.02/14.18                     ( ?[D:$i]:
% 14.02/14.18                       ( ( m1_subset_1 @
% 14.02/14.18                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 14.02/14.18                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 14.02/14.18                         ( ( C ) =
% 14.02/14.18                           ( k9_subset_1 @
% 14.02/14.18                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 14.02/14.18               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 14.02/14.18  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 14.02/14.18  thf(zf_stmt_2, axiom,
% 14.02/14.18    (![D:$i,C:$i,B:$i,A:$i]:
% 14.02/14.18     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 14.02/14.18       ( ( ( C ) =
% 14.02/14.18           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 14.02/14.18         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 14.02/14.18         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 14.02/14.18  thf(zf_stmt_3, axiom,
% 14.02/14.18    (![A:$i]:
% 14.02/14.18     ( ( l1_pre_topc @ A ) =>
% 14.02/14.18       ( ![B:$i]:
% 14.02/14.18         ( ( l1_pre_topc @ B ) =>
% 14.02/14.18           ( ( m1_pre_topc @ B @ A ) <=>
% 14.02/14.18             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 14.02/14.18               ( ![C:$i]:
% 14.02/14.18                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 14.02/14.18                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 14.02/14.18                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 14.02/14.18  thf('15', plain,
% 14.02/14.18      (![X15 : $i, X16 : $i]:
% 14.02/14.18         (~ (l1_pre_topc @ X15)
% 14.02/14.18          | ~ (m1_pre_topc @ X15 @ X16)
% 14.02/14.18          | (r1_tarski @ (k2_struct_0 @ X15) @ (k2_struct_0 @ X16))
% 14.02/14.18          | ~ (l1_pre_topc @ X16))),
% 14.02/14.18      inference('cnf', [status(esa)], [zf_stmt_3])).
% 14.02/14.18  thf('16', plain,
% 14.02/14.18      ((~ (l1_pre_topc @ sk_C_1)
% 14.02/14.18        | (r1_tarski @ (k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) @ 
% 14.02/14.18           (k2_struct_0 @ sk_C_1))
% 14.02/14.18        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 14.02/14.18      inference('sup-', [status(thm)], ['14', '15'])).
% 14.02/14.18  thf('17', plain, ((l1_pre_topc @ sk_C_1)),
% 14.02/14.18      inference('demod', [status(thm)], ['11', '12'])).
% 14.02/14.18  thf('18', plain,
% 14.02/14.18      (((r1_tarski @ (k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) @ 
% 14.02/14.18         (k2_struct_0 @ sk_C_1))
% 14.02/14.18        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 14.02/14.18      inference('demod', [status(thm)], ['16', '17'])).
% 14.02/14.18  thf(d3_struct_0, axiom,
% 14.02/14.18    (![A:$i]:
% 14.02/14.18     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 14.02/14.18  thf('19', plain,
% 14.02/14.18      (![X9 : $i]:
% 14.02/14.18         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 14.02/14.18      inference('cnf', [status(esa)], [d3_struct_0])).
% 14.02/14.18  thf(dt_k2_subset_1, axiom,
% 14.02/14.18    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 14.02/14.18  thf('20', plain,
% 14.02/14.18      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 14.02/14.18      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 14.02/14.18  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 14.02/14.18  thf('21', plain, (![X2 : $i]: ((k2_subset_1 @ X2) = (X2))),
% 14.02/14.18      inference('cnf', [status(esa)], [d4_subset_1])).
% 14.02/14.18  thf('22', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 14.02/14.18      inference('demod', [status(thm)], ['20', '21'])).
% 14.02/14.18  thf(t29_pre_topc, axiom,
% 14.02/14.18    (![A:$i]:
% 14.02/14.18     ( ( l1_pre_topc @ A ) =>
% 14.02/14.18       ( ![B:$i]:
% 14.02/14.18         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 14.02/14.18           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 14.02/14.18  thf('23', plain,
% 14.02/14.18      (![X25 : $i, X26 : $i]:
% 14.02/14.18         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 14.02/14.18          | ((u1_struct_0 @ (k1_pre_topc @ X26 @ X25)) = (X25))
% 14.02/14.18          | ~ (l1_pre_topc @ X26))),
% 14.02/14.18      inference('cnf', [status(esa)], [t29_pre_topc])).
% 14.02/14.18  thf('24', plain,
% 14.02/14.18      (![X0 : $i]:
% 14.02/14.18         (~ (l1_pre_topc @ X0)
% 14.02/14.18          | ((u1_struct_0 @ (k1_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 14.02/14.18              = (u1_struct_0 @ X0)))),
% 14.02/14.18      inference('sup-', [status(thm)], ['22', '23'])).
% 14.02/14.18  thf('25', plain,
% 14.02/14.18      (![X0 : $i]:
% 14.02/14.18         (((u1_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 14.02/14.18            = (u1_struct_0 @ X0))
% 14.02/14.18          | ~ (l1_struct_0 @ X0)
% 14.02/14.18          | ~ (l1_pre_topc @ X0))),
% 14.02/14.18      inference('sup+', [status(thm)], ['19', '24'])).
% 14.02/14.18  thf(dt_l1_pre_topc, axiom,
% 14.02/14.18    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 14.02/14.18  thf('26', plain,
% 14.02/14.18      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_pre_topc @ X22))),
% 14.02/14.18      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 14.02/14.18  thf('27', plain,
% 14.02/14.18      (![X0 : $i]:
% 14.02/14.18         (~ (l1_pre_topc @ X0)
% 14.02/14.18          | ((u1_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 14.02/14.18              = (u1_struct_0 @ X0)))),
% 14.02/14.18      inference('clc', [status(thm)], ['25', '26'])).
% 14.02/14.18  thf('28', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 14.02/14.18      inference('demod', [status(thm)], ['20', '21'])).
% 14.02/14.18  thf('29', plain,
% 14.02/14.18      (![X9 : $i]:
% 14.02/14.18         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 14.02/14.18      inference('cnf', [status(esa)], [d3_struct_0])).
% 14.02/14.18  thf('30', plain,
% 14.02/14.18      (![X25 : $i, X26 : $i]:
% 14.02/14.18         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 14.02/14.18          | ((u1_struct_0 @ (k1_pre_topc @ X26 @ X25)) = (X25))
% 14.02/14.18          | ~ (l1_pre_topc @ X26))),
% 14.02/14.18      inference('cnf', [status(esa)], [t29_pre_topc])).
% 14.02/14.18  thf('31', plain,
% 14.02/14.18      (![X0 : $i, X1 : $i]:
% 14.02/14.18         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 14.02/14.18          | ~ (l1_struct_0 @ X0)
% 14.02/14.18          | ~ (l1_pre_topc @ X0)
% 14.02/14.18          | ((u1_struct_0 @ (k1_pre_topc @ X0 @ X1)) = (X1)))),
% 14.02/14.18      inference('sup-', [status(thm)], ['29', '30'])).
% 14.02/14.18  thf('32', plain,
% 14.02/14.18      (![X0 : $i]:
% 14.02/14.18         (((u1_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 14.02/14.18            = (k2_struct_0 @ X0))
% 14.02/14.18          | ~ (l1_pre_topc @ X0)
% 14.02/14.18          | ~ (l1_struct_0 @ X0))),
% 14.02/14.18      inference('sup-', [status(thm)], ['28', '31'])).
% 14.02/14.18  thf('33', plain,
% 14.02/14.18      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_pre_topc @ X22))),
% 14.02/14.18      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 14.02/14.18  thf('34', plain,
% 14.02/14.18      (![X0 : $i]:
% 14.02/14.18         (~ (l1_pre_topc @ X0)
% 14.02/14.18          | ((u1_struct_0 @ (k1_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 14.02/14.18              = (k2_struct_0 @ X0)))),
% 14.02/14.18      inference('clc', [status(thm)], ['32', '33'])).
% 14.02/14.18  thf('35', plain,
% 14.02/14.18      (![X0 : $i]:
% 14.02/14.18         (((u1_struct_0 @ X0) = (k2_struct_0 @ X0))
% 14.02/14.18          | ~ (l1_pre_topc @ X0)
% 14.02/14.18          | ~ (l1_pre_topc @ X0))),
% 14.02/14.18      inference('sup+', [status(thm)], ['27', '34'])).
% 14.02/14.18  thf('36', plain,
% 14.02/14.18      (![X0 : $i]:
% 14.02/14.18         (~ (l1_pre_topc @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 14.02/14.18      inference('simplify', [status(thm)], ['35'])).
% 14.02/14.18  thf('37', plain,
% 14.02/14.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 14.02/14.18      inference('demod', [status(thm)], ['4', '5'])).
% 14.02/14.18  thf('38', plain,
% 14.02/14.18      (![X25 : $i, X26 : $i]:
% 14.02/14.18         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 14.02/14.18          | ((u1_struct_0 @ (k1_pre_topc @ X26 @ X25)) = (X25))
% 14.02/14.18          | ~ (l1_pre_topc @ X26))),
% 14.02/14.18      inference('cnf', [status(esa)], [t29_pre_topc])).
% 14.02/14.18  thf('39', plain,
% 14.02/14.18      ((~ (l1_pre_topc @ sk_C_1)
% 14.02/14.18        | ((u1_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) = (sk_B)))),
% 14.02/14.18      inference('sup-', [status(thm)], ['37', '38'])).
% 14.02/14.18  thf('40', plain, ((l1_pre_topc @ sk_C_1)),
% 14.02/14.18      inference('demod', [status(thm)], ['11', '12'])).
% 14.02/14.18  thf('41', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) = (sk_B))),
% 14.02/14.18      inference('demod', [status(thm)], ['39', '40'])).
% 14.02/14.18  thf('42', plain,
% 14.02/14.18      ((((k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) = (sk_B))
% 14.02/14.18        | ~ (l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 14.02/14.18      inference('sup+', [status(thm)], ['36', '41'])).
% 14.02/14.18  thf('43', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B) @ sk_C_1)),
% 14.02/14.18      inference('demod', [status(thm)], ['8', '13'])).
% 14.02/14.18  thf('44', plain,
% 14.02/14.18      (![X23 : $i, X24 : $i]:
% 14.02/14.18         (~ (m1_pre_topc @ X23 @ X24)
% 14.02/14.18          | (l1_pre_topc @ X23)
% 14.02/14.18          | ~ (l1_pre_topc @ X24))),
% 14.02/14.18      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 14.02/14.18  thf('45', plain,
% 14.02/14.18      ((~ (l1_pre_topc @ sk_C_1)
% 14.02/14.18        | (l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B)))),
% 14.02/14.18      inference('sup-', [status(thm)], ['43', '44'])).
% 14.02/14.18  thf('46', plain, ((l1_pre_topc @ sk_C_1)),
% 14.02/14.18      inference('demod', [status(thm)], ['11', '12'])).
% 14.02/14.18  thf('47', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))),
% 14.02/14.18      inference('demod', [status(thm)], ['45', '46'])).
% 14.02/14.18  thf('48', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_C_1 @ sk_B)) = (sk_B))),
% 14.02/14.18      inference('demod', [status(thm)], ['42', '47'])).
% 14.02/14.18  thf('49', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_C_1 @ sk_B))),
% 14.02/14.18      inference('demod', [status(thm)], ['45', '46'])).
% 14.02/14.18  thf('50', plain, ((r1_tarski @ sk_B @ (k2_struct_0 @ sk_C_1))),
% 14.02/14.18      inference('demod', [status(thm)], ['18', '48', '49'])).
% 14.02/14.18  thf(t28_xboole_1, axiom,
% 14.02/14.18    (![A:$i,B:$i]:
% 14.02/14.18     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 14.02/14.18  thf('51', plain,
% 14.02/14.18      (![X0 : $i, X1 : $i]:
% 14.02/14.18         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 14.02/14.18      inference('cnf', [status(esa)], [t28_xboole_1])).
% 14.02/14.18  thf('52', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C_1)) = (sk_B))),
% 14.02/14.18      inference('sup-', [status(thm)], ['50', '51'])).
% 14.02/14.18  thf('53', plain,
% 14.02/14.18      (![X9 : $i]:
% 14.02/14.18         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 14.02/14.18      inference('cnf', [status(esa)], [d3_struct_0])).
% 14.02/14.18  thf(t43_pre_topc, axiom,
% 14.02/14.18    (![A:$i]:
% 14.02/14.18     ( ( l1_pre_topc @ A ) =>
% 14.02/14.18       ( ![B:$i]:
% 14.02/14.18         ( ( m1_pre_topc @ B @ A ) =>
% 14.02/14.18           ( ![C:$i]:
% 14.02/14.18             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 14.02/14.18               ( ( v4_pre_topc @ C @ B ) <=>
% 14.02/14.18                 ( ?[D:$i]:
% 14.02/14.18                   ( ( ( k9_subset_1 @
% 14.02/14.18                         ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) =
% 14.02/14.18                       ( C ) ) & 
% 14.02/14.18                     ( v4_pre_topc @ D @ A ) & 
% 14.02/14.18                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 14.02/14.18  thf('54', plain,
% 14.02/14.18      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 14.02/14.18         (~ (m1_pre_topc @ X30 @ X31)
% 14.02/14.18          | ((k9_subset_1 @ (u1_struct_0 @ X30) @ X33 @ (k2_struct_0 @ X30))
% 14.02/14.18              != (X32))
% 14.02/14.18          | ~ (v4_pre_topc @ X33 @ X31)
% 14.02/14.18          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 14.02/14.18          | (v4_pre_topc @ X32 @ X30)
% 14.02/14.18          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 14.02/14.18          | ~ (l1_pre_topc @ X31))),
% 14.02/14.18      inference('cnf', [status(esa)], [t43_pre_topc])).
% 14.02/14.18  thf('55', plain,
% 14.02/14.18      (![X30 : $i, X31 : $i, X33 : $i]:
% 14.02/14.18         (~ (l1_pre_topc @ X31)
% 14.02/14.18          | ~ (m1_subset_1 @ 
% 14.02/14.18               (k9_subset_1 @ (u1_struct_0 @ X30) @ X33 @ (k2_struct_0 @ X30)) @ 
% 14.02/14.18               (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 14.02/14.18          | (v4_pre_topc @ 
% 14.02/14.18             (k9_subset_1 @ (u1_struct_0 @ X30) @ X33 @ (k2_struct_0 @ X30)) @ 
% 14.02/14.18             X30)
% 14.02/14.18          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 14.02/14.18          | ~ (v4_pre_topc @ X33 @ X31)
% 14.02/14.18          | ~ (m1_pre_topc @ X30 @ X31))),
% 14.02/14.18      inference('simplify', [status(thm)], ['54'])).
% 14.02/14.18  thf('56', plain,
% 14.02/14.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.02/14.18         (~ (m1_subset_1 @ 
% 14.02/14.18             (k9_subset_1 @ (k2_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ 
% 14.02/14.18             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 14.02/14.18          | ~ (l1_struct_0 @ X0)
% 14.02/14.18          | ~ (m1_pre_topc @ X0 @ X2)
% 14.02/14.18          | ~ (v4_pre_topc @ X1 @ X2)
% 14.02/14.18          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 14.02/14.18          | (v4_pre_topc @ 
% 14.02/14.18             (k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ X0)
% 14.02/14.18          | ~ (l1_pre_topc @ X2))),
% 14.02/14.18      inference('sup-', [status(thm)], ['53', '55'])).
% 14.02/14.18  thf('57', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 14.02/14.18      inference('demod', [status(thm)], ['20', '21'])).
% 14.02/14.18  thf(redefinition_k9_subset_1, axiom,
% 14.02/14.18    (![A:$i,B:$i,C:$i]:
% 14.02/14.18     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 14.02/14.18       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 14.02/14.18  thf('58', plain,
% 14.02/14.18      (![X4 : $i, X5 : $i, X6 : $i]:
% 14.02/14.18         (((k9_subset_1 @ X6 @ X4 @ X5) = (k3_xboole_0 @ X4 @ X5))
% 14.02/14.18          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 14.02/14.18      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 14.02/14.18  thf('59', plain,
% 14.02/14.18      (![X0 : $i, X1 : $i]:
% 14.02/14.18         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 14.02/14.18      inference('sup-', [status(thm)], ['57', '58'])).
% 14.02/14.18  thf('60', plain,
% 14.02/14.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.02/14.18         (~ (m1_subset_1 @ (k3_xboole_0 @ X1 @ (k2_struct_0 @ X0)) @ 
% 14.02/14.18             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 14.02/14.18          | ~ (l1_struct_0 @ X0)
% 14.02/14.18          | ~ (m1_pre_topc @ X0 @ X2)
% 14.02/14.18          | ~ (v4_pre_topc @ X1 @ X2)
% 14.02/14.18          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 14.02/14.18          | (v4_pre_topc @ 
% 14.02/14.18             (k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ X0)
% 14.02/14.18          | ~ (l1_pre_topc @ X2))),
% 14.02/14.18      inference('demod', [status(thm)], ['56', '59'])).
% 14.02/14.18  thf('61', plain,
% 14.02/14.18      (![X0 : $i]:
% 14.02/14.18         (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 14.02/14.18          | ~ (l1_pre_topc @ X0)
% 14.02/14.18          | (v4_pre_topc @ 
% 14.02/14.18             (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ 
% 14.02/14.18              (k2_struct_0 @ sk_C_1)) @ 
% 14.02/14.18             sk_C_1)
% 14.02/14.18          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 14.02/14.18          | ~ (v4_pre_topc @ sk_B @ X0)
% 14.02/14.18          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 14.02/14.18          | ~ (l1_struct_0 @ sk_C_1))),
% 14.02/14.18      inference('sup-', [status(thm)], ['52', '60'])).
% 14.02/14.18  thf('62', plain,
% 14.02/14.18      (![X9 : $i]:
% 14.02/14.18         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 14.02/14.18      inference('cnf', [status(esa)], [d3_struct_0])).
% 14.02/14.18  thf('63', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 14.02/14.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.02/14.18  thf('64', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 14.02/14.18      inference('demod', [status(thm)], ['20', '21'])).
% 14.02/14.18  thf(t39_pre_topc, axiom,
% 14.02/14.18    (![A:$i]:
% 14.02/14.18     ( ( l1_pre_topc @ A ) =>
% 14.02/14.18       ( ![B:$i]:
% 14.02/14.18         ( ( m1_pre_topc @ B @ A ) =>
% 14.02/14.18           ( ![C:$i]:
% 14.02/14.18             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 14.02/14.18               ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ))).
% 14.02/14.18  thf('65', plain,
% 14.02/14.18      (![X27 : $i, X28 : $i, X29 : $i]:
% 14.02/14.18         (~ (m1_pre_topc @ X27 @ X28)
% 14.02/14.18          | (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 14.02/14.18          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 14.02/14.18          | ~ (l1_pre_topc @ X28))),
% 14.02/14.18      inference('cnf', [status(esa)], [t39_pre_topc])).
% 14.02/14.18  thf('66', plain,
% 14.02/14.18      (![X0 : $i, X1 : $i]:
% 14.02/14.18         (~ (l1_pre_topc @ X1)
% 14.02/14.18          | (m1_subset_1 @ (u1_struct_0 @ X0) @ 
% 14.02/14.18             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 14.02/14.18          | ~ (m1_pre_topc @ X0 @ X1))),
% 14.02/14.18      inference('sup-', [status(thm)], ['64', '65'])).
% 14.02/14.18  thf('67', plain,
% 14.02/14.18      (((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 14.02/14.18         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 14.02/14.18        | ~ (l1_pre_topc @ sk_A))),
% 14.02/14.18      inference('sup-', [status(thm)], ['63', '66'])).
% 14.02/14.18  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 14.02/14.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.02/14.18  thf('69', plain,
% 14.02/14.18      ((m1_subset_1 @ (u1_struct_0 @ sk_C_1) @ 
% 14.02/14.18        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.02/14.18      inference('demod', [status(thm)], ['67', '68'])).
% 14.02/14.18  thf('70', plain,
% 14.02/14.18      (![X25 : $i, X26 : $i]:
% 14.02/14.18         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 14.02/14.18          | ((u1_struct_0 @ (k1_pre_topc @ X26 @ X25)) = (X25))
% 14.02/14.18          | ~ (l1_pre_topc @ X26))),
% 14.02/14.18      inference('cnf', [status(esa)], [t29_pre_topc])).
% 14.02/14.18  thf('71', plain,
% 14.02/14.18      ((~ (l1_pre_topc @ sk_A)
% 14.02/14.18        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)))
% 14.02/14.18            = (u1_struct_0 @ sk_C_1)))),
% 14.02/14.18      inference('sup-', [status(thm)], ['69', '70'])).
% 14.02/14.18  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 14.02/14.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.02/14.18  thf('73', plain,
% 14.02/14.18      (((u1_struct_0 @ (k1_pre_topc @ sk_A @ (u1_struct_0 @ sk_C_1)))
% 14.02/14.18         = (u1_struct_0 @ sk_C_1))),
% 14.02/14.18      inference('demod', [status(thm)], ['71', '72'])).
% 14.02/14.18  thf('74', plain,
% 14.02/14.18      ((((u1_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))
% 14.02/14.18          = (u1_struct_0 @ sk_C_1))
% 14.02/14.18        | ~ (l1_struct_0 @ sk_C_1))),
% 14.02/14.18      inference('sup+', [status(thm)], ['62', '73'])).
% 14.02/14.18  thf('75', plain, ((l1_pre_topc @ sk_C_1)),
% 14.02/14.18      inference('demod', [status(thm)], ['11', '12'])).
% 14.02/14.18  thf('76', plain,
% 14.02/14.18      (![X22 : $i]: ((l1_struct_0 @ X22) | ~ (l1_pre_topc @ X22))),
% 14.02/14.18      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 14.02/14.18  thf('77', plain, ((l1_struct_0 @ sk_C_1)),
% 14.02/14.18      inference('sup-', [status(thm)], ['75', '76'])).
% 14.02/14.18  thf('78', plain,
% 14.02/14.18      (((u1_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))
% 14.02/14.18         = (u1_struct_0 @ sk_C_1))),
% 14.02/14.18      inference('demod', [status(thm)], ['74', '77'])).
% 14.02/14.18  thf('79', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 14.02/14.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.02/14.18  thf('80', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 14.02/14.18      inference('demod', [status(thm)], ['20', '21'])).
% 14.02/14.18  thf('81', plain,
% 14.02/14.18      (![X0 : $i]:
% 14.02/14.18         (~ (l1_pre_topc @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 14.02/14.18      inference('simplify', [status(thm)], ['35'])).
% 14.02/14.18  thf('82', plain,
% 14.02/14.18      (![X27 : $i, X28 : $i, X29 : $i]:
% 14.02/14.18         (~ (m1_pre_topc @ X27 @ X28)
% 14.02/14.18          | (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 14.02/14.18          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 14.02/14.18          | ~ (l1_pre_topc @ X28))),
% 14.02/14.18      inference('cnf', [status(esa)], [t39_pre_topc])).
% 14.02/14.18  thf('83', plain,
% 14.02/14.18      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.02/14.18         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 14.02/14.18          | ~ (l1_pre_topc @ X0)
% 14.02/14.18          | ~ (l1_pre_topc @ X2)
% 14.02/14.18          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 14.02/14.18          | ~ (m1_pre_topc @ X0 @ X2))),
% 14.02/14.18      inference('sup-', [status(thm)], ['81', '82'])).
% 14.02/14.18  thf('84', plain,
% 14.02/14.18      (![X0 : $i, X1 : $i]:
% 14.02/14.18         (~ (m1_pre_topc @ X0 @ X1)
% 14.02/14.18          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 14.02/14.18             (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 14.02/14.18          | ~ (l1_pre_topc @ X1)
% 14.02/14.18          | ~ (l1_pre_topc @ X0))),
% 14.02/14.18      inference('sup-', [status(thm)], ['80', '83'])).
% 14.02/14.18  thf('85', plain,
% 14.02/14.18      ((~ (l1_pre_topc @ sk_C_1)
% 14.02/14.18        | ~ (l1_pre_topc @ sk_A)
% 14.02/14.18        | (m1_subset_1 @ (k2_struct_0 @ sk_C_1) @ 
% 14.02/14.18           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 14.02/14.18      inference('sup-', [status(thm)], ['79', '84'])).
% 14.02/14.18  thf('86', plain, ((l1_pre_topc @ sk_C_1)),
% 14.02/14.18      inference('demod', [status(thm)], ['11', '12'])).
% 14.02/14.18  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 14.02/14.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.02/14.18  thf('88', plain,
% 14.02/14.18      ((m1_subset_1 @ (k2_struct_0 @ sk_C_1) @ 
% 14.02/14.18        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.02/14.18      inference('demod', [status(thm)], ['85', '86', '87'])).
% 14.02/14.18  thf('89', plain,
% 14.02/14.18      (![X25 : $i, X26 : $i]:
% 14.02/14.18         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 14.02/14.18          | ((u1_struct_0 @ (k1_pre_topc @ X26 @ X25)) = (X25))
% 14.02/14.18          | ~ (l1_pre_topc @ X26))),
% 14.02/14.18      inference('cnf', [status(esa)], [t29_pre_topc])).
% 14.02/14.18  thf('90', plain,
% 14.02/14.18      ((~ (l1_pre_topc @ sk_A)
% 14.02/14.18        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))
% 14.02/14.18            = (k2_struct_0 @ sk_C_1)))),
% 14.02/14.18      inference('sup-', [status(thm)], ['88', '89'])).
% 14.02/14.18  thf('91', plain, ((l1_pre_topc @ sk_A)),
% 14.02/14.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.02/14.18  thf('92', plain,
% 14.02/14.18      (((u1_struct_0 @ (k1_pre_topc @ sk_A @ (k2_struct_0 @ sk_C_1)))
% 14.02/14.18         = (k2_struct_0 @ sk_C_1))),
% 14.02/14.18      inference('demod', [status(thm)], ['90', '91'])).
% 14.02/14.18  thf('93', plain, (((u1_struct_0 @ sk_C_1) = (k2_struct_0 @ sk_C_1))),
% 14.02/14.18      inference('sup+', [status(thm)], ['78', '92'])).
% 14.02/14.18  thf('94', plain,
% 14.02/14.18      (![X9 : $i]:
% 14.02/14.18         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 14.02/14.18      inference('cnf', [status(esa)], [d3_struct_0])).
% 14.02/14.18  thf('95', plain,
% 14.02/14.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 14.02/14.18      inference('demod', [status(thm)], ['4', '5'])).
% 14.02/14.18  thf('96', plain,
% 14.02/14.18      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C_1)))
% 14.02/14.18        | ~ (l1_struct_0 @ sk_C_1))),
% 14.02/14.18      inference('sup+', [status(thm)], ['94', '95'])).
% 14.02/14.18  thf('97', plain, ((l1_struct_0 @ sk_C_1)),
% 14.02/14.18      inference('sup-', [status(thm)], ['75', '76'])).
% 14.02/14.18  thf('98', plain,
% 14.02/14.18      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_C_1)))),
% 14.02/14.18      inference('demod', [status(thm)], ['96', '97'])).
% 14.02/14.18  thf('99', plain, (((u1_struct_0 @ sk_C_1) = (k2_struct_0 @ sk_C_1))),
% 14.02/14.18      inference('sup+', [status(thm)], ['78', '92'])).
% 14.02/14.18  thf('100', plain,
% 14.02/14.18      (![X0 : $i, X1 : $i]:
% 14.02/14.18         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 14.02/14.18      inference('sup-', [status(thm)], ['57', '58'])).
% 14.02/14.18  thf('101', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C_1)) = (sk_B))),
% 14.02/14.18      inference('sup-', [status(thm)], ['50', '51'])).
% 14.02/14.18  thf('102', plain, ((l1_struct_0 @ sk_C_1)),
% 14.02/14.18      inference('sup-', [status(thm)], ['75', '76'])).
% 14.02/14.18  thf('103', plain,
% 14.02/14.18      (![X0 : $i]:
% 14.02/14.18         (~ (l1_pre_topc @ X0)
% 14.02/14.18          | (v4_pre_topc @ sk_B @ sk_C_1)
% 14.02/14.18          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 14.02/14.18          | ~ (v4_pre_topc @ sk_B @ X0)
% 14.02/14.18          | ~ (m1_pre_topc @ sk_C_1 @ X0))),
% 14.02/14.18      inference('demod', [status(thm)],
% 14.02/14.18                ['61', '93', '98', '99', '100', '101', '102'])).
% 14.02/14.18  thf('104', plain,
% 14.02/14.18      ((~ (m1_pre_topc @ sk_C_1 @ sk_A)
% 14.02/14.18        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 14.02/14.18        | (v4_pre_topc @ sk_B @ sk_C_1)
% 14.02/14.18        | ~ (l1_pre_topc @ sk_A))),
% 14.02/14.18      inference('sup-', [status(thm)], ['3', '103'])).
% 14.02/14.18  thf('105', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 14.02/14.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.02/14.18  thf('106', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 14.02/14.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.02/14.18  thf('107', plain, ((l1_pre_topc @ sk_A)),
% 14.02/14.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.02/14.18  thf('108', plain, ((v4_pre_topc @ sk_B @ sk_C_1)),
% 14.02/14.18      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 14.02/14.18  thf('109', plain, ($false), inference('demod', [status(thm)], ['2', '108'])).
% 14.02/14.18  
% 14.02/14.18  % SZS output end Refutation
% 14.02/14.18  
% 14.02/14.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
