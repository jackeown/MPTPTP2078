%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PE5cBESjZG

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 259 expanded)
%              Number of leaves         :   31 (  90 expanded)
%              Depth                    :   13
%              Number of atoms          :  713 (3084 expanded)
%              Number of equality atoms :   36 ( 148 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
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

thf('14',plain,(
    ! [X30: $i,X31: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X30 ) @ X33 @ ( k2_struct_0 @ X30 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X30 ) @ X33 @ ( k2_struct_0 @ X30 ) ) @ X30 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v4_pre_topc @ X33 @ X31 )
      | ~ ( m1_pre_topc @ X30 @ X31 ) ) ),
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

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('16',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X2 @ X4 @ X3 )
        = ( k9_subset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ X0 @ sk_B )
        = ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('26',plain,(
    ! [X27: $i] :
      ( ( l1_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('27',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('30',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_pre_topc @ X22 @ X23 )
      | ( r1_tarski @ ( k2_struct_0 @ X22 ) @ ( k2_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('34',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_pre_topc @ X28 @ X29 )
      | ( l1_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ ( k2_struct_0 @ sk_C_1 ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','37'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    m1_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ ( k2_struct_0 @ sk_C_1 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['28','42'])).

thf('44',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('49',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_C_1 ) )
    = sk_B ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C_1 ) )
      = sk_B )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['44','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['35','36'])).

thf('52',plain,(
    ! [X27: $i] :
      ( ( l1_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('53',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C_1 ) )
    = sk_B ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['43','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('58',plain,
    ( ( k3_xboole_0 @ ( k2_struct_0 @ sk_C_1 ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['43','54'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ sk_C_1 @ X0 )
      | ~ ( v4_pre_topc @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v4_pre_topc @ sk_B @ sk_C_1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['15','55','56','57','58'])).

thf('60',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_C_1 )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v4_pre_topc @ sk_B @ sk_C_1 ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['2','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PE5cBESjZG
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:14:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 283 iterations in 0.134s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.20/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.56  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.20/0.56  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.56  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.56  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(t34_tops_2, conjecture,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56           ( ![C:$i]:
% 0.20/0.56             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.56               ( ( v4_pre_topc @ B @ A ) =>
% 0.20/0.56                 ( ![D:$i]:
% 0.20/0.56                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.20/0.56                     ( ( ( D ) = ( B ) ) => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i]:
% 0.20/0.56        ( ( l1_pre_topc @ A ) =>
% 0.20/0.56          ( ![B:$i]:
% 0.20/0.56            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.56              ( ![C:$i]:
% 0.20/0.56                ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.56                  ( ( v4_pre_topc @ B @ A ) =>
% 0.20/0.56                    ( ![D:$i]:
% 0.20/0.56                      ( ( m1_subset_1 @
% 0.20/0.56                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.20/0.56                        ( ( ( D ) = ( B ) ) => ( v4_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t34_tops_2])).
% 0.20/0.56  thf('0', plain, (~ (v4_pre_topc @ sk_D_3 @ sk_C_1)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('1', plain, (((sk_D_3) = (sk_B))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('2', plain, (~ (v4_pre_topc @ sk_B @ sk_C_1)),
% 0.20/0.56      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('5', plain, (((sk_D_3) = (sk_B))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.56      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.56  thf(commutativity_k9_subset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.56         (((k9_subset_1 @ X2 @ X4 @ X3) = (k9_subset_1 @ X2 @ X3 @ X4))
% 0.20/0.56          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.20/0.56      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.20/0.56  thf('8', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ X0 @ sk_B)
% 0.20/0.56           = (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.56  thf('9', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.56      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.56  thf(redefinition_k9_subset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.56       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.56         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 0.20/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.56      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ X0 @ sk_B)
% 0.20/0.56           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k3_xboole_0 @ X0 @ sk_B)
% 0.20/0.56           = (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['8', '11'])).
% 0.20/0.56  thf(t43_pre_topc, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.56           ( ![C:$i]:
% 0.20/0.56             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.56               ( ( v4_pre_topc @ C @ B ) <=>
% 0.20/0.56                 ( ?[D:$i]:
% 0.20/0.56                   ( ( ( k9_subset_1 @
% 0.20/0.56                         ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) =
% 0.20/0.56                       ( C ) ) & 
% 0.20/0.56                     ( v4_pre_topc @ D @ A ) & 
% 0.20/0.56                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('13', plain,
% 0.20/0.56      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.56         (~ (m1_pre_topc @ X30 @ X31)
% 0.20/0.56          | ((k9_subset_1 @ (u1_struct_0 @ X30) @ X33 @ (k2_struct_0 @ X30))
% 0.20/0.56              != (X32))
% 0.20/0.56          | ~ (v4_pre_topc @ X33 @ X31)
% 0.20/0.56          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.20/0.56          | (v4_pre_topc @ X32 @ X30)
% 0.20/0.56          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.20/0.56          | ~ (l1_pre_topc @ X31))),
% 0.20/0.56      inference('cnf', [status(esa)], [t43_pre_topc])).
% 0.20/0.56  thf('14', plain,
% 0.20/0.56      (![X30 : $i, X31 : $i, X33 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X31)
% 0.20/0.56          | ~ (m1_subset_1 @ 
% 0.20/0.56               (k9_subset_1 @ (u1_struct_0 @ X30) @ X33 @ (k2_struct_0 @ X30)) @ 
% 0.20/0.56               (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.20/0.56          | (v4_pre_topc @ 
% 0.20/0.56             (k9_subset_1 @ (u1_struct_0 @ X30) @ X33 @ (k2_struct_0 @ X30)) @ 
% 0.20/0.56             X30)
% 0.20/0.56          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.20/0.56          | ~ (v4_pre_topc @ X33 @ X31)
% 0.20/0.56          | ~ (m1_pre_topc @ X30 @ X31))),
% 0.20/0.56      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.56  thf('15', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_subset_1 @ (k3_xboole_0 @ (k2_struct_0 @ sk_C_1) @ sk_B) @ 
% 0.20/0.56             (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))
% 0.20/0.56          | ~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.20/0.56          | ~ (v4_pre_topc @ sk_B @ X0)
% 0.20/0.56          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.56          | (v4_pre_topc @ 
% 0.20/0.56             (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ 
% 0.20/0.56              (k2_struct_0 @ sk_C_1)) @ 
% 0.20/0.56             sk_C_1)
% 0.20/0.56          | ~ (l1_pre_topc @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['12', '14'])).
% 0.20/0.56  thf(d3_struct_0, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      (![X16 : $i]:
% 0.20/0.56         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.56  thf('17', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('18', plain,
% 0.20/0.56      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.56         (((k9_subset_1 @ X2 @ X4 @ X3) = (k9_subset_1 @ X2 @ X3 @ X4))
% 0.20/0.56          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.20/0.56      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.20/0.56           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.56         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 0.20/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.56      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.20/0.56           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.56  thf('23', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k3_xboole_0 @ X0 @ sk_B)
% 0.20/0.56           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['19', '22'])).
% 0.20/0.56  thf('24', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (((k3_xboole_0 @ X0 @ sk_B)
% 0.20/0.56            = (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ X0))
% 0.20/0.56          | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.56      inference('sup+', [status(thm)], ['16', '23'])).
% 0.20/0.56  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(dt_l1_pre_topc, axiom,
% 0.20/0.56    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      (![X27 : $i]: ((l1_struct_0 @ X27) | ~ (l1_pre_topc @ X27))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.56  thf('27', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.56  thf('28', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k3_xboole_0 @ X0 @ sk_B)
% 0.20/0.56           = (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['24', '27'])).
% 0.20/0.56  thf('29', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(d9_pre_topc, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( l1_pre_topc @ B ) =>
% 0.20/0.56           ( ( m1_pre_topc @ B @ A ) <=>
% 0.20/0.56             ( ( ![C:$i]:
% 0.20/0.56                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.56                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.20/0.56                     ( ?[D:$i]:
% 0.20/0.56                       ( ( m1_subset_1 @
% 0.20/0.56                           D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.20/0.56                         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.20/0.56                         ( ( C ) =
% 0.20/0.56                           ( k9_subset_1 @
% 0.20/0.56                             ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) ) ) ) ) ) & 
% 0.20/0.56               ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.56  thf(zf_stmt_2, axiom,
% 0.20/0.56    (![D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.56     ( ( zip_tseitin_0 @ D @ C @ B @ A ) <=>
% 0.20/0.56       ( ( ( C ) =
% 0.20/0.56           ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) ) & 
% 0.20/0.56         ( r2_hidden @ D @ ( u1_pre_topc @ A ) ) & 
% 0.20/0.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_3, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( l1_pre_topc @ B ) =>
% 0.20/0.56           ( ( m1_pre_topc @ B @ A ) <=>
% 0.20/0.56             ( ( r1_tarski @ ( k2_struct_0 @ B ) @ ( k2_struct_0 @ A ) ) & 
% 0.20/0.56               ( ![C:$i]:
% 0.20/0.56                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.56                   ( ( r2_hidden @ C @ ( u1_pre_topc @ B ) ) <=>
% 0.20/0.56                     ( ?[D:$i]: ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      (![X22 : $i, X23 : $i]:
% 0.20/0.56         (~ (l1_pre_topc @ X22)
% 0.20/0.56          | ~ (m1_pre_topc @ X22 @ X23)
% 0.20/0.56          | (r1_tarski @ (k2_struct_0 @ X22) @ (k2_struct_0 @ X23))
% 0.20/0.56          | ~ (l1_pre_topc @ X23))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.56  thf('31', plain,
% 0.20/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | (r1_tarski @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_A))
% 0.20/0.56        | ~ (l1_pre_topc @ sk_C_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.56  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('33', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(dt_m1_pre_topc, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( l1_pre_topc @ A ) =>
% 0.20/0.56       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      (![X28 : $i, X29 : $i]:
% 0.20/0.56         (~ (m1_pre_topc @ X28 @ X29)
% 0.20/0.56          | (l1_pre_topc @ X28)
% 0.20/0.56          | ~ (l1_pre_topc @ X29))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.56  thf('35', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.56  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('37', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.56      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.56  thf('38', plain,
% 0.20/0.56      ((r1_tarski @ (k2_struct_0 @ sk_C_1) @ (k2_struct_0 @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['31', '32', '37'])).
% 0.20/0.56  thf(t3_subset, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.56  thf('39', plain,
% 0.20/0.56      (![X13 : $i, X15 : $i]:
% 0.20/0.56         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 0.20/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.56  thf('40', plain,
% 0.20/0.56      ((m1_subset_1 @ (k2_struct_0 @ sk_C_1) @ 
% 0.20/0.56        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.56  thf('41', plain,
% 0.20/0.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.56         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 0.20/0.56          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.20/0.56      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.20/0.56  thf('42', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ (k2_struct_0 @ sk_C_1))
% 0.20/0.56           = (k3_xboole_0 @ X0 @ (k2_struct_0 @ sk_C_1)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.56  thf('43', plain,
% 0.20/0.56      (((k3_xboole_0 @ (k2_struct_0 @ sk_C_1) @ sk_B)
% 0.20/0.56         = (k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C_1)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['28', '42'])).
% 0.20/0.56  thf('44', plain,
% 0.20/0.56      (![X16 : $i]:
% 0.20/0.56         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 0.20/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.20/0.56  thf('45', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.56      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i]:
% 0.20/0.56         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.20/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.56  thf('47', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_C_1))),
% 0.20/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.56  thf(t28_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.56  thf('48', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.56  thf('49', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_C_1)) = (sk_B))),
% 0.20/0.56      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.56  thf('50', plain,
% 0.20/0.56      ((((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C_1)) = (sk_B))
% 0.20/0.56        | ~ (l1_struct_0 @ sk_C_1))),
% 0.20/0.56      inference('sup+', [status(thm)], ['44', '49'])).
% 0.20/0.56  thf('51', plain, ((l1_pre_topc @ sk_C_1)),
% 0.20/0.56      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.56  thf('52', plain,
% 0.20/0.56      (![X27 : $i]: ((l1_struct_0 @ X27) | ~ (l1_pre_topc @ X27))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.56  thf('53', plain, ((l1_struct_0 @ sk_C_1)),
% 0.20/0.56      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.56  thf('54', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C_1)) = (sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['50', '53'])).
% 0.20/0.56  thf('55', plain, (((k3_xboole_0 @ (k2_struct_0 @ sk_C_1) @ sk_B) = (sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['43', '54'])).
% 0.20/0.56  thf('56', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.20/0.56      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.56  thf('57', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((k3_xboole_0 @ X0 @ sk_B)
% 0.20/0.56           = (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['8', '11'])).
% 0.20/0.56  thf('58', plain, (((k3_xboole_0 @ (k2_struct_0 @ sk_C_1) @ sk_B) = (sk_B))),
% 0.20/0.56      inference('demod', [status(thm)], ['43', '54'])).
% 0.20/0.56  thf('59', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (m1_pre_topc @ sk_C_1 @ X0)
% 0.20/0.56          | ~ (v4_pre_topc @ sk_B @ X0)
% 0.20/0.56          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.20/0.56          | (v4_pre_topc @ sk_B @ sk_C_1)
% 0.20/0.56          | ~ (l1_pre_topc @ X0))),
% 0.20/0.56      inference('demod', [status(thm)], ['15', '55', '56', '57', '58'])).
% 0.20/0.56  thf('60', plain,
% 0.20/0.56      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.56        | (v4_pre_topc @ sk_B @ sk_C_1)
% 0.20/0.56        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.20/0.56        | ~ (m1_pre_topc @ sk_C_1 @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['3', '59'])).
% 0.20/0.56  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('62', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('63', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('64', plain, ((v4_pre_topc @ sk_B @ sk_C_1)),
% 0.20/0.56      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.20/0.56  thf('65', plain, ($false), inference('demod', [status(thm)], ['2', '64'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
