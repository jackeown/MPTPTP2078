%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WhtDYmM88I

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:39 EST 2020

% Result     : Theorem 1.01s
% Output     : Refutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 210 expanded)
%              Number of leaves         :   26 (  72 expanded)
%              Depth                    :   11
%              Number of atoms          :  921 (3378 expanded)
%              Number of equality atoms :   30 (  76 expanded)
%              Maximal formula depth    :   21 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tops_2_type,type,(
    k1_tops_2: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(t41_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                 => ( ( r2_hidden @ B @ D )
                   => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( k1_tops_2 @ A @ C @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                   => ( ( r2_hidden @ B @ D )
                     => ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( k1_tops_2 @ A @ C @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_tops_2])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_tops_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X7 @ X5 @ X6 )
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X2 @ X4 @ X3 )
        = ( k9_subset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ~ ( r2_hidden @ ( k3_xboole_0 @ sk_C @ sk_B ) @ ( k1_tops_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('9',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X7 @ X5 @ X6 )
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ~ ( r2_hidden @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k1_tops_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) )
                 => ( ( D
                      = ( k1_tops_2 @ A @ B @ C ) )
                  <=> ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) )
                       => ( ( r2_hidden @ E @ D )
                        <=> ? [F: $i] :
                              ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                              & ( r2_hidden @ F @ C )
                              & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ F @ B )
                                = E ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ C @ B @ A )
    <=> ( ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ F @ B )
          = E )
        & ( r2_hidden @ F @ C )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X18: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X20 @ X18 @ X22 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( r2_hidden @ X20 @ X22 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X20 @ X21 )
       != X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( zip_tseitin_0 @ X20 @ ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X20 @ X21 ) @ X22 @ X21 @ X23 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ X1 @ X0 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X2 @ X4 @ X3 )
        = ( k9_subset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_B ) @ X1 @ X0 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X1 ) ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_D @ X0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) )).

thf('29',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) ) )
      | ( m1_subset_1 @ ( k1_tops_2 @ X32 @ X31 @ X33 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X32 @ X31 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_2])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ ( k1_tops_2 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X17 @ X16 ) )
        = X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ ( k1_tops_2 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['36','37'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) )
                 => ( ( D
                      = ( k1_tops_2 @ A @ B @ C ) )
                  <=> ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) )
                       => ( ( r2_hidden @ E @ D )
                        <=> ? [F: $i] :
                              ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X25 @ X24 ) ) ) ) )
      | ( X26
       != ( k1_tops_2 @ X25 @ X24 @ X27 ) )
      | ( r2_hidden @ X29 @ X26 )
      | ~ ( zip_tseitin_0 @ X30 @ X29 @ X27 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X25 @ X24 ) ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('42',plain,(
    ! [X24: $i,X25: $i,X27: $i,X29: $i,X30: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X25 @ X24 ) ) ) )
      | ~ ( zip_tseitin_0 @ X30 @ X29 @ X27 @ X24 @ X25 )
      | ( r2_hidden @ X29 @ ( k1_tops_2 @ X25 @ X24 @ X27 ) )
      | ~ ( m1_subset_1 @ ( k1_tops_2 @ X25 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X25 @ X24 ) ) ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_C ) ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X1 @ ( k1_tops_2 @ sk_A @ sk_C @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X1 @ X0 @ sk_C @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['36','37'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_C ) ) )
      | ( r2_hidden @ X1 @ ( k1_tops_2 @ sk_A @ sk_C @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X1 @ X0 @ sk_C @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_C @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_2 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['39','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_C @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_2 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r2_hidden @ ( k3_xboole_0 @ sk_C @ sk_B ) @ ( k1_tops_2 @ sk_A @ sk_C @ sk_D ) )
    | ~ ( m1_subset_1 @ ( k3_xboole_0 @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','50'])).

thf('52',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('53',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('54',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('56',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['54','57'])).

thf('59',plain,(
    r2_hidden @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k1_tops_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['51','52','53','58'])).

thf('60',plain,(
    $false ),
    inference(demod,[status(thm)],['14','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WhtDYmM88I
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:49:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.01/1.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.01/1.21  % Solved by: fo/fo7.sh
% 1.01/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.01/1.21  % done 551 iterations in 0.752s
% 1.01/1.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.01/1.21  % SZS output start Refutation
% 1.01/1.21  thf(sk_B_type, type, sk_B: $i).
% 1.01/1.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.01/1.21  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 1.01/1.21  thf(sk_C_type, type, sk_C: $i).
% 1.01/1.21  thf(sk_A_type, type, sk_A: $i).
% 1.01/1.21  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.01/1.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.01/1.21  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.01/1.21  thf(sk_D_type, type, sk_D: $i).
% 1.01/1.21  thf(k1_tops_2_type, type, k1_tops_2: $i > $i > $i > $i).
% 1.01/1.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.01/1.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.01/1.21  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.01/1.21  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.01/1.21  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 1.01/1.21  thf(t41_tops_2, conjecture,
% 1.01/1.21    (![A:$i]:
% 1.01/1.21     ( ( l1_pre_topc @ A ) =>
% 1.01/1.21       ( ![B:$i]:
% 1.01/1.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.21           ( ![C:$i]:
% 1.01/1.21             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.21               ( ![D:$i]:
% 1.01/1.21                 ( ( m1_subset_1 @
% 1.01/1.21                     D @ 
% 1.01/1.21                     ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.01/1.21                   ( ( r2_hidden @ B @ D ) =>
% 1.01/1.21                     ( r2_hidden @
% 1.01/1.21                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 1.01/1.21                       ( k1_tops_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 1.01/1.21  thf(zf_stmt_0, negated_conjecture,
% 1.01/1.21    (~( ![A:$i]:
% 1.01/1.21        ( ( l1_pre_topc @ A ) =>
% 1.01/1.21          ( ![B:$i]:
% 1.01/1.21            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.21              ( ![C:$i]:
% 1.01/1.21                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.21                  ( ![D:$i]:
% 1.01/1.21                    ( ( m1_subset_1 @
% 1.01/1.21                        D @ 
% 1.01/1.21                        ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.01/1.21                      ( ( r2_hidden @ B @ D ) =>
% 1.01/1.21                        ( r2_hidden @
% 1.01/1.21                          ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 1.01/1.21                          ( k1_tops_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ) )),
% 1.01/1.21    inference('cnf.neg', [status(esa)], [t41_tops_2])).
% 1.01/1.21  thf('0', plain,
% 1.01/1.21      (~ (r2_hidden @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 1.01/1.21          (k1_tops_2 @ sk_A @ sk_C @ sk_D))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('1', plain,
% 1.01/1.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf(redefinition_k9_subset_1, axiom,
% 1.01/1.21    (![A:$i,B:$i,C:$i]:
% 1.01/1.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.01/1.21       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.01/1.21  thf('2', plain,
% 1.01/1.21      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.01/1.21         (((k9_subset_1 @ X7 @ X5 @ X6) = (k3_xboole_0 @ X5 @ X6))
% 1.01/1.21          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 1.01/1.21      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.01/1.21  thf('3', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 1.01/1.21           = (k3_xboole_0 @ X0 @ sk_B))),
% 1.01/1.21      inference('sup-', [status(thm)], ['1', '2'])).
% 1.01/1.21  thf('4', plain,
% 1.01/1.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf(commutativity_k9_subset_1, axiom,
% 1.01/1.21    (![A:$i,B:$i,C:$i]:
% 1.01/1.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.01/1.21       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 1.01/1.21  thf('5', plain,
% 1.01/1.21      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.01/1.21         (((k9_subset_1 @ X2 @ X4 @ X3) = (k9_subset_1 @ X2 @ X3 @ X4))
% 1.01/1.21          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 1.01/1.21      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 1.01/1.21  thf('6', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 1.01/1.21           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 1.01/1.21      inference('sup-', [status(thm)], ['4', '5'])).
% 1.01/1.21  thf('7', plain,
% 1.01/1.21      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 1.01/1.21         = (k3_xboole_0 @ sk_C @ sk_B))),
% 1.01/1.21      inference('sup+', [status(thm)], ['3', '6'])).
% 1.01/1.21  thf('8', plain,
% 1.01/1.21      (~ (r2_hidden @ (k3_xboole_0 @ sk_C @ sk_B) @ 
% 1.01/1.21          (k1_tops_2 @ sk_A @ sk_C @ sk_D))),
% 1.01/1.21      inference('demod', [status(thm)], ['0', '7'])).
% 1.01/1.21  thf('9', plain,
% 1.01/1.21      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 1.01/1.21         = (k3_xboole_0 @ sk_C @ sk_B))),
% 1.01/1.21      inference('sup+', [status(thm)], ['3', '6'])).
% 1.01/1.21  thf('10', plain,
% 1.01/1.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('11', plain,
% 1.01/1.21      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.01/1.21         (((k9_subset_1 @ X7 @ X5 @ X6) = (k3_xboole_0 @ X5 @ X6))
% 1.01/1.21          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 1.01/1.21      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.01/1.21  thf('12', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 1.01/1.21           = (k3_xboole_0 @ X0 @ sk_C))),
% 1.01/1.21      inference('sup-', [status(thm)], ['10', '11'])).
% 1.01/1.21  thf('13', plain,
% 1.01/1.21      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 1.01/1.21      inference('demod', [status(thm)], ['9', '12'])).
% 1.01/1.21  thf('14', plain,
% 1.01/1.21      (~ (r2_hidden @ (k3_xboole_0 @ sk_B @ sk_C) @ 
% 1.01/1.21          (k1_tops_2 @ sk_A @ sk_C @ sk_D))),
% 1.01/1.21      inference('demod', [status(thm)], ['8', '13'])).
% 1.01/1.21  thf('15', plain, ((r2_hidden @ sk_B @ sk_D)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('16', plain,
% 1.01/1.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf(d3_tops_2, axiom,
% 1.01/1.21    (![A:$i]:
% 1.01/1.21     ( ( l1_pre_topc @ A ) =>
% 1.01/1.21       ( ![B:$i]:
% 1.01/1.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.21           ( ![C:$i]:
% 1.01/1.21             ( ( m1_subset_1 @
% 1.01/1.21                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.01/1.21               ( ![D:$i]:
% 1.01/1.21                 ( ( m1_subset_1 @
% 1.01/1.21                     D @ 
% 1.01/1.21                     ( k1_zfmisc_1 @
% 1.01/1.21                       ( k1_zfmisc_1 @
% 1.01/1.21                         ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) =>
% 1.01/1.21                   ( ( ( D ) = ( k1_tops_2 @ A @ B @ C ) ) <=>
% 1.01/1.21                     ( ![E:$i]:
% 1.01/1.21                       ( ( m1_subset_1 @
% 1.01/1.21                           E @ 
% 1.01/1.21                           ( k1_zfmisc_1 @
% 1.01/1.21                             ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) =>
% 1.01/1.21                         ( ( r2_hidden @ E @ D ) <=>
% 1.01/1.21                           ( ?[F:$i]:
% 1.01/1.21                             ( ( m1_subset_1 @
% 1.01/1.21                                 F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 1.01/1.21                               ( r2_hidden @ F @ C ) & 
% 1.01/1.21                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ F @ B ) =
% 1.01/1.21                                 ( E ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.01/1.21  thf(zf_stmt_1, axiom,
% 1.01/1.21    (![F:$i,E:$i,C:$i,B:$i,A:$i]:
% 1.01/1.21     ( ( zip_tseitin_0 @ F @ E @ C @ B @ A ) <=>
% 1.01/1.21       ( ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ F @ B ) = ( E ) ) & 
% 1.01/1.21         ( r2_hidden @ F @ C ) & 
% 1.01/1.21         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 1.01/1.21  thf('17', plain,
% 1.01/1.21      (![X18 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.01/1.21         ((zip_tseitin_0 @ X20 @ X18 @ X22 @ X21 @ X23)
% 1.01/1.21          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 1.01/1.21          | ~ (r2_hidden @ X20 @ X22)
% 1.01/1.21          | ((k9_subset_1 @ (u1_struct_0 @ X23) @ X20 @ X21) != (X18)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.01/1.21  thf('18', plain,
% 1.01/1.21      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 1.01/1.21         (~ (r2_hidden @ X20 @ X22)
% 1.01/1.21          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 1.01/1.21          | (zip_tseitin_0 @ X20 @ 
% 1.01/1.21             (k9_subset_1 @ (u1_struct_0 @ X23) @ X20 @ X21) @ X22 @ X21 @ X23))),
% 1.01/1.21      inference('simplify', [status(thm)], ['17'])).
% 1.01/1.21  thf('19', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((zip_tseitin_0 @ sk_B @ 
% 1.01/1.21           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ X1 @ X0 @ sk_A)
% 1.01/1.21          | ~ (r2_hidden @ sk_B @ X1))),
% 1.01/1.21      inference('sup-', [status(thm)], ['16', '18'])).
% 1.01/1.21  thf('20', plain,
% 1.01/1.21      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('21', plain,
% 1.01/1.21      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.01/1.21         (((k9_subset_1 @ X2 @ X4 @ X3) = (k9_subset_1 @ X2 @ X3 @ X4))
% 1.01/1.21          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 1.01/1.21      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 1.01/1.21  thf('22', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 1.01/1.21           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 1.01/1.21      inference('sup-', [status(thm)], ['20', '21'])).
% 1.01/1.21  thf('23', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 1.01/1.21           = (k3_xboole_0 @ X0 @ sk_B))),
% 1.01/1.21      inference('sup-', [status(thm)], ['1', '2'])).
% 1.01/1.21  thf('24', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         ((k3_xboole_0 @ X0 @ sk_B)
% 1.01/1.21           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 1.01/1.21      inference('demod', [status(thm)], ['22', '23'])).
% 1.01/1.21  thf('25', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         ((zip_tseitin_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_B) @ X1 @ X0 @ sk_A)
% 1.01/1.21          | ~ (r2_hidden @ sk_B @ X1))),
% 1.01/1.21      inference('demod', [status(thm)], ['19', '24'])).
% 1.01/1.21  thf('26', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         (zip_tseitin_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_B) @ sk_D @ X0 @ sk_A)),
% 1.01/1.21      inference('sup-', [status(thm)], ['15', '25'])).
% 1.01/1.21  thf('27', plain,
% 1.01/1.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('28', plain,
% 1.01/1.21      ((m1_subset_1 @ sk_D @ 
% 1.01/1.21        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf(dt_k1_tops_2, axiom,
% 1.01/1.21    (![A:$i,B:$i,C:$i]:
% 1.01/1.21     ( ( ( l1_pre_topc @ A ) & 
% 1.01/1.21         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 1.01/1.21         ( m1_subset_1 @
% 1.01/1.21           C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 1.01/1.21       ( m1_subset_1 @
% 1.01/1.21         ( k1_tops_2 @ A @ B @ C ) @ 
% 1.01/1.21         ( k1_zfmisc_1 @
% 1.01/1.21           ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ))).
% 1.01/1.21  thf('29', plain,
% 1.01/1.21      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.01/1.21         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 1.01/1.21          | ~ (l1_pre_topc @ X32)
% 1.01/1.21          | ~ (m1_subset_1 @ X33 @ 
% 1.01/1.21               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32))))
% 1.01/1.21          | (m1_subset_1 @ (k1_tops_2 @ X32 @ X31 @ X33) @ 
% 1.01/1.21             (k1_zfmisc_1 @ 
% 1.01/1.21              (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X32 @ X31))))))),
% 1.01/1.21      inference('cnf', [status(esa)], [dt_k1_tops_2])).
% 1.01/1.21  thf('30', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         ((m1_subset_1 @ (k1_tops_2 @ sk_A @ X0 @ sk_D) @ 
% 1.01/1.21           (k1_zfmisc_1 @ 
% 1.01/1.21            (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)))))
% 1.01/1.21          | ~ (l1_pre_topc @ sk_A)
% 1.01/1.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.01/1.21      inference('sup-', [status(thm)], ['28', '29'])).
% 1.01/1.21  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('32', plain,
% 1.01/1.21      (![X0 : $i]:
% 1.01/1.21         ((m1_subset_1 @ (k1_tops_2 @ sk_A @ X0 @ sk_D) @ 
% 1.01/1.21           (k1_zfmisc_1 @ 
% 1.01/1.21            (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)))))
% 1.01/1.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.01/1.21      inference('demod', [status(thm)], ['30', '31'])).
% 1.01/1.21  thf('33', plain,
% 1.01/1.21      ((m1_subset_1 @ (k1_tops_2 @ sk_A @ sk_C @ sk_D) @ 
% 1.01/1.21        (k1_zfmisc_1 @ 
% 1.01/1.21         (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)))))),
% 1.01/1.21      inference('sup-', [status(thm)], ['27', '32'])).
% 1.01/1.21  thf('34', plain,
% 1.01/1.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf(t29_pre_topc, axiom,
% 1.01/1.21    (![A:$i]:
% 1.01/1.21     ( ( l1_pre_topc @ A ) =>
% 1.01/1.21       ( ![B:$i]:
% 1.01/1.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.21           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 1.01/1.21  thf('35', plain,
% 1.01/1.21      (![X16 : $i, X17 : $i]:
% 1.01/1.21         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.01/1.21          | ((u1_struct_0 @ (k1_pre_topc @ X17 @ X16)) = (X16))
% 1.01/1.21          | ~ (l1_pre_topc @ X17))),
% 1.01/1.21      inference('cnf', [status(esa)], [t29_pre_topc])).
% 1.01/1.21  thf('36', plain,
% 1.01/1.21      ((~ (l1_pre_topc @ sk_A)
% 1.01/1.21        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['34', '35'])).
% 1.01/1.21  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('38', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C))),
% 1.01/1.21      inference('demod', [status(thm)], ['36', '37'])).
% 1.01/1.21  thf('39', plain,
% 1.01/1.21      ((m1_subset_1 @ (k1_tops_2 @ sk_A @ sk_C @ sk_D) @ 
% 1.01/1.21        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_C)))),
% 1.01/1.21      inference('demod', [status(thm)], ['33', '38'])).
% 1.01/1.21  thf('40', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C))),
% 1.01/1.21      inference('demod', [status(thm)], ['36', '37'])).
% 1.01/1.21  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 1.01/1.21  thf(zf_stmt_3, axiom,
% 1.01/1.21    (![A:$i]:
% 1.01/1.21     ( ( l1_pre_topc @ A ) =>
% 1.01/1.21       ( ![B:$i]:
% 1.01/1.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.21           ( ![C:$i]:
% 1.01/1.21             ( ( m1_subset_1 @
% 1.01/1.21                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.01/1.21               ( ![D:$i]:
% 1.01/1.21                 ( ( m1_subset_1 @
% 1.01/1.21                     D @ 
% 1.01/1.21                     ( k1_zfmisc_1 @
% 1.01/1.21                       ( k1_zfmisc_1 @
% 1.01/1.21                         ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) =>
% 1.01/1.21                   ( ( ( D ) = ( k1_tops_2 @ A @ B @ C ) ) <=>
% 1.01/1.21                     ( ![E:$i]:
% 1.01/1.21                       ( ( m1_subset_1 @
% 1.01/1.21                           E @ 
% 1.01/1.21                           ( k1_zfmisc_1 @
% 1.01/1.21                             ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) =>
% 1.01/1.21                         ( ( r2_hidden @ E @ D ) <=>
% 1.01/1.21                           ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.01/1.21  thf('41', plain,
% 1.01/1.21      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X29 : $i, X30 : $i]:
% 1.01/1.21         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.01/1.21          | ~ (m1_subset_1 @ X26 @ 
% 1.01/1.21               (k1_zfmisc_1 @ 
% 1.01/1.21                (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X25 @ X24)))))
% 1.01/1.21          | ((X26) != (k1_tops_2 @ X25 @ X24 @ X27))
% 1.01/1.21          | (r2_hidden @ X29 @ X26)
% 1.01/1.21          | ~ (zip_tseitin_0 @ X30 @ X29 @ X27 @ X24 @ X25)
% 1.01/1.21          | ~ (m1_subset_1 @ X29 @ 
% 1.01/1.21               (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X25 @ X24))))
% 1.01/1.21          | ~ (m1_subset_1 @ X27 @ 
% 1.01/1.21               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25))))
% 1.01/1.21          | ~ (l1_pre_topc @ X25))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.01/1.21  thf('42', plain,
% 1.01/1.21      (![X24 : $i, X25 : $i, X27 : $i, X29 : $i, X30 : $i]:
% 1.01/1.21         (~ (l1_pre_topc @ X25)
% 1.01/1.21          | ~ (m1_subset_1 @ X27 @ 
% 1.01/1.21               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25))))
% 1.01/1.21          | ~ (m1_subset_1 @ X29 @ 
% 1.01/1.21               (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X25 @ X24))))
% 1.01/1.21          | ~ (zip_tseitin_0 @ X30 @ X29 @ X27 @ X24 @ X25)
% 1.01/1.21          | (r2_hidden @ X29 @ (k1_tops_2 @ X25 @ X24 @ X27))
% 1.01/1.21          | ~ (m1_subset_1 @ (k1_tops_2 @ X25 @ X24 @ X27) @ 
% 1.01/1.21               (k1_zfmisc_1 @ 
% 1.01/1.21                (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X25 @ X24)))))
% 1.01/1.21          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25))))),
% 1.01/1.21      inference('simplify', [status(thm)], ['41'])).
% 1.01/1.21  thf('43', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.21         (~ (m1_subset_1 @ (k1_tops_2 @ sk_A @ sk_C @ X0) @ 
% 1.01/1.21             (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_C)))
% 1.01/1.21          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.21          | (r2_hidden @ X1 @ (k1_tops_2 @ sk_A @ sk_C @ X0))
% 1.01/1.21          | ~ (zip_tseitin_0 @ X2 @ X1 @ X0 @ sk_C @ sk_A)
% 1.01/1.21          | ~ (m1_subset_1 @ X1 @ 
% 1.01/1.21               (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C))))
% 1.01/1.21          | ~ (m1_subset_1 @ X0 @ 
% 1.01/1.21               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.01/1.21          | ~ (l1_pre_topc @ sk_A))),
% 1.01/1.21      inference('sup-', [status(thm)], ['40', '42'])).
% 1.01/1.21  thf('44', plain,
% 1.01/1.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('45', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C))),
% 1.01/1.21      inference('demod', [status(thm)], ['36', '37'])).
% 1.01/1.21  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('47', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.21         (~ (m1_subset_1 @ (k1_tops_2 @ sk_A @ sk_C @ X0) @ 
% 1.01/1.21             (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_C)))
% 1.01/1.21          | (r2_hidden @ X1 @ (k1_tops_2 @ sk_A @ sk_C @ X0))
% 1.01/1.21          | ~ (zip_tseitin_0 @ X2 @ X1 @ X0 @ sk_C @ sk_A)
% 1.01/1.21          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ sk_C))
% 1.01/1.21          | ~ (m1_subset_1 @ X0 @ 
% 1.01/1.21               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.01/1.21      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 1.01/1.21  thf('48', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (~ (m1_subset_1 @ sk_D @ 
% 1.01/1.21             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.01/1.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_C))
% 1.01/1.21          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_C @ sk_A)
% 1.01/1.21          | (r2_hidden @ X0 @ (k1_tops_2 @ sk_A @ sk_C @ sk_D)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['39', '47'])).
% 1.01/1.21  thf('49', plain,
% 1.01/1.21      ((m1_subset_1 @ sk_D @ 
% 1.01/1.21        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.01/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.21  thf('50', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_C))
% 1.01/1.21          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_C @ sk_A)
% 1.01/1.21          | (r2_hidden @ X0 @ (k1_tops_2 @ sk_A @ sk_C @ sk_D)))),
% 1.01/1.21      inference('demod', [status(thm)], ['48', '49'])).
% 1.01/1.21  thf('51', plain,
% 1.01/1.21      (((r2_hidden @ (k3_xboole_0 @ sk_C @ sk_B) @ 
% 1.01/1.21         (k1_tops_2 @ sk_A @ sk_C @ sk_D))
% 1.01/1.21        | ~ (m1_subset_1 @ (k3_xboole_0 @ sk_C @ sk_B) @ (k1_zfmisc_1 @ sk_C)))),
% 1.01/1.21      inference('sup-', [status(thm)], ['26', '50'])).
% 1.01/1.21  thf('52', plain,
% 1.01/1.21      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 1.01/1.21      inference('demod', [status(thm)], ['9', '12'])).
% 1.01/1.21  thf('53', plain,
% 1.01/1.21      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 1.01/1.21      inference('demod', [status(thm)], ['9', '12'])).
% 1.01/1.21  thf('54', plain,
% 1.01/1.21      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 1.01/1.21      inference('demod', [status(thm)], ['9', '12'])).
% 1.01/1.21  thf(t17_xboole_1, axiom,
% 1.01/1.21    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.01/1.21  thf('55', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 1.01/1.21      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.01/1.21  thf(t3_subset, axiom,
% 1.01/1.21    (![A:$i,B:$i]:
% 1.01/1.21     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.01/1.21  thf('56', plain,
% 1.01/1.21      (![X10 : $i, X12 : $i]:
% 1.01/1.21         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 1.01/1.21      inference('cnf', [status(esa)], [t3_subset])).
% 1.01/1.21  thf('57', plain,
% 1.01/1.21      (![X0 : $i, X1 : $i]:
% 1.01/1.21         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.01/1.21      inference('sup-', [status(thm)], ['55', '56'])).
% 1.01/1.21  thf('58', plain,
% 1.01/1.21      ((m1_subset_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_C))),
% 1.01/1.21      inference('sup+', [status(thm)], ['54', '57'])).
% 1.01/1.21  thf('59', plain,
% 1.01/1.21      ((r2_hidden @ (k3_xboole_0 @ sk_B @ sk_C) @ 
% 1.01/1.21        (k1_tops_2 @ sk_A @ sk_C @ sk_D))),
% 1.01/1.21      inference('demod', [status(thm)], ['51', '52', '53', '58'])).
% 1.01/1.21  thf('60', plain, ($false), inference('demod', [status(thm)], ['14', '59'])).
% 1.01/1.21  
% 1.01/1.21  % SZS output end Refutation
% 1.01/1.21  
% 1.05/1.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
