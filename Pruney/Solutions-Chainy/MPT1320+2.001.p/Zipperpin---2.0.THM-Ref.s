%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zZYREPmQmz

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:38 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 125 expanded)
%              Number of leaves         :   29 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :  812 (1923 expanded)
%              Number of equality atoms :   23 (  32 expanded)
%              Maximal formula depth    :   21 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_2_type,type,(
    k1_tops_2: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k9_subset_1 @ X6 @ X4 @ X5 )
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r2_hidden @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k1_tops_2 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('6',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X17: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X19 @ X17 @ X21 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( r2_hidden @ X19 @ X21 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X22 ) @ X19 @ X20 )
       != X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('9',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( zip_tseitin_0 @ X19 @ ( k9_subset_1 @ ( u1_struct_0 @ X22 ) @ X19 @ X20 ) @ X21 @ X20 @ X22 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ X1 @ X0 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_D @ X0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    zip_tseitin_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_D @ sk_C @ sk_A ),
    inference('sup+',[status(thm)],['5','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) ) )
      | ( m1_subset_1 @ ( k1_tops_2 @ X31 @ X30 @ X32 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X31 @ X30 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_2])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ ( k1_tops_2 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X16 @ X15 ) )
        = X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('22',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ ( k1_tops_2 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('26',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['22','23'])).

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

thf('27',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X24 @ X23 ) ) ) ) )
      | ( X25
       != ( k1_tops_2 @ X24 @ X23 @ X26 ) )
      | ( r2_hidden @ X28 @ X25 )
      | ~ ( zip_tseitin_0 @ X29 @ X28 @ X26 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X24 @ X23 ) ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('28',plain,(
    ! [X23: $i,X24: $i,X26: $i,X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X24 @ X23 ) ) ) )
      | ~ ( zip_tseitin_0 @ X29 @ X28 @ X26 @ X23 @ X24 )
      | ( r2_hidden @ X28 @ ( k1_tops_2 @ X24 @ X23 @ X26 ) )
      | ~ ( m1_subset_1 @ ( k1_tops_2 @ X24 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X24 @ X23 ) ) ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_C ) ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X1 @ ( k1_tops_2 @ sk_A @ sk_C @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X1 @ X0 @ sk_C @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['22','23'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_C ) ) )
      | ( r2_hidden @ X1 @ ( k1_tops_2 @ sk_A @ sk_C @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X1 @ X0 @ sk_C @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_C @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_2 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_C ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_C @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_2 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r2_hidden @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k1_tops_2 @ sk_A @ sk_C @ sk_D ) )
    | ~ ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','36'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X3 @ X2 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('45',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r2_hidden @ ( k3_xboole_0 @ sk_B @ sk_C ) @ ( k1_tops_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['37','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['4','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zZYREPmQmz
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:24:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.74/0.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.74/0.93  % Solved by: fo/fo7.sh
% 0.74/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.93  % done 666 iterations in 0.487s
% 0.74/0.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.74/0.93  % SZS output start Refutation
% 0.74/0.93  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.74/0.93  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.74/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.93  thf(sk_D_type, type, sk_D: $i).
% 0.74/0.93  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.74/0.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.74/0.93  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.74/0.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.74/0.93  thf(sk_C_type, type, sk_C: $i).
% 0.74/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.74/0.93  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.74/0.93  thf(k1_tops_2_type, type, k1_tops_2: $i > $i > $i > $i).
% 0.74/0.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.74/0.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.74/0.93  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.74/0.93  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.74/0.93  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.74/0.93  thf(t41_tops_2, conjecture,
% 0.74/0.93    (![A:$i]:
% 0.74/0.93     ( ( l1_pre_topc @ A ) =>
% 0.74/0.93       ( ![B:$i]:
% 0.74/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.74/0.93           ( ![C:$i]:
% 0.74/0.93             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.74/0.93               ( ![D:$i]:
% 0.74/0.93                 ( ( m1_subset_1 @
% 0.74/0.93                     D @ 
% 0.74/0.93                     ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.74/0.93                   ( ( r2_hidden @ B @ D ) =>
% 0.74/0.93                     ( r2_hidden @
% 0.74/0.93                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.74/0.93                       ( k1_tops_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.74/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.93    (~( ![A:$i]:
% 0.74/0.93        ( ( l1_pre_topc @ A ) =>
% 0.74/0.93          ( ![B:$i]:
% 0.74/0.93            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.74/0.93              ( ![C:$i]:
% 0.74/0.93                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.74/0.93                  ( ![D:$i]:
% 0.74/0.93                    ( ( m1_subset_1 @
% 0.74/0.93                        D @ 
% 0.74/0.93                        ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.74/0.93                      ( ( r2_hidden @ B @ D ) =>
% 0.74/0.93                        ( r2_hidden @
% 0.74/0.93                          ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.74/0.93                          ( k1_tops_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ) )),
% 0.74/0.93    inference('cnf.neg', [status(esa)], [t41_tops_2])).
% 0.74/0.93  thf('0', plain,
% 0.74/0.93      (~ (r2_hidden @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.74/0.93          (k1_tops_2 @ sk_A @ sk_C @ sk_D))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('1', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(redefinition_k9_subset_1, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i]:
% 0.74/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.74/0.93       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.74/0.93  thf('2', plain,
% 0.74/0.93      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.74/0.93         (((k9_subset_1 @ X6 @ X4 @ X5) = (k3_xboole_0 @ X4 @ X5))
% 0.74/0.93          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.74/0.93      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.74/0.93  thf('3', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.74/0.93           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.74/0.93      inference('sup-', [status(thm)], ['1', '2'])).
% 0.74/0.93  thf('4', plain,
% 0.74/0.93      (~ (r2_hidden @ (k3_xboole_0 @ sk_B @ sk_C) @ 
% 0.74/0.93          (k1_tops_2 @ sk_A @ sk_C @ sk_D))),
% 0.74/0.93      inference('demod', [status(thm)], ['0', '3'])).
% 0.74/0.93  thf('5', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.74/0.93           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.74/0.93      inference('sup-', [status(thm)], ['1', '2'])).
% 0.74/0.93  thf('6', plain, ((r2_hidden @ sk_B @ sk_D)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('7', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(d3_tops_2, axiom,
% 0.74/0.93    (![A:$i]:
% 0.74/0.93     ( ( l1_pre_topc @ A ) =>
% 0.74/0.93       ( ![B:$i]:
% 0.74/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.74/0.93           ( ![C:$i]:
% 0.74/0.93             ( ( m1_subset_1 @
% 0.74/0.93                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.74/0.93               ( ![D:$i]:
% 0.74/0.93                 ( ( m1_subset_1 @
% 0.74/0.93                     D @ 
% 0.74/0.93                     ( k1_zfmisc_1 @
% 0.74/0.93                       ( k1_zfmisc_1 @
% 0.74/0.93                         ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) =>
% 0.74/0.93                   ( ( ( D ) = ( k1_tops_2 @ A @ B @ C ) ) <=>
% 0.74/0.93                     ( ![E:$i]:
% 0.74/0.93                       ( ( m1_subset_1 @
% 0.74/0.93                           E @ 
% 0.74/0.93                           ( k1_zfmisc_1 @
% 0.74/0.93                             ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) =>
% 0.74/0.93                         ( ( r2_hidden @ E @ D ) <=>
% 0.74/0.93                           ( ?[F:$i]:
% 0.74/0.93                             ( ( m1_subset_1 @
% 0.74/0.93                                 F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.74/0.93                               ( r2_hidden @ F @ C ) & 
% 0.74/0.93                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ F @ B ) =
% 0.74/0.93                                 ( E ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.74/0.93  thf(zf_stmt_1, axiom,
% 0.74/0.93    (![F:$i,E:$i,C:$i,B:$i,A:$i]:
% 0.74/0.93     ( ( zip_tseitin_0 @ F @ E @ C @ B @ A ) <=>
% 0.74/0.93       ( ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ F @ B ) = ( E ) ) & 
% 0.74/0.93         ( r2_hidden @ F @ C ) & 
% 0.74/0.93         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.74/0.93  thf('8', plain,
% 0.74/0.93      (![X17 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.74/0.93         ((zip_tseitin_0 @ X19 @ X17 @ X21 @ X20 @ X22)
% 0.74/0.93          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.74/0.93          | ~ (r2_hidden @ X19 @ X21)
% 0.74/0.93          | ((k9_subset_1 @ (u1_struct_0 @ X22) @ X19 @ X20) != (X17)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.74/0.93  thf('9', plain,
% 0.74/0.93      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.74/0.93         (~ (r2_hidden @ X19 @ X21)
% 0.74/0.93          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.74/0.93          | (zip_tseitin_0 @ X19 @ 
% 0.74/0.93             (k9_subset_1 @ (u1_struct_0 @ X22) @ X19 @ X20) @ X21 @ X20 @ X22))),
% 0.74/0.93      inference('simplify', [status(thm)], ['8'])).
% 0.74/0.93  thf('10', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((zip_tseitin_0 @ sk_B @ 
% 0.74/0.93           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ X1 @ X0 @ sk_A)
% 0.74/0.93          | ~ (r2_hidden @ sk_B @ X1))),
% 0.74/0.93      inference('sup-', [status(thm)], ['7', '9'])).
% 0.74/0.93  thf('11', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         (zip_tseitin_0 @ sk_B @ 
% 0.74/0.93          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ sk_D @ X0 @ sk_A)),
% 0.74/0.93      inference('sup-', [status(thm)], ['6', '10'])).
% 0.74/0.93  thf('12', plain,
% 0.74/0.93      ((zip_tseitin_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_D @ sk_C @ sk_A)),
% 0.74/0.93      inference('sup+', [status(thm)], ['5', '11'])).
% 0.74/0.93  thf('13', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('14', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_D @ 
% 0.74/0.93        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(dt_k1_tops_2, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i]:
% 0.74/0.93     ( ( ( l1_pre_topc @ A ) & 
% 0.74/0.93         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.74/0.93         ( m1_subset_1 @
% 0.74/0.93           C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.74/0.93       ( m1_subset_1 @
% 0.74/0.93         ( k1_tops_2 @ A @ B @ C ) @ 
% 0.74/0.93         ( k1_zfmisc_1 @
% 0.74/0.93           ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ))).
% 0.74/0.93  thf('15', plain,
% 0.74/0.93      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.74/0.93         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.74/0.93          | ~ (l1_pre_topc @ X31)
% 0.74/0.93          | ~ (m1_subset_1 @ X32 @ 
% 0.74/0.93               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31))))
% 0.74/0.93          | (m1_subset_1 @ (k1_tops_2 @ X31 @ X30 @ X32) @ 
% 0.74/0.93             (k1_zfmisc_1 @ 
% 0.74/0.93              (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X31 @ X30))))))),
% 0.74/0.93      inference('cnf', [status(esa)], [dt_k1_tops_2])).
% 0.74/0.93  thf('16', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         ((m1_subset_1 @ (k1_tops_2 @ sk_A @ X0 @ sk_D) @ 
% 0.74/0.93           (k1_zfmisc_1 @ 
% 0.74/0.93            (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)))))
% 0.74/0.93          | ~ (l1_pre_topc @ sk_A)
% 0.74/0.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['14', '15'])).
% 0.74/0.93  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('18', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         ((m1_subset_1 @ (k1_tops_2 @ sk_A @ X0 @ sk_D) @ 
% 0.74/0.93           (k1_zfmisc_1 @ 
% 0.74/0.93            (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)))))
% 0.74/0.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.74/0.93      inference('demod', [status(thm)], ['16', '17'])).
% 0.74/0.93  thf('19', plain,
% 0.74/0.93      ((m1_subset_1 @ (k1_tops_2 @ sk_A @ sk_C @ sk_D) @ 
% 0.74/0.93        (k1_zfmisc_1 @ 
% 0.74/0.93         (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['13', '18'])).
% 0.74/0.93  thf('20', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(t29_pre_topc, axiom,
% 0.74/0.93    (![A:$i]:
% 0.74/0.93     ( ( l1_pre_topc @ A ) =>
% 0.74/0.93       ( ![B:$i]:
% 0.74/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.74/0.93           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 0.74/0.93  thf('21', plain,
% 0.74/0.93      (![X15 : $i, X16 : $i]:
% 0.74/0.93         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.74/0.93          | ((u1_struct_0 @ (k1_pre_topc @ X16 @ X15)) = (X15))
% 0.74/0.93          | ~ (l1_pre_topc @ X16))),
% 0.74/0.93      inference('cnf', [status(esa)], [t29_pre_topc])).
% 0.74/0.93  thf('22', plain,
% 0.74/0.93      ((~ (l1_pre_topc @ sk_A)
% 0.74/0.93        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['20', '21'])).
% 0.74/0.93  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('24', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C))),
% 0.74/0.93      inference('demod', [status(thm)], ['22', '23'])).
% 0.74/0.93  thf('25', plain,
% 0.74/0.93      ((m1_subset_1 @ (k1_tops_2 @ sk_A @ sk_C @ sk_D) @ 
% 0.74/0.93        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_C)))),
% 0.74/0.93      inference('demod', [status(thm)], ['19', '24'])).
% 0.74/0.93  thf('26', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C))),
% 0.74/0.93      inference('demod', [status(thm)], ['22', '23'])).
% 0.74/0.93  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.74/0.93  thf(zf_stmt_3, axiom,
% 0.74/0.93    (![A:$i]:
% 0.74/0.93     ( ( l1_pre_topc @ A ) =>
% 0.74/0.93       ( ![B:$i]:
% 0.74/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.74/0.93           ( ![C:$i]:
% 0.74/0.93             ( ( m1_subset_1 @
% 0.74/0.93                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.74/0.93               ( ![D:$i]:
% 0.74/0.93                 ( ( m1_subset_1 @
% 0.74/0.93                     D @ 
% 0.74/0.93                     ( k1_zfmisc_1 @
% 0.74/0.93                       ( k1_zfmisc_1 @
% 0.74/0.93                         ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) =>
% 0.74/0.93                   ( ( ( D ) = ( k1_tops_2 @ A @ B @ C ) ) <=>
% 0.74/0.93                     ( ![E:$i]:
% 0.74/0.93                       ( ( m1_subset_1 @
% 0.74/0.93                           E @ 
% 0.74/0.93                           ( k1_zfmisc_1 @
% 0.74/0.93                             ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) =>
% 0.74/0.93                         ( ( r2_hidden @ E @ D ) <=>
% 0.74/0.93                           ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.74/0.93  thf('27', plain,
% 0.74/0.93      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X28 : $i, X29 : $i]:
% 0.74/0.93         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.74/0.93          | ~ (m1_subset_1 @ X25 @ 
% 0.74/0.93               (k1_zfmisc_1 @ 
% 0.74/0.93                (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X24 @ X23)))))
% 0.74/0.93          | ((X25) != (k1_tops_2 @ X24 @ X23 @ X26))
% 0.74/0.93          | (r2_hidden @ X28 @ X25)
% 0.74/0.93          | ~ (zip_tseitin_0 @ X29 @ X28 @ X26 @ X23 @ X24)
% 0.74/0.93          | ~ (m1_subset_1 @ X28 @ 
% 0.74/0.93               (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X24 @ X23))))
% 0.74/0.93          | ~ (m1_subset_1 @ X26 @ 
% 0.74/0.93               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24))))
% 0.74/0.93          | ~ (l1_pre_topc @ X24))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.74/0.93  thf('28', plain,
% 0.74/0.93      (![X23 : $i, X24 : $i, X26 : $i, X28 : $i, X29 : $i]:
% 0.74/0.93         (~ (l1_pre_topc @ X24)
% 0.74/0.93          | ~ (m1_subset_1 @ X26 @ 
% 0.74/0.93               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24))))
% 0.74/0.93          | ~ (m1_subset_1 @ X28 @ 
% 0.74/0.93               (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X24 @ X23))))
% 0.74/0.93          | ~ (zip_tseitin_0 @ X29 @ X28 @ X26 @ X23 @ X24)
% 0.74/0.93          | (r2_hidden @ X28 @ (k1_tops_2 @ X24 @ X23 @ X26))
% 0.74/0.93          | ~ (m1_subset_1 @ (k1_tops_2 @ X24 @ X23 @ X26) @ 
% 0.74/0.93               (k1_zfmisc_1 @ 
% 0.74/0.93                (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X24 @ X23)))))
% 0.74/0.93          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24))))),
% 0.74/0.93      inference('simplify', [status(thm)], ['27'])).
% 0.74/0.93  thf('29', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.93         (~ (m1_subset_1 @ (k1_tops_2 @ sk_A @ sk_C @ X0) @ 
% 0.74/0.93             (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_C)))
% 0.74/0.93          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.74/0.93          | (r2_hidden @ X1 @ (k1_tops_2 @ sk_A @ sk_C @ X0))
% 0.74/0.93          | ~ (zip_tseitin_0 @ X2 @ X1 @ X0 @ sk_C @ sk_A)
% 0.74/0.93          | ~ (m1_subset_1 @ X1 @ 
% 0.74/0.93               (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C))))
% 0.74/0.93          | ~ (m1_subset_1 @ X0 @ 
% 0.74/0.93               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.74/0.93          | ~ (l1_pre_topc @ sk_A))),
% 0.74/0.93      inference('sup-', [status(thm)], ['26', '28'])).
% 0.74/0.93  thf('30', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('31', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C))),
% 0.74/0.93      inference('demod', [status(thm)], ['22', '23'])).
% 0.74/0.93  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('33', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.93         (~ (m1_subset_1 @ (k1_tops_2 @ sk_A @ sk_C @ X0) @ 
% 0.74/0.93             (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_C)))
% 0.74/0.93          | (r2_hidden @ X1 @ (k1_tops_2 @ sk_A @ sk_C @ X0))
% 0.74/0.93          | ~ (zip_tseitin_0 @ X2 @ X1 @ X0 @ sk_C @ sk_A)
% 0.74/0.93          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ sk_C))
% 0.74/0.93          | ~ (m1_subset_1 @ X0 @ 
% 0.74/0.93               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.74/0.93      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.74/0.93  thf('34', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         (~ (m1_subset_1 @ sk_D @ 
% 0.74/0.93             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.74/0.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_C))
% 0.74/0.93          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_C @ sk_A)
% 0.74/0.93          | (r2_hidden @ X0 @ (k1_tops_2 @ sk_A @ sk_C @ sk_D)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['25', '33'])).
% 0.74/0.93  thf('35', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_D @ 
% 0.74/0.93        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('36', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_C))
% 0.74/0.93          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_C @ sk_A)
% 0.74/0.93          | (r2_hidden @ X0 @ (k1_tops_2 @ sk_A @ sk_C @ sk_D)))),
% 0.74/0.93      inference('demod', [status(thm)], ['34', '35'])).
% 0.74/0.93  thf('37', plain,
% 0.74/0.93      (((r2_hidden @ (k3_xboole_0 @ sk_B @ sk_C) @ 
% 0.74/0.93         (k1_tops_2 @ sk_A @ sk_C @ sk_D))
% 0.74/0.93        | ~ (m1_subset_1 @ (k3_xboole_0 @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_C)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['12', '36'])).
% 0.74/0.93  thf(commutativity_k2_tarski, axiom,
% 0.74/0.93    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.74/0.93  thf('38', plain,
% 0.74/0.93      (![X2 : $i, X3 : $i]: ((k2_tarski @ X3 @ X2) = (k2_tarski @ X2 @ X3))),
% 0.74/0.93      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.74/0.93  thf(t12_setfam_1, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.74/0.93  thf('39', plain,
% 0.74/0.93      (![X7 : $i, X8 : $i]:
% 0.74/0.93         ((k1_setfam_1 @ (k2_tarski @ X7 @ X8)) = (k3_xboole_0 @ X7 @ X8))),
% 0.74/0.93      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.74/0.93  thf('40', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.74/0.93      inference('sup+', [status(thm)], ['38', '39'])).
% 0.74/0.93  thf('41', plain,
% 0.74/0.93      (![X7 : $i, X8 : $i]:
% 0.74/0.93         ((k1_setfam_1 @ (k2_tarski @ X7 @ X8)) = (k3_xboole_0 @ X7 @ X8))),
% 0.74/0.93      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.74/0.93  thf('42', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.74/0.93      inference('sup+', [status(thm)], ['40', '41'])).
% 0.74/0.93  thf(t17_xboole_1, axiom,
% 0.74/0.93    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.74/0.93  thf('43', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.74/0.93      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.74/0.93  thf('44', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.74/0.93      inference('sup+', [status(thm)], ['42', '43'])).
% 0.74/0.93  thf(t3_subset, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.74/0.93  thf('45', plain,
% 0.74/0.93      (![X9 : $i, X11 : $i]:
% 0.74/0.93         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.74/0.93      inference('cnf', [status(esa)], [t3_subset])).
% 0.74/0.93  thf('46', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i]:
% 0.74/0.93         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['44', '45'])).
% 0.74/0.93  thf('47', plain,
% 0.74/0.93      ((r2_hidden @ (k3_xboole_0 @ sk_B @ sk_C) @ 
% 0.74/0.93        (k1_tops_2 @ sk_A @ sk_C @ sk_D))),
% 0.74/0.93      inference('demod', [status(thm)], ['37', '46'])).
% 0.74/0.93  thf('48', plain, ($false), inference('demod', [status(thm)], ['4', '47'])).
% 0.74/0.93  
% 0.74/0.93  % SZS output end Refutation
% 0.74/0.93  
% 0.74/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
