%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7U5hSLoHu5

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:39 EST 2020

% Result     : Theorem 17.93s
% Output     : Refutation 17.93s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 140 expanded)
%              Number of leaves         :   27 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :  840 (2112 expanded)
%              Number of equality atoms :   19 (  30 expanded)
%              Maximal formula depth    :   21 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tops_2_type,type,(
    k1_tops_2: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ~ ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_tops_2 @ sk_A @ sk_C_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k9_subset_1 @ X9 @ X7 @ X8 )
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 )
      = ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r2_hidden @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ ( k1_tops_2 @ sk_A @ sk_C_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
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

thf('7',plain,(
    ! [X20: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X22 @ X20 @ X24 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( r2_hidden @ X22 @ X24 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X25 ) @ X22 @ X23 )
       != X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( zip_tseitin_0 @ X22 @ ( k9_subset_1 @ ( u1_struct_0 @ X25 ) @ X22 @ X23 ) @ X24 @ X23 @ X25 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ X1 @ X0 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_D @ X0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) ) )
      | ( m1_subset_1 @ ( k1_tops_2 @ X34 @ X33 @ X35 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X34 @ X33 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_2])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( k1_tops_2 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('19',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X19 @ X18 ) )
        = X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ ( k1_tops_2 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

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

thf('25',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X27 @ X26 ) ) ) ) )
      | ( X28
       != ( k1_tops_2 @ X27 @ X26 @ X29 ) )
      | ( r2_hidden @ X31 @ X28 )
      | ~ ( zip_tseitin_0 @ X32 @ X31 @ X29 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X27 @ X26 ) ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('26',plain,(
    ! [X26: $i,X27: $i,X29: $i,X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X27 @ X26 ) ) ) )
      | ~ ( zip_tseitin_0 @ X32 @ X31 @ X29 @ X26 @ X27 )
      | ( r2_hidden @ X31 @ ( k1_tops_2 @ X27 @ X26 @ X29 ) )
      | ~ ( m1_subset_1 @ ( k1_tops_2 @ X27 @ X26 @ X29 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X27 @ X26 ) ) ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X1 @ ( k1_tops_2 @ sk_A @ sk_C_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X1 @ X0 @ sk_C_1 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['20','21'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_C_1 ) ) )
      | ( r2_hidden @ X1 @ ( k1_tops_2 @ sk_A @ sk_C_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X1 @ X0 @ sk_C_1 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_C_1 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_2 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['23','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_C_1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_C_1 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_2 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_tops_2 @ sk_A @ sk_C_1 @ sk_D ) )
    | ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 )
      = ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 )
      = ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('38',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('42',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('44',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X4 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('47',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k9_subset_1 @ X9 @ X7 @ X8 )
        = ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    r2_hidden @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ ( k1_tops_2 @ sk_A @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['35','36','37','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['4','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7U5hSLoHu5
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:01:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 17.93/18.17  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 17.93/18.17  % Solved by: fo/fo7.sh
% 17.93/18.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.93/18.17  % done 2870 iterations in 17.705s
% 17.93/18.17  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 17.93/18.17  % SZS output start Refutation
% 17.93/18.17  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 17.93/18.17  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 17.93/18.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 17.93/18.17  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 17.93/18.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 17.93/18.17  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 17.93/18.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 17.93/18.17  thf(sk_D_type, type, sk_D: $i).
% 17.93/18.17  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 17.93/18.17  thf(sk_C_1_type, type, sk_C_1: $i).
% 17.93/18.17  thf(k1_tops_2_type, type, k1_tops_2: $i > $i > $i > $i).
% 17.93/18.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 17.93/18.17  thf(sk_A_type, type, sk_A: $i).
% 17.93/18.17  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 17.93/18.17  thf(sk_B_type, type, sk_B: $i).
% 17.93/18.17  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 17.93/18.17  thf(t41_tops_2, conjecture,
% 17.93/18.17    (![A:$i]:
% 17.93/18.17     ( ( l1_pre_topc @ A ) =>
% 17.93/18.17       ( ![B:$i]:
% 17.93/18.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.93/18.17           ( ![C:$i]:
% 17.93/18.17             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.93/18.17               ( ![D:$i]:
% 17.93/18.17                 ( ( m1_subset_1 @
% 17.93/18.17                     D @ 
% 17.93/18.17                     ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 17.93/18.17                   ( ( r2_hidden @ B @ D ) =>
% 17.93/18.17                     ( r2_hidden @
% 17.93/18.17                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 17.93/18.17                       ( k1_tops_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 17.93/18.17  thf(zf_stmt_0, negated_conjecture,
% 17.93/18.17    (~( ![A:$i]:
% 17.93/18.17        ( ( l1_pre_topc @ A ) =>
% 17.93/18.17          ( ![B:$i]:
% 17.93/18.17            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.93/18.17              ( ![C:$i]:
% 17.93/18.17                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.93/18.17                  ( ![D:$i]:
% 17.93/18.17                    ( ( m1_subset_1 @
% 17.93/18.17                        D @ 
% 17.93/18.17                        ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 17.93/18.17                      ( ( r2_hidden @ B @ D ) =>
% 17.93/18.17                        ( r2_hidden @
% 17.93/18.17                          ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 17.93/18.17                          ( k1_tops_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ) )),
% 17.93/18.17    inference('cnf.neg', [status(esa)], [t41_tops_2])).
% 17.93/18.17  thf('0', plain,
% 17.93/18.17      (~ (r2_hidden @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C_1) @ 
% 17.93/18.17          (k1_tops_2 @ sk_A @ sk_C_1 @ sk_D))),
% 17.93/18.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.93/18.17  thf('1', plain,
% 17.93/18.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.93/18.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.93/18.17  thf(redefinition_k9_subset_1, axiom,
% 17.93/18.17    (![A:$i,B:$i,C:$i]:
% 17.93/18.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 17.93/18.17       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 17.93/18.17  thf('2', plain,
% 17.93/18.17      (![X7 : $i, X8 : $i, X9 : $i]:
% 17.93/18.17         (((k9_subset_1 @ X9 @ X7 @ X8) = (k3_xboole_0 @ X7 @ X8))
% 17.93/18.17          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 17.93/18.17      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 17.93/18.17  thf('3', plain,
% 17.93/18.17      (![X0 : $i]:
% 17.93/18.17         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1)
% 17.93/18.17           = (k3_xboole_0 @ X0 @ sk_C_1))),
% 17.93/18.17      inference('sup-', [status(thm)], ['1', '2'])).
% 17.93/18.17  thf('4', plain,
% 17.93/18.17      (~ (r2_hidden @ (k3_xboole_0 @ sk_B @ sk_C_1) @ 
% 17.93/18.17          (k1_tops_2 @ sk_A @ sk_C_1 @ sk_D))),
% 17.93/18.17      inference('demod', [status(thm)], ['0', '3'])).
% 17.93/18.17  thf('5', plain, ((r2_hidden @ sk_B @ sk_D)),
% 17.93/18.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.93/18.17  thf('6', plain,
% 17.93/18.17      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.93/18.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.93/18.17  thf(d3_tops_2, axiom,
% 17.93/18.17    (![A:$i]:
% 17.93/18.17     ( ( l1_pre_topc @ A ) =>
% 17.93/18.17       ( ![B:$i]:
% 17.93/18.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.93/18.17           ( ![C:$i]:
% 17.93/18.17             ( ( m1_subset_1 @
% 17.93/18.17                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 17.93/18.17               ( ![D:$i]:
% 17.93/18.17                 ( ( m1_subset_1 @
% 17.93/18.17                     D @ 
% 17.93/18.17                     ( k1_zfmisc_1 @
% 17.93/18.17                       ( k1_zfmisc_1 @
% 17.93/18.17                         ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) =>
% 17.93/18.17                   ( ( ( D ) = ( k1_tops_2 @ A @ B @ C ) ) <=>
% 17.93/18.17                     ( ![E:$i]:
% 17.93/18.17                       ( ( m1_subset_1 @
% 17.93/18.17                           E @ 
% 17.93/18.17                           ( k1_zfmisc_1 @
% 17.93/18.17                             ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) =>
% 17.93/18.17                         ( ( r2_hidden @ E @ D ) <=>
% 17.93/18.17                           ( ?[F:$i]:
% 17.93/18.17                             ( ( m1_subset_1 @
% 17.93/18.17                                 F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 17.93/18.17                               ( r2_hidden @ F @ C ) & 
% 17.93/18.17                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ F @ B ) =
% 17.93/18.17                                 ( E ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 17.93/18.17  thf(zf_stmt_1, axiom,
% 17.93/18.17    (![F:$i,E:$i,C:$i,B:$i,A:$i]:
% 17.93/18.17     ( ( zip_tseitin_0 @ F @ E @ C @ B @ A ) <=>
% 17.93/18.17       ( ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ F @ B ) = ( E ) ) & 
% 17.93/18.17         ( r2_hidden @ F @ C ) & 
% 17.93/18.17         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 17.93/18.17  thf('7', plain,
% 17.93/18.17      (![X20 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 17.93/18.17         ((zip_tseitin_0 @ X22 @ X20 @ X24 @ X23 @ X25)
% 17.93/18.17          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 17.93/18.17          | ~ (r2_hidden @ X22 @ X24)
% 17.93/18.17          | ((k9_subset_1 @ (u1_struct_0 @ X25) @ X22 @ X23) != (X20)))),
% 17.93/18.17      inference('cnf', [status(esa)], [zf_stmt_1])).
% 17.93/18.17  thf('8', plain,
% 17.93/18.17      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 17.93/18.17         (~ (r2_hidden @ X22 @ X24)
% 17.93/18.17          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 17.93/18.17          | (zip_tseitin_0 @ X22 @ 
% 17.93/18.17             (k9_subset_1 @ (u1_struct_0 @ X25) @ X22 @ X23) @ X24 @ X23 @ X25))),
% 17.93/18.17      inference('simplify', [status(thm)], ['7'])).
% 17.93/18.17  thf('9', plain,
% 17.93/18.17      (![X0 : $i, X1 : $i]:
% 17.93/18.17         ((zip_tseitin_0 @ sk_B @ 
% 17.93/18.17           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ X1 @ X0 @ sk_A)
% 17.93/18.17          | ~ (r2_hidden @ sk_B @ X1))),
% 17.93/18.17      inference('sup-', [status(thm)], ['6', '8'])).
% 17.93/18.17  thf('10', plain,
% 17.93/18.17      (![X0 : $i]:
% 17.93/18.17         (zip_tseitin_0 @ sk_B @ 
% 17.93/18.17          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ sk_D @ X0 @ sk_A)),
% 17.93/18.17      inference('sup-', [status(thm)], ['5', '9'])).
% 17.93/18.17  thf('11', plain,
% 17.93/18.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.93/18.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.93/18.17  thf('12', plain,
% 17.93/18.17      ((m1_subset_1 @ sk_D @ 
% 17.93/18.17        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 17.93/18.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.93/18.17  thf(dt_k1_tops_2, axiom,
% 17.93/18.17    (![A:$i,B:$i,C:$i]:
% 17.93/18.17     ( ( ( l1_pre_topc @ A ) & 
% 17.93/18.17         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 17.93/18.17         ( m1_subset_1 @
% 17.93/18.17           C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 17.93/18.17       ( m1_subset_1 @
% 17.93/18.17         ( k1_tops_2 @ A @ B @ C ) @ 
% 17.93/18.17         ( k1_zfmisc_1 @
% 17.93/18.17           ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ))).
% 17.93/18.17  thf('13', plain,
% 17.93/18.17      (![X33 : $i, X34 : $i, X35 : $i]:
% 17.93/18.17         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 17.93/18.17          | ~ (l1_pre_topc @ X34)
% 17.93/18.17          | ~ (m1_subset_1 @ X35 @ 
% 17.93/18.17               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34))))
% 17.93/18.17          | (m1_subset_1 @ (k1_tops_2 @ X34 @ X33 @ X35) @ 
% 17.93/18.17             (k1_zfmisc_1 @ 
% 17.93/18.17              (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X34 @ X33))))))),
% 17.93/18.17      inference('cnf', [status(esa)], [dt_k1_tops_2])).
% 17.93/18.17  thf('14', plain,
% 17.93/18.17      (![X0 : $i]:
% 17.93/18.17         ((m1_subset_1 @ (k1_tops_2 @ sk_A @ X0 @ sk_D) @ 
% 17.93/18.17           (k1_zfmisc_1 @ 
% 17.93/18.17            (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)))))
% 17.93/18.17          | ~ (l1_pre_topc @ sk_A)
% 17.93/18.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 17.93/18.17      inference('sup-', [status(thm)], ['12', '13'])).
% 17.93/18.17  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 17.93/18.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.93/18.17  thf('16', plain,
% 17.93/18.17      (![X0 : $i]:
% 17.93/18.17         ((m1_subset_1 @ (k1_tops_2 @ sk_A @ X0 @ sk_D) @ 
% 17.93/18.17           (k1_zfmisc_1 @ 
% 17.93/18.17            (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)))))
% 17.93/18.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 17.93/18.17      inference('demod', [status(thm)], ['14', '15'])).
% 17.93/18.17  thf('17', plain,
% 17.93/18.17      ((m1_subset_1 @ (k1_tops_2 @ sk_A @ sk_C_1 @ sk_D) @ 
% 17.93/18.17        (k1_zfmisc_1 @ 
% 17.93/18.17         (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C_1)))))),
% 17.93/18.17      inference('sup-', [status(thm)], ['11', '16'])).
% 17.93/18.17  thf('18', plain,
% 17.93/18.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.93/18.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.93/18.17  thf(t29_pre_topc, axiom,
% 17.93/18.17    (![A:$i]:
% 17.93/18.17     ( ( l1_pre_topc @ A ) =>
% 17.93/18.17       ( ![B:$i]:
% 17.93/18.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.93/18.17           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 17.93/18.17  thf('19', plain,
% 17.93/18.17      (![X18 : $i, X19 : $i]:
% 17.93/18.17         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 17.93/18.17          | ((u1_struct_0 @ (k1_pre_topc @ X19 @ X18)) = (X18))
% 17.93/18.17          | ~ (l1_pre_topc @ X19))),
% 17.93/18.17      inference('cnf', [status(esa)], [t29_pre_topc])).
% 17.93/18.17  thf('20', plain,
% 17.93/18.17      ((~ (l1_pre_topc @ sk_A)
% 17.93/18.17        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C_1)) = (sk_C_1)))),
% 17.93/18.17      inference('sup-', [status(thm)], ['18', '19'])).
% 17.93/18.17  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 17.93/18.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.93/18.17  thf('22', plain,
% 17.93/18.17      (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C_1)) = (sk_C_1))),
% 17.93/18.17      inference('demod', [status(thm)], ['20', '21'])).
% 17.93/18.17  thf('23', plain,
% 17.93/18.17      ((m1_subset_1 @ (k1_tops_2 @ sk_A @ sk_C_1 @ sk_D) @ 
% 17.93/18.17        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_C_1)))),
% 17.93/18.17      inference('demod', [status(thm)], ['17', '22'])).
% 17.93/18.17  thf('24', plain,
% 17.93/18.17      (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C_1)) = (sk_C_1))),
% 17.93/18.17      inference('demod', [status(thm)], ['20', '21'])).
% 17.93/18.17  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 17.93/18.17  thf(zf_stmt_3, axiom,
% 17.93/18.17    (![A:$i]:
% 17.93/18.17     ( ( l1_pre_topc @ A ) =>
% 17.93/18.17       ( ![B:$i]:
% 17.93/18.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 17.93/18.17           ( ![C:$i]:
% 17.93/18.17             ( ( m1_subset_1 @
% 17.93/18.17                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 17.93/18.17               ( ![D:$i]:
% 17.93/18.17                 ( ( m1_subset_1 @
% 17.93/18.17                     D @ 
% 17.93/18.17                     ( k1_zfmisc_1 @
% 17.93/18.17                       ( k1_zfmisc_1 @
% 17.93/18.17                         ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) =>
% 17.93/18.17                   ( ( ( D ) = ( k1_tops_2 @ A @ B @ C ) ) <=>
% 17.93/18.17                     ( ![E:$i]:
% 17.93/18.17                       ( ( m1_subset_1 @
% 17.93/18.17                           E @ 
% 17.93/18.17                           ( k1_zfmisc_1 @
% 17.93/18.17                             ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) =>
% 17.93/18.17                         ( ( r2_hidden @ E @ D ) <=>
% 17.93/18.17                           ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 17.93/18.17  thf('25', plain,
% 17.93/18.17      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X31 : $i, X32 : $i]:
% 17.93/18.17         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 17.93/18.17          | ~ (m1_subset_1 @ X28 @ 
% 17.93/18.17               (k1_zfmisc_1 @ 
% 17.93/18.17                (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X27 @ X26)))))
% 17.93/18.17          | ((X28) != (k1_tops_2 @ X27 @ X26 @ X29))
% 17.93/18.17          | (r2_hidden @ X31 @ X28)
% 17.93/18.17          | ~ (zip_tseitin_0 @ X32 @ X31 @ X29 @ X26 @ X27)
% 17.93/18.17          | ~ (m1_subset_1 @ X31 @ 
% 17.93/18.17               (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X27 @ X26))))
% 17.93/18.17          | ~ (m1_subset_1 @ X29 @ 
% 17.93/18.17               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))
% 17.93/18.17          | ~ (l1_pre_topc @ X27))),
% 17.93/18.17      inference('cnf', [status(esa)], [zf_stmt_3])).
% 17.93/18.17  thf('26', plain,
% 17.93/18.17      (![X26 : $i, X27 : $i, X29 : $i, X31 : $i, X32 : $i]:
% 17.93/18.17         (~ (l1_pre_topc @ X27)
% 17.93/18.17          | ~ (m1_subset_1 @ X29 @ 
% 17.93/18.17               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))
% 17.93/18.17          | ~ (m1_subset_1 @ X31 @ 
% 17.93/18.17               (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X27 @ X26))))
% 17.93/18.17          | ~ (zip_tseitin_0 @ X32 @ X31 @ X29 @ X26 @ X27)
% 17.93/18.17          | (r2_hidden @ X31 @ (k1_tops_2 @ X27 @ X26 @ X29))
% 17.93/18.17          | ~ (m1_subset_1 @ (k1_tops_2 @ X27 @ X26 @ X29) @ 
% 17.93/18.17               (k1_zfmisc_1 @ 
% 17.93/18.17                (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X27 @ X26)))))
% 17.93/18.17          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27))))),
% 17.93/18.17      inference('simplify', [status(thm)], ['25'])).
% 17.93/18.17  thf('27', plain,
% 17.93/18.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.93/18.17         (~ (m1_subset_1 @ (k1_tops_2 @ sk_A @ sk_C_1 @ X0) @ 
% 17.93/18.17             (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_C_1)))
% 17.93/18.17          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 17.93/18.17          | (r2_hidden @ X1 @ (k1_tops_2 @ sk_A @ sk_C_1 @ X0))
% 17.93/18.17          | ~ (zip_tseitin_0 @ X2 @ X1 @ X0 @ sk_C_1 @ sk_A)
% 17.93/18.17          | ~ (m1_subset_1 @ X1 @ 
% 17.93/18.17               (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C_1))))
% 17.93/18.17          | ~ (m1_subset_1 @ X0 @ 
% 17.93/18.17               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 17.93/18.17          | ~ (l1_pre_topc @ sk_A))),
% 17.93/18.17      inference('sup-', [status(thm)], ['24', '26'])).
% 17.93/18.17  thf('28', plain,
% 17.93/18.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 17.93/18.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.93/18.17  thf('29', plain,
% 17.93/18.17      (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C_1)) = (sk_C_1))),
% 17.93/18.17      inference('demod', [status(thm)], ['20', '21'])).
% 17.93/18.17  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 17.93/18.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.93/18.17  thf('31', plain,
% 17.93/18.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.93/18.17         (~ (m1_subset_1 @ (k1_tops_2 @ sk_A @ sk_C_1 @ X0) @ 
% 17.93/18.17             (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_C_1)))
% 17.93/18.17          | (r2_hidden @ X1 @ (k1_tops_2 @ sk_A @ sk_C_1 @ X0))
% 17.93/18.17          | ~ (zip_tseitin_0 @ X2 @ X1 @ X0 @ sk_C_1 @ sk_A)
% 17.93/18.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ sk_C_1))
% 17.93/18.17          | ~ (m1_subset_1 @ X0 @ 
% 17.93/18.17               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 17.93/18.17      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 17.93/18.17  thf('32', plain,
% 17.93/18.17      (![X0 : $i, X1 : $i]:
% 17.93/18.17         (~ (m1_subset_1 @ sk_D @ 
% 17.93/18.17             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 17.93/18.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_C_1))
% 17.93/18.17          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_C_1 @ sk_A)
% 17.93/18.17          | (r2_hidden @ X0 @ (k1_tops_2 @ sk_A @ sk_C_1 @ sk_D)))),
% 17.93/18.17      inference('sup-', [status(thm)], ['23', '31'])).
% 17.93/18.17  thf('33', plain,
% 17.93/18.17      ((m1_subset_1 @ sk_D @ 
% 17.93/18.17        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 17.93/18.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.93/18.17  thf('34', plain,
% 17.93/18.17      (![X0 : $i, X1 : $i]:
% 17.93/18.17         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_C_1))
% 17.93/18.17          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_C_1 @ sk_A)
% 17.93/18.17          | (r2_hidden @ X0 @ (k1_tops_2 @ sk_A @ sk_C_1 @ sk_D)))),
% 17.93/18.17      inference('demod', [status(thm)], ['32', '33'])).
% 17.93/18.17  thf('35', plain,
% 17.93/18.17      (((r2_hidden @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C_1) @ 
% 17.93/18.17         (k1_tops_2 @ sk_A @ sk_C_1 @ sk_D))
% 17.93/18.17        | ~ (m1_subset_1 @ 
% 17.93/18.17             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C_1) @ 
% 17.93/18.17             (k1_zfmisc_1 @ sk_C_1)))),
% 17.93/18.17      inference('sup-', [status(thm)], ['10', '34'])).
% 17.93/18.17  thf('36', plain,
% 17.93/18.17      (![X0 : $i]:
% 17.93/18.17         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1)
% 17.93/18.17           = (k3_xboole_0 @ X0 @ sk_C_1))),
% 17.93/18.17      inference('sup-', [status(thm)], ['1', '2'])).
% 17.93/18.17  thf('37', plain,
% 17.93/18.17      (![X0 : $i]:
% 17.93/18.17         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1)
% 17.93/18.17           = (k3_xboole_0 @ X0 @ sk_C_1))),
% 17.93/18.17      inference('sup-', [status(thm)], ['1', '2'])).
% 17.93/18.17  thf(d3_tarski, axiom,
% 17.93/18.17    (![A:$i,B:$i]:
% 17.93/18.17     ( ( r1_tarski @ A @ B ) <=>
% 17.93/18.17       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 17.93/18.17  thf('38', plain,
% 17.93/18.17      (![X1 : $i, X3 : $i]:
% 17.93/18.17         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 17.93/18.17      inference('cnf', [status(esa)], [d3_tarski])).
% 17.93/18.17  thf('39', plain,
% 17.93/18.17      (![X1 : $i, X3 : $i]:
% 17.93/18.17         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 17.93/18.17      inference('cnf', [status(esa)], [d3_tarski])).
% 17.93/18.17  thf('40', plain,
% 17.93/18.17      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 17.93/18.17      inference('sup-', [status(thm)], ['38', '39'])).
% 17.93/18.17  thf('41', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 17.93/18.17      inference('simplify', [status(thm)], ['40'])).
% 17.93/18.17  thf(t3_subset, axiom,
% 17.93/18.17    (![A:$i,B:$i]:
% 17.93/18.17     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 17.93/18.17  thf('42', plain,
% 17.93/18.17      (![X12 : $i, X14 : $i]:
% 17.93/18.17         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 17.93/18.17      inference('cnf', [status(esa)], [t3_subset])).
% 17.93/18.17  thf('43', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 17.93/18.17      inference('sup-', [status(thm)], ['41', '42'])).
% 17.93/18.17  thf(dt_k9_subset_1, axiom,
% 17.93/18.17    (![A:$i,B:$i,C:$i]:
% 17.93/18.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 17.93/18.17       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 17.93/18.17  thf('44', plain,
% 17.93/18.17      (![X4 : $i, X5 : $i, X6 : $i]:
% 17.93/18.17         ((m1_subset_1 @ (k9_subset_1 @ X4 @ X5 @ X6) @ (k1_zfmisc_1 @ X4))
% 17.93/18.17          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X4)))),
% 17.93/18.17      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 17.93/18.17  thf('45', plain,
% 17.93/18.17      (![X0 : $i, X1 : $i]:
% 17.93/18.17         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 17.93/18.17      inference('sup-', [status(thm)], ['43', '44'])).
% 17.93/18.17  thf('46', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 17.93/18.17      inference('sup-', [status(thm)], ['41', '42'])).
% 17.93/18.17  thf('47', plain,
% 17.93/18.17      (![X7 : $i, X8 : $i, X9 : $i]:
% 17.93/18.17         (((k9_subset_1 @ X9 @ X7 @ X8) = (k3_xboole_0 @ X7 @ X8))
% 17.93/18.17          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 17.93/18.17      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 17.93/18.17  thf('48', plain,
% 17.93/18.17      (![X0 : $i, X1 : $i]:
% 17.93/18.17         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 17.93/18.17      inference('sup-', [status(thm)], ['46', '47'])).
% 17.93/18.17  thf('49', plain,
% 17.93/18.17      (![X0 : $i, X1 : $i]:
% 17.93/18.17         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 17.93/18.17      inference('demod', [status(thm)], ['45', '48'])).
% 17.93/18.17  thf('50', plain,
% 17.93/18.17      ((r2_hidden @ (k3_xboole_0 @ sk_B @ sk_C_1) @ 
% 17.93/18.17        (k1_tops_2 @ sk_A @ sk_C_1 @ sk_D))),
% 17.93/18.17      inference('demod', [status(thm)], ['35', '36', '37', '49'])).
% 17.93/18.17  thf('51', plain, ($false), inference('demod', [status(thm)], ['4', '50'])).
% 17.93/18.17  
% 17.93/18.17  % SZS output end Refutation
% 17.93/18.17  
% 17.93/18.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
