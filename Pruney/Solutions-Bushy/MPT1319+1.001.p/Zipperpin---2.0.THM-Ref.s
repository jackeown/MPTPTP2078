%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1319+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v2BQBePcdz

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:29 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 268 expanded)
%              Number of leaves         :   27 (  89 expanded)
%              Depth                    :   22
%              Number of atoms          : 1497 (5303 expanded)
%              Number of equality atoms :   17 (  28 expanded)
%              Maximal formula depth    :   21 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tops_2_type,type,(
    k1_tops_2: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t40_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                 => ( ( r1_tarski @ C @ D )
                   => ( r1_tarski @ ( k1_tops_2 @ A @ B @ C ) @ ( k1_tops_2 @ A @ B @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                   => ( ( r1_tarski @ C @ D )
                     => ( r1_tarski @ ( k1_tops_2 @ A @ B @ C ) @ ( k1_tops_2 @ A @ B @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_tops_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ( m1_subset_1 @ ( k1_tops_2 @ X20 @ X19 @ X21 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X20 @ X19 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ C @ B @ A )
    <=> ( ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ F @ B )
          = E )
        & ( r2_hidden @ F @ C )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

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

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X13 @ X12 ) ) ) ) )
      | ( X14
       != ( k1_tops_2 @ X13 @ X12 @ X15 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X17 @ X15 @ X12 @ X13 ) @ X17 @ X15 @ X12 @ X13 )
      | ~ ( r2_hidden @ X17 @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X13 @ X12 ) ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('10',plain,(
    ! [X12: $i,X13: $i,X15: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X13 @ X12 ) ) ) )
      | ~ ( r2_hidden @ X17 @ ( k1_tops_2 @ X13 @ X12 @ X15 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X17 @ X15 @ X12 @ X13 ) @ X17 @ X15 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ ( k1_tops_2 @ X13 @ X12 @ X15 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X13 @ X12 ) ) ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_C_1 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_C_1 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('16',plain,(
    m1_subset_1 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('17',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ( m1_subset_1 @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X0 @ sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','19'])).

thf('21',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ X7 ) @ X8 @ X9 )
        = X6 )
      | ~ ( zip_tseitin_0 @ X8 @ X6 @ X10 @ X9 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_F_1 @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ sk_B )
        = ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k9_subset_1 @ X24 @ X22 @ X23 )
        = ( k3_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( ( k3_xboole_0 @ sk_B @ ( sk_F_1 @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) )
        = ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['22','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','19'])).

thf('30',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ X10 )
      | ~ ( zip_tseitin_0 @ X8 @ X6 @ X10 @ X9 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_F_1 @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_F_1 @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','19'])).

thf('37',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( zip_tseitin_0 @ X8 @ X6 @ X10 @ X9 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X6: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X8 @ X6 @ X10 @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X11 ) @ X8 @ X9 )
       != X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('40',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( zip_tseitin_0 @ X8 @ ( k9_subset_1 @ ( u1_struct_0 @ X11 ) @ X8 @ X9 ) @ X10 @ X9 @ X11 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_F_1 @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ X1 ) @ X2 @ X1 @ sk_A )
      | ~ ( r2_hidden @ ( sk_F_1 @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_F_1 @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ X1 ) @ sk_D @ X1 @ sk_A )
      | ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_F_1 @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ X1 ) @ sk_D @ X1 @ sk_A )
      | ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ sk_B ) @ sk_D @ sk_B @ sk_A )
      | ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_B @ ( sk_F_1 @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_D @ sk_B @ sk_A )
      | ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_D @ sk_B @ sk_A )
      | ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_D @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) )
      | ( m1_subset_1 @ ( k1_tops_2 @ X20 @ X19 @ X21 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X20 @ X19 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_2])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X13 @ X12 ) ) ) ) )
      | ( X14
       != ( k1_tops_2 @ X13 @ X12 @ X15 ) )
      | ( r2_hidden @ X17 @ X14 )
      | ~ ( zip_tseitin_0 @ X18 @ X17 @ X15 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X13 @ X12 ) ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('60',plain,(
    ! [X12: $i,X13: $i,X15: $i,X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X13 @ X12 ) ) ) )
      | ~ ( zip_tseitin_0 @ X18 @ X17 @ X15 @ X12 @ X13 )
      | ( r2_hidden @ X17 @ ( k1_tops_2 @ X13 @ X12 @ X15 ) )
      | ~ ( m1_subset_1 @ ( k1_tops_2 @ X13 @ X12 @ X15 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X13 @ X12 ) ) ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_D @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ~ ( zip_tseitin_0 @ X1 @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ sk_D @ sk_B @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['51','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_D ) )
      | ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_D ) )
      | ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('70',plain,
    ( ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_D ) )
    | ( r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    r1_tarski @ ( k1_tops_2 @ sk_A @ sk_B @ sk_C_1 ) @ ( k1_tops_2 @ sk_A @ sk_B @ sk_D ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['0','71'])).


%------------------------------------------------------------------------------
