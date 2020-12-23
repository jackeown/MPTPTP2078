%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NTwdv5QLSS

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:39 EST 2020

% Result     : Theorem 34.55s
% Output     : Refutation 34.55s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 276 expanded)
%              Number of leaves         :   28 (  91 expanded)
%              Depth                    :   18
%              Number of atoms          : 1285 (3751 expanded)
%              Number of equality atoms :   34 ( 102 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tops_2_type,type,(
    k1_tops_2: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ~ ( r2_hidden @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k1_tops_2 @ sk_A @ sk_C_1 @ sk_D_1 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 )
      = ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r2_hidden @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ ( k1_tops_2 @ sk_A @ sk_C_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 )
      = ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('6',plain,(
    r2_hidden @ sk_B @ sk_D_1 ),
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
    ! [X21: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X23 @ X21 @ X25 @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( r2_hidden @ X23 @ X25 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X26 ) @ X23 @ X24 )
       != X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('9',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( zip_tseitin_0 @ X23 @ ( k9_subset_1 @ ( u1_struct_0 @ X26 ) @ X23 @ X24 ) @ X25 @ X24 @ X26 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ X1 @ X0 @ sk_A )
      | ~ ( r2_hidden @ sk_B @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ sk_D_1 @ X0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    zip_tseitin_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_D_1 @ sk_C_1 @ sk_A ),
    inference('sup+',[status(thm)],['5','11'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k3_xboole_0 @ sk_C_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_C_1 @ X0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('22',plain,
    ( ( sk_C_1
      = ( k3_xboole_0 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_C_1 )
    | ~ ( r2_hidden @ ( sk_D @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_C_1 )
    | ( sk_C_1
      = ( k3_xboole_0 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_C_1 )
    | ( sk_C_1
      = ( k3_xboole_0 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['13'])).

thf('25',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('28',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('31',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['25','35'])).

thf('37',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) ) )
      | ( m1_subset_1 @ ( k1_tops_2 @ X35 @ X34 @ X36 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X35 @ X34 ) ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ X0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ X0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('46',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X20 @ X19 ) )
        = X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) )
        = ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) )
      = ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_tops_2 @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X20 @ X19 ) )
        = X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) ) )
        = ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

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

thf('61',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X28 @ X27 ) ) ) ) )
      | ( X29
       != ( k1_tops_2 @ X28 @ X27 @ X30 ) )
      | ( r2_hidden @ X32 @ X29 )
      | ~ ( zip_tseitin_0 @ X33 @ X32 @ X30 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X28 @ X27 ) ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('62',plain,(
    ! [X27: $i,X28: $i,X30: $i,X32: $i,X33: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X28 @ X27 ) ) ) )
      | ~ ( zip_tseitin_0 @ X33 @ X32 @ X30 @ X27 @ X28 )
      | ( r2_hidden @ X32 @ ( k1_tops_2 @ X28 @ X27 @ X30 ) )
      | ~ ( m1_subset_1 @ ( k1_tops_2 @ X28 @ X27 @ X30 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X28 @ X27 ) ) ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ ( k1_tops_2 @ X0 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( r2_hidden @ X3 @ ( k1_tops_2 @ X0 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ X2 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X3 @ X2 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) ) ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ ( k1_tops_2 @ X0 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ X3 @ ( k1_tops_2 @ X0 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ X2 ) )
      | ~ ( zip_tseitin_0 @ X4 @ X3 @ X2 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) ) ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X0 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) ) ) ) )
      | ~ ( zip_tseitin_0 @ X4 @ X3 @ X2 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ( r2_hidden @ X3 @ ( k1_tops_2 @ X0 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ X2 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ ( k1_tops_2 @ X0 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_2 @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_D_1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_D_1 @ ( k3_xboole_0 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) )
      | ~ ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['50','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('70',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('71',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('72',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X20 @ X19 ) )
        = X19 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('74',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C_1 ) )
    = sk_C_1 ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_2 @ sk_A @ sk_C_1 @ sk_D_1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_D_1 @ sk_C_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['67','68','69','70','71','76','77'])).

thf('79',plain,
    ( ~ ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ ( k1_tops_2 @ sk_A @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['12','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('81',plain,(
    r2_hidden @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ ( k1_tops_2 @ sk_A @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['4','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NTwdv5QLSS
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 34.55/34.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 34.55/34.78  % Solved by: fo/fo7.sh
% 34.55/34.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 34.55/34.78  % done 10457 iterations in 34.317s
% 34.55/34.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 34.55/34.78  % SZS output start Refutation
% 34.55/34.78  thf(sk_D_1_type, type, sk_D_1: $i).
% 34.55/34.78  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 34.55/34.78  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 34.55/34.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 34.55/34.78  thf(sk_C_1_type, type, sk_C_1: $i).
% 34.55/34.78  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 34.55/34.78  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 34.55/34.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 34.55/34.78  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 34.55/34.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 34.55/34.78  thf(k1_tops_2_type, type, k1_tops_2: $i > $i > $i > $i).
% 34.55/34.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 34.55/34.78  thf(sk_B_type, type, sk_B: $i).
% 34.55/34.78  thf(sk_A_type, type, sk_A: $i).
% 34.55/34.78  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 34.55/34.78  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 34.55/34.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 34.55/34.78  thf(t41_tops_2, conjecture,
% 34.55/34.78    (![A:$i]:
% 34.55/34.78     ( ( l1_pre_topc @ A ) =>
% 34.55/34.78       ( ![B:$i]:
% 34.55/34.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 34.55/34.78           ( ![C:$i]:
% 34.55/34.78             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 34.55/34.78               ( ![D:$i]:
% 34.55/34.78                 ( ( m1_subset_1 @
% 34.55/34.78                     D @ 
% 34.55/34.78                     ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 34.55/34.78                   ( ( r2_hidden @ B @ D ) =>
% 34.55/34.78                     ( r2_hidden @
% 34.55/34.78                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 34.55/34.78                       ( k1_tops_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 34.55/34.78  thf(zf_stmt_0, negated_conjecture,
% 34.55/34.78    (~( ![A:$i]:
% 34.55/34.78        ( ( l1_pre_topc @ A ) =>
% 34.55/34.78          ( ![B:$i]:
% 34.55/34.78            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 34.55/34.78              ( ![C:$i]:
% 34.55/34.78                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 34.55/34.78                  ( ![D:$i]:
% 34.55/34.78                    ( ( m1_subset_1 @
% 34.55/34.78                        D @ 
% 34.55/34.78                        ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 34.55/34.78                      ( ( r2_hidden @ B @ D ) =>
% 34.55/34.78                        ( r2_hidden @
% 34.55/34.78                          ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 34.55/34.78                          ( k1_tops_2 @ A @ C @ D ) ) ) ) ) ) ) ) ) ) )),
% 34.55/34.78    inference('cnf.neg', [status(esa)], [t41_tops_2])).
% 34.55/34.78  thf('0', plain,
% 34.55/34.78      (~ (r2_hidden @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C_1) @ 
% 34.55/34.78          (k1_tops_2 @ sk_A @ sk_C_1 @ sk_D_1))),
% 34.55/34.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.55/34.78  thf('1', plain,
% 34.55/34.78      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 34.55/34.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.55/34.78  thf(redefinition_k9_subset_1, axiom,
% 34.55/34.78    (![A:$i,B:$i,C:$i]:
% 34.55/34.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 34.55/34.78       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 34.55/34.78  thf('2', plain,
% 34.55/34.78      (![X10 : $i, X11 : $i, X12 : $i]:
% 34.55/34.78         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 34.55/34.78          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 34.55/34.78      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 34.55/34.78  thf('3', plain,
% 34.55/34.78      (![X0 : $i]:
% 34.55/34.78         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1)
% 34.55/34.78           = (k3_xboole_0 @ X0 @ sk_C_1))),
% 34.55/34.78      inference('sup-', [status(thm)], ['1', '2'])).
% 34.55/34.78  thf('4', plain,
% 34.55/34.78      (~ (r2_hidden @ (k3_xboole_0 @ sk_B @ sk_C_1) @ 
% 34.55/34.78          (k1_tops_2 @ sk_A @ sk_C_1 @ sk_D_1))),
% 34.55/34.78      inference('demod', [status(thm)], ['0', '3'])).
% 34.55/34.78  thf('5', plain,
% 34.55/34.78      (![X0 : $i]:
% 34.55/34.78         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1)
% 34.55/34.78           = (k3_xboole_0 @ X0 @ sk_C_1))),
% 34.55/34.78      inference('sup-', [status(thm)], ['1', '2'])).
% 34.55/34.78  thf('6', plain, ((r2_hidden @ sk_B @ sk_D_1)),
% 34.55/34.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.55/34.78  thf('7', plain,
% 34.55/34.78      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 34.55/34.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.55/34.78  thf(d3_tops_2, axiom,
% 34.55/34.78    (![A:$i]:
% 34.55/34.78     ( ( l1_pre_topc @ A ) =>
% 34.55/34.78       ( ![B:$i]:
% 34.55/34.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 34.55/34.78           ( ![C:$i]:
% 34.55/34.78             ( ( m1_subset_1 @
% 34.55/34.78                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 34.55/34.78               ( ![D:$i]:
% 34.55/34.78                 ( ( m1_subset_1 @
% 34.55/34.78                     D @ 
% 34.55/34.78                     ( k1_zfmisc_1 @
% 34.55/34.78                       ( k1_zfmisc_1 @
% 34.55/34.78                         ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) =>
% 34.55/34.78                   ( ( ( D ) = ( k1_tops_2 @ A @ B @ C ) ) <=>
% 34.55/34.78                     ( ![E:$i]:
% 34.55/34.78                       ( ( m1_subset_1 @
% 34.55/34.78                           E @ 
% 34.55/34.78                           ( k1_zfmisc_1 @
% 34.55/34.78                             ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) =>
% 34.55/34.78                         ( ( r2_hidden @ E @ D ) <=>
% 34.55/34.78                           ( ?[F:$i]:
% 34.55/34.78                             ( ( m1_subset_1 @
% 34.55/34.78                                 F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 34.55/34.78                               ( r2_hidden @ F @ C ) & 
% 34.55/34.78                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ F @ B ) =
% 34.55/34.78                                 ( E ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 34.55/34.78  thf(zf_stmt_1, axiom,
% 34.55/34.78    (![F:$i,E:$i,C:$i,B:$i,A:$i]:
% 34.55/34.78     ( ( zip_tseitin_0 @ F @ E @ C @ B @ A ) <=>
% 34.55/34.78       ( ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ F @ B ) = ( E ) ) & 
% 34.55/34.78         ( r2_hidden @ F @ C ) & 
% 34.55/34.78         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 34.55/34.78  thf('8', plain,
% 34.55/34.78      (![X21 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 34.55/34.78         ((zip_tseitin_0 @ X23 @ X21 @ X25 @ X24 @ X26)
% 34.55/34.78          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 34.55/34.78          | ~ (r2_hidden @ X23 @ X25)
% 34.55/34.78          | ((k9_subset_1 @ (u1_struct_0 @ X26) @ X23 @ X24) != (X21)))),
% 34.55/34.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 34.55/34.78  thf('9', plain,
% 34.55/34.78      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 34.55/34.78         (~ (r2_hidden @ X23 @ X25)
% 34.55/34.78          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 34.55/34.78          | (zip_tseitin_0 @ X23 @ 
% 34.55/34.78             (k9_subset_1 @ (u1_struct_0 @ X26) @ X23 @ X24) @ X25 @ X24 @ X26))),
% 34.55/34.78      inference('simplify', [status(thm)], ['8'])).
% 34.55/34.78  thf('10', plain,
% 34.55/34.78      (![X0 : $i, X1 : $i]:
% 34.55/34.78         ((zip_tseitin_0 @ sk_B @ 
% 34.55/34.78           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ X1 @ X0 @ sk_A)
% 34.55/34.78          | ~ (r2_hidden @ sk_B @ X1))),
% 34.55/34.78      inference('sup-', [status(thm)], ['7', '9'])).
% 34.55/34.78  thf('11', plain,
% 34.55/34.78      (![X0 : $i]:
% 34.55/34.78         (zip_tseitin_0 @ sk_B @ 
% 34.55/34.78          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ sk_D_1 @ X0 @ sk_A)),
% 34.55/34.78      inference('sup-', [status(thm)], ['6', '10'])).
% 34.55/34.78  thf('12', plain,
% 34.55/34.78      ((zip_tseitin_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_D_1 @ 
% 34.55/34.78        sk_C_1 @ sk_A)),
% 34.55/34.78      inference('sup+', [status(thm)], ['5', '11'])).
% 34.55/34.78  thf(d4_xboole_0, axiom,
% 34.55/34.78    (![A:$i,B:$i,C:$i]:
% 34.55/34.78     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 34.55/34.78       ( ![D:$i]:
% 34.55/34.78         ( ( r2_hidden @ D @ C ) <=>
% 34.55/34.78           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 34.55/34.78  thf('13', plain,
% 34.55/34.78      (![X5 : $i, X6 : $i, X9 : $i]:
% 34.55/34.78         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 34.55/34.78          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 34.55/34.78          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 34.55/34.78      inference('cnf', [status(esa)], [d4_xboole_0])).
% 34.55/34.78  thf('14', plain,
% 34.55/34.78      (![X0 : $i, X1 : $i]:
% 34.55/34.78         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 34.55/34.78          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 34.55/34.78      inference('eq_fact', [status(thm)], ['13'])).
% 34.55/34.78  thf('15', plain,
% 34.55/34.78      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 34.55/34.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.55/34.78  thf(t3_subset, axiom,
% 34.55/34.78    (![A:$i,B:$i]:
% 34.55/34.78     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 34.55/34.78  thf('16', plain,
% 34.55/34.78      (![X13 : $i, X14 : $i]:
% 34.55/34.78         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 34.55/34.78      inference('cnf', [status(esa)], [t3_subset])).
% 34.55/34.78  thf('17', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 34.55/34.78      inference('sup-', [status(thm)], ['15', '16'])).
% 34.55/34.78  thf(d3_tarski, axiom,
% 34.55/34.78    (![A:$i,B:$i]:
% 34.55/34.78     ( ( r1_tarski @ A @ B ) <=>
% 34.55/34.78       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 34.55/34.78  thf('18', plain,
% 34.55/34.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.55/34.78         (~ (r2_hidden @ X0 @ X1)
% 34.55/34.78          | (r2_hidden @ X0 @ X2)
% 34.55/34.78          | ~ (r1_tarski @ X1 @ X2))),
% 34.55/34.78      inference('cnf', [status(esa)], [d3_tarski])).
% 34.55/34.78  thf('19', plain,
% 34.55/34.78      (![X0 : $i]:
% 34.55/34.78         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 34.55/34.78      inference('sup-', [status(thm)], ['17', '18'])).
% 34.55/34.78  thf('20', plain,
% 34.55/34.78      (![X0 : $i]:
% 34.55/34.78         (((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ X0))
% 34.55/34.78          | (r2_hidden @ (sk_D @ sk_C_1 @ X0 @ sk_C_1) @ (u1_struct_0 @ sk_A)))),
% 34.55/34.78      inference('sup-', [status(thm)], ['14', '19'])).
% 34.55/34.78  thf('21', plain,
% 34.55/34.78      (![X5 : $i, X6 : $i, X9 : $i]:
% 34.55/34.78         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 34.55/34.78          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 34.55/34.78          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 34.55/34.78          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 34.55/34.78      inference('cnf', [status(esa)], [d4_xboole_0])).
% 34.55/34.78  thf('22', plain,
% 34.55/34.78      ((((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ (u1_struct_0 @ sk_A)))
% 34.55/34.78        | ~ (r2_hidden @ (sk_D @ sk_C_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 34.55/34.78             sk_C_1)
% 34.55/34.78        | ~ (r2_hidden @ (sk_D @ sk_C_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 34.55/34.78             sk_C_1)
% 34.55/34.78        | ((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ (u1_struct_0 @ sk_A))))),
% 34.55/34.78      inference('sup-', [status(thm)], ['20', '21'])).
% 34.55/34.78  thf('23', plain,
% 34.55/34.78      ((~ (r2_hidden @ (sk_D @ sk_C_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_C_1)
% 34.55/34.78        | ((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ (u1_struct_0 @ sk_A))))),
% 34.55/34.78      inference('simplify', [status(thm)], ['22'])).
% 34.55/34.78  thf('24', plain,
% 34.55/34.78      (![X0 : $i, X1 : $i]:
% 34.55/34.78         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 34.55/34.78          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 34.55/34.78      inference('eq_fact', [status(thm)], ['13'])).
% 34.55/34.78  thf('25', plain,
% 34.55/34.78      (((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 34.55/34.78      inference('clc', [status(thm)], ['23', '24'])).
% 34.55/34.78  thf('26', plain,
% 34.55/34.78      (![X1 : $i, X3 : $i]:
% 34.55/34.78         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 34.55/34.78      inference('cnf', [status(esa)], [d3_tarski])).
% 34.55/34.78  thf('27', plain,
% 34.55/34.78      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 34.55/34.78         (~ (r2_hidden @ X8 @ X7)
% 34.55/34.78          | (r2_hidden @ X8 @ X5)
% 34.55/34.78          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 34.55/34.78      inference('cnf', [status(esa)], [d4_xboole_0])).
% 34.55/34.78  thf('28', plain,
% 34.55/34.78      (![X5 : $i, X6 : $i, X8 : $i]:
% 34.55/34.78         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 34.55/34.78      inference('simplify', [status(thm)], ['27'])).
% 34.55/34.78  thf('29', plain,
% 34.55/34.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.55/34.78         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 34.55/34.78          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 34.55/34.78      inference('sup-', [status(thm)], ['26', '28'])).
% 34.55/34.78  thf('30', plain,
% 34.55/34.78      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 34.55/34.78         (~ (r2_hidden @ X8 @ X7)
% 34.55/34.78          | (r2_hidden @ X8 @ X6)
% 34.55/34.78          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 34.55/34.78      inference('cnf', [status(esa)], [d4_xboole_0])).
% 34.55/34.78  thf('31', plain,
% 34.55/34.78      (![X5 : $i, X6 : $i, X8 : $i]:
% 34.55/34.78         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 34.55/34.78      inference('simplify', [status(thm)], ['30'])).
% 34.55/34.78  thf('32', plain,
% 34.55/34.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 34.55/34.78         ((r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X3)
% 34.55/34.78          | (r2_hidden @ 
% 34.55/34.78             (sk_C @ X3 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)) @ X0))),
% 34.55/34.78      inference('sup-', [status(thm)], ['29', '31'])).
% 34.55/34.78  thf('33', plain,
% 34.55/34.78      (![X1 : $i, X3 : $i]:
% 34.55/34.78         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 34.55/34.78      inference('cnf', [status(esa)], [d3_tarski])).
% 34.55/34.78  thf('34', plain,
% 34.55/34.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.55/34.78         ((r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ X1) @ X0)
% 34.55/34.78          | (r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ X1) @ X0))),
% 34.55/34.78      inference('sup-', [status(thm)], ['32', '33'])).
% 34.55/34.78  thf('35', plain,
% 34.55/34.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.55/34.78         (r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ X1) @ X0)),
% 34.55/34.78      inference('simplify', [status(thm)], ['34'])).
% 34.55/34.78  thf('36', plain,
% 34.55/34.78      (![X0 : $i]:
% 34.55/34.78         (r1_tarski @ (k3_xboole_0 @ sk_C_1 @ X0) @ (u1_struct_0 @ sk_A))),
% 34.55/34.78      inference('sup+', [status(thm)], ['25', '35'])).
% 34.55/34.78  thf('37', plain,
% 34.55/34.78      (![X13 : $i, X15 : $i]:
% 34.55/34.78         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 34.55/34.78      inference('cnf', [status(esa)], [t3_subset])).
% 34.55/34.78  thf('38', plain,
% 34.55/34.78      (![X0 : $i]:
% 34.55/34.78         (m1_subset_1 @ (k3_xboole_0 @ sk_C_1 @ X0) @ 
% 34.55/34.78          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 34.55/34.78      inference('sup-', [status(thm)], ['36', '37'])).
% 34.55/34.78  thf('39', plain,
% 34.55/34.78      ((m1_subset_1 @ sk_D_1 @ 
% 34.55/34.78        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 34.55/34.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.55/34.78  thf(dt_k1_tops_2, axiom,
% 34.55/34.78    (![A:$i,B:$i,C:$i]:
% 34.55/34.78     ( ( ( l1_pre_topc @ A ) & 
% 34.55/34.78         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 34.55/34.78         ( m1_subset_1 @
% 34.55/34.78           C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 34.55/34.78       ( m1_subset_1 @
% 34.55/34.78         ( k1_tops_2 @ A @ B @ C ) @ 
% 34.55/34.78         ( k1_zfmisc_1 @
% 34.55/34.78           ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ))).
% 34.55/34.78  thf('40', plain,
% 34.55/34.78      (![X34 : $i, X35 : $i, X36 : $i]:
% 34.55/34.78         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 34.55/34.78          | ~ (l1_pre_topc @ X35)
% 34.55/34.78          | ~ (m1_subset_1 @ X36 @ 
% 34.55/34.78               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35))))
% 34.55/34.78          | (m1_subset_1 @ (k1_tops_2 @ X35 @ X34 @ X36) @ 
% 34.55/34.78             (k1_zfmisc_1 @ 
% 34.55/34.78              (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X35 @ X34))))))),
% 34.55/34.78      inference('cnf', [status(esa)], [dt_k1_tops_2])).
% 34.55/34.78  thf('41', plain,
% 34.55/34.78      (![X0 : $i]:
% 34.55/34.78         ((m1_subset_1 @ (k1_tops_2 @ sk_A @ X0 @ sk_D_1) @ 
% 34.55/34.78           (k1_zfmisc_1 @ 
% 34.55/34.78            (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)))))
% 34.55/34.78          | ~ (l1_pre_topc @ sk_A)
% 34.55/34.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 34.55/34.78      inference('sup-', [status(thm)], ['39', '40'])).
% 34.55/34.78  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 34.55/34.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.55/34.78  thf('43', plain,
% 34.55/34.78      (![X0 : $i]:
% 34.55/34.78         ((m1_subset_1 @ (k1_tops_2 @ sk_A @ X0 @ sk_D_1) @ 
% 34.55/34.78           (k1_zfmisc_1 @ 
% 34.55/34.78            (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)))))
% 34.55/34.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 34.55/34.78      inference('demod', [status(thm)], ['41', '42'])).
% 34.55/34.78  thf('44', plain,
% 34.55/34.78      (![X0 : $i]:
% 34.55/34.78         (m1_subset_1 @ 
% 34.55/34.78          (k1_tops_2 @ sk_A @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_D_1) @ 
% 34.55/34.78          (k1_zfmisc_1 @ 
% 34.55/34.78           (k1_zfmisc_1 @ 
% 34.55/34.78            (u1_struct_0 @ (k1_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C_1 @ X0))))))),
% 34.55/34.78      inference('sup-', [status(thm)], ['38', '43'])).
% 34.55/34.78  thf('45', plain,
% 34.55/34.78      (![X0 : $i]:
% 34.55/34.78         (m1_subset_1 @ (k3_xboole_0 @ sk_C_1 @ X0) @ 
% 34.55/34.78          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 34.55/34.78      inference('sup-', [status(thm)], ['36', '37'])).
% 34.55/34.78  thf(t29_pre_topc, axiom,
% 34.55/34.78    (![A:$i]:
% 34.55/34.78     ( ( l1_pre_topc @ A ) =>
% 34.55/34.78       ( ![B:$i]:
% 34.55/34.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 34.55/34.78           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 34.55/34.78  thf('46', plain,
% 34.55/34.78      (![X19 : $i, X20 : $i]:
% 34.55/34.78         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 34.55/34.78          | ((u1_struct_0 @ (k1_pre_topc @ X20 @ X19)) = (X19))
% 34.55/34.78          | ~ (l1_pre_topc @ X20))),
% 34.55/34.78      inference('cnf', [status(esa)], [t29_pre_topc])).
% 34.55/34.78  thf('47', plain,
% 34.55/34.78      (![X0 : $i]:
% 34.55/34.78         (~ (l1_pre_topc @ sk_A)
% 34.55/34.78          | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C_1 @ X0)))
% 34.55/34.78              = (k3_xboole_0 @ sk_C_1 @ X0)))),
% 34.55/34.78      inference('sup-', [status(thm)], ['45', '46'])).
% 34.55/34.78  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 34.55/34.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.55/34.78  thf('49', plain,
% 34.55/34.78      (![X0 : $i]:
% 34.55/34.78         ((u1_struct_0 @ (k1_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C_1 @ X0)))
% 34.55/34.78           = (k3_xboole_0 @ sk_C_1 @ X0))),
% 34.55/34.78      inference('demod', [status(thm)], ['47', '48'])).
% 34.55/34.78  thf('50', plain,
% 34.55/34.78      (![X0 : $i]:
% 34.55/34.78         (m1_subset_1 @ 
% 34.55/34.78          (k1_tops_2 @ sk_A @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_D_1) @ 
% 34.55/34.78          (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k3_xboole_0 @ sk_C_1 @ X0))))),
% 34.55/34.78      inference('demod', [status(thm)], ['44', '49'])).
% 34.55/34.78  thf('51', plain,
% 34.55/34.78      (![X1 : $i, X3 : $i]:
% 34.55/34.78         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 34.55/34.78      inference('cnf', [status(esa)], [d3_tarski])).
% 34.55/34.78  thf('52', plain,
% 34.55/34.78      (![X5 : $i, X6 : $i, X8 : $i]:
% 34.55/34.78         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 34.55/34.78      inference('simplify', [status(thm)], ['30'])).
% 34.55/34.78  thf('53', plain,
% 34.55/34.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 34.55/34.78         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 34.55/34.78          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 34.55/34.78      inference('sup-', [status(thm)], ['51', '52'])).
% 34.55/34.78  thf('54', plain,
% 34.55/34.78      (![X1 : $i, X3 : $i]:
% 34.55/34.78         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 34.55/34.78      inference('cnf', [status(esa)], [d3_tarski])).
% 34.55/34.78  thf('55', plain,
% 34.55/34.78      (![X0 : $i, X1 : $i]:
% 34.55/34.78         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 34.55/34.78          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 34.55/34.78      inference('sup-', [status(thm)], ['53', '54'])).
% 34.55/34.78  thf('56', plain,
% 34.55/34.78      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 34.55/34.78      inference('simplify', [status(thm)], ['55'])).
% 34.55/34.78  thf('57', plain,
% 34.55/34.78      (![X13 : $i, X15 : $i]:
% 34.55/34.78         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 34.55/34.78      inference('cnf', [status(esa)], [t3_subset])).
% 34.55/34.78  thf('58', plain,
% 34.55/34.78      (![X0 : $i, X1 : $i]:
% 34.55/34.78         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 34.55/34.78      inference('sup-', [status(thm)], ['56', '57'])).
% 34.55/34.78  thf('59', plain,
% 34.55/34.78      (![X19 : $i, X20 : $i]:
% 34.55/34.78         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 34.55/34.78          | ((u1_struct_0 @ (k1_pre_topc @ X20 @ X19)) = (X19))
% 34.55/34.78          | ~ (l1_pre_topc @ X20))),
% 34.55/34.78      inference('cnf', [status(esa)], [t29_pre_topc])).
% 34.55/34.78  thf('60', plain,
% 34.55/34.78      (![X0 : $i, X1 : $i]:
% 34.55/34.78         (~ (l1_pre_topc @ X0)
% 34.55/34.78          | ((u1_struct_0 @ 
% 34.55/34.78              (k1_pre_topc @ X0 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0))))
% 34.55/34.78              = (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0))))),
% 34.55/34.78      inference('sup-', [status(thm)], ['58', '59'])).
% 34.55/34.78  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 34.55/34.78  thf(zf_stmt_3, axiom,
% 34.55/34.78    (![A:$i]:
% 34.55/34.78     ( ( l1_pre_topc @ A ) =>
% 34.55/34.78       ( ![B:$i]:
% 34.55/34.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 34.55/34.78           ( ![C:$i]:
% 34.55/34.78             ( ( m1_subset_1 @
% 34.55/34.78                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 34.55/34.78               ( ![D:$i]:
% 34.55/34.78                 ( ( m1_subset_1 @
% 34.55/34.78                     D @ 
% 34.55/34.78                     ( k1_zfmisc_1 @
% 34.55/34.78                       ( k1_zfmisc_1 @
% 34.55/34.78                         ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) ) =>
% 34.55/34.78                   ( ( ( D ) = ( k1_tops_2 @ A @ B @ C ) ) <=>
% 34.55/34.78                     ( ![E:$i]:
% 34.55/34.78                       ( ( m1_subset_1 @
% 34.55/34.78                           E @ 
% 34.55/34.78                           ( k1_zfmisc_1 @
% 34.55/34.78                             ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) ) ) =>
% 34.55/34.78                         ( ( r2_hidden @ E @ D ) <=>
% 34.55/34.78                           ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 34.55/34.78  thf('61', plain,
% 34.55/34.78      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X32 : $i, X33 : $i]:
% 34.55/34.78         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 34.55/34.78          | ~ (m1_subset_1 @ X29 @ 
% 34.55/34.78               (k1_zfmisc_1 @ 
% 34.55/34.78                (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X28 @ X27)))))
% 34.55/34.78          | ((X29) != (k1_tops_2 @ X28 @ X27 @ X30))
% 34.55/34.78          | (r2_hidden @ X32 @ X29)
% 34.55/34.78          | ~ (zip_tseitin_0 @ X33 @ X32 @ X30 @ X27 @ X28)
% 34.55/34.78          | ~ (m1_subset_1 @ X32 @ 
% 34.55/34.78               (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X28 @ X27))))
% 34.55/34.78          | ~ (m1_subset_1 @ X30 @ 
% 34.55/34.78               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28))))
% 34.55/34.78          | ~ (l1_pre_topc @ X28))),
% 34.55/34.78      inference('cnf', [status(esa)], [zf_stmt_3])).
% 34.55/34.78  thf('62', plain,
% 34.55/34.78      (![X27 : $i, X28 : $i, X30 : $i, X32 : $i, X33 : $i]:
% 34.55/34.78         (~ (l1_pre_topc @ X28)
% 34.55/34.78          | ~ (m1_subset_1 @ X30 @ 
% 34.55/34.78               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28))))
% 34.55/34.78          | ~ (m1_subset_1 @ X32 @ 
% 34.55/34.78               (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X28 @ X27))))
% 34.55/34.78          | ~ (zip_tseitin_0 @ X33 @ X32 @ X30 @ X27 @ X28)
% 34.55/34.78          | (r2_hidden @ X32 @ (k1_tops_2 @ X28 @ X27 @ X30))
% 34.55/34.78          | ~ (m1_subset_1 @ (k1_tops_2 @ X28 @ X27 @ X30) @ 
% 34.55/34.78               (k1_zfmisc_1 @ 
% 34.55/34.78                (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X28 @ X27)))))
% 34.55/34.78          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28))))),
% 34.55/34.78      inference('simplify', [status(thm)], ['61'])).
% 34.55/34.78  thf('63', plain,
% 34.55/34.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 34.55/34.78         (~ (m1_subset_1 @ 
% 34.55/34.78             (k1_tops_2 @ X0 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ X2) @ 
% 34.55/34.78             (k1_zfmisc_1 @ 
% 34.55/34.78              (k1_zfmisc_1 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)))))
% 34.55/34.78          | ~ (l1_pre_topc @ X0)
% 34.55/34.78          | ~ (m1_subset_1 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ 
% 34.55/34.78               (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 34.55/34.78          | (r2_hidden @ X3 @ 
% 34.55/34.78             (k1_tops_2 @ X0 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ X2))
% 34.55/34.78          | ~ (zip_tseitin_0 @ X4 @ X3 @ X2 @ 
% 34.55/34.78               (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ X0)
% 34.55/34.78          | ~ (m1_subset_1 @ X3 @ 
% 34.55/34.78               (k1_zfmisc_1 @ 
% 34.55/34.78                (u1_struct_0 @ 
% 34.55/34.78                 (k1_pre_topc @ X0 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0))))))
% 34.55/34.78          | ~ (m1_subset_1 @ X2 @ 
% 34.55/34.78               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 34.55/34.78          | ~ (l1_pre_topc @ X0))),
% 34.55/34.78      inference('sup-', [status(thm)], ['60', '62'])).
% 34.55/34.78  thf('64', plain,
% 34.55/34.78      (![X0 : $i, X1 : $i]:
% 34.55/34.78         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 34.55/34.78      inference('sup-', [status(thm)], ['56', '57'])).
% 34.55/34.78  thf('65', plain,
% 34.55/34.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 34.55/34.78         (~ (m1_subset_1 @ 
% 34.55/34.78             (k1_tops_2 @ X0 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ X2) @ 
% 34.55/34.78             (k1_zfmisc_1 @ 
% 34.55/34.78              (k1_zfmisc_1 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)))))
% 34.55/34.78          | ~ (l1_pre_topc @ X0)
% 34.55/34.78          | (r2_hidden @ X3 @ 
% 34.55/34.78             (k1_tops_2 @ X0 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ X2))
% 34.55/34.78          | ~ (zip_tseitin_0 @ X4 @ X3 @ X2 @ 
% 34.55/34.78               (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ X0)
% 34.55/34.78          | ~ (m1_subset_1 @ X3 @ 
% 34.55/34.78               (k1_zfmisc_1 @ 
% 34.55/34.78                (u1_struct_0 @ 
% 34.55/34.78                 (k1_pre_topc @ X0 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0))))))
% 34.55/34.78          | ~ (m1_subset_1 @ X2 @ 
% 34.55/34.78               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 34.55/34.78          | ~ (l1_pre_topc @ X0))),
% 34.55/34.78      inference('demod', [status(thm)], ['63', '64'])).
% 34.55/34.78  thf('66', plain,
% 34.55/34.78      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 34.55/34.78         (~ (m1_subset_1 @ X2 @ 
% 34.55/34.78             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 34.55/34.78          | ~ (m1_subset_1 @ X3 @ 
% 34.55/34.78               (k1_zfmisc_1 @ 
% 34.55/34.78                (u1_struct_0 @ 
% 34.55/34.78                 (k1_pre_topc @ X0 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0))))))
% 34.55/34.78          | ~ (zip_tseitin_0 @ X4 @ X3 @ X2 @ 
% 34.55/34.78               (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ X0)
% 34.55/34.78          | (r2_hidden @ X3 @ 
% 34.55/34.78             (k1_tops_2 @ X0 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ X2))
% 34.55/34.78          | ~ (l1_pre_topc @ X0)
% 34.55/34.78          | ~ (m1_subset_1 @ 
% 34.55/34.78               (k1_tops_2 @ X0 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ X2) @ 
% 34.55/34.78               (k1_zfmisc_1 @ 
% 34.55/34.78                (k1_zfmisc_1 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0))))))),
% 34.55/34.78      inference('simplify', [status(thm)], ['65'])).
% 34.55/34.78  thf('67', plain,
% 34.55/34.78      (![X0 : $i, X1 : $i]:
% 34.55/34.78         (~ (l1_pre_topc @ sk_A)
% 34.55/34.78          | (r2_hidden @ X0 @ 
% 34.55/34.78             (k1_tops_2 @ sk_A @ 
% 34.55/34.78              (k3_xboole_0 @ sk_C_1 @ (u1_struct_0 @ sk_A)) @ sk_D_1))
% 34.55/34.78          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_D_1 @ 
% 34.55/34.78               (k3_xboole_0 @ sk_C_1 @ (u1_struct_0 @ sk_A)) @ sk_A)
% 34.55/34.78          | ~ (m1_subset_1 @ X0 @ 
% 34.55/34.78               (k1_zfmisc_1 @ 
% 34.55/34.78                (u1_struct_0 @ 
% 34.55/34.78                 (k1_pre_topc @ sk_A @ 
% 34.55/34.78                  (k3_xboole_0 @ sk_C_1 @ (u1_struct_0 @ sk_A))))))
% 34.55/34.78          | ~ (m1_subset_1 @ sk_D_1 @ 
% 34.55/34.78               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 34.55/34.78      inference('sup-', [status(thm)], ['50', '66'])).
% 34.55/34.78  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 34.55/34.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.55/34.78  thf('69', plain,
% 34.55/34.78      (((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 34.55/34.78      inference('clc', [status(thm)], ['23', '24'])).
% 34.55/34.78  thf('70', plain,
% 34.55/34.78      (((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 34.55/34.78      inference('clc', [status(thm)], ['23', '24'])).
% 34.55/34.78  thf('71', plain,
% 34.55/34.78      (((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 34.55/34.78      inference('clc', [status(thm)], ['23', '24'])).
% 34.55/34.78  thf('72', plain,
% 34.55/34.78      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 34.55/34.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.55/34.78  thf('73', plain,
% 34.55/34.78      (![X19 : $i, X20 : $i]:
% 34.55/34.78         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 34.55/34.78          | ((u1_struct_0 @ (k1_pre_topc @ X20 @ X19)) = (X19))
% 34.55/34.78          | ~ (l1_pre_topc @ X20))),
% 34.55/34.78      inference('cnf', [status(esa)], [t29_pre_topc])).
% 34.55/34.78  thf('74', plain,
% 34.55/34.78      ((~ (l1_pre_topc @ sk_A)
% 34.55/34.78        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C_1)) = (sk_C_1)))),
% 34.55/34.78      inference('sup-', [status(thm)], ['72', '73'])).
% 34.55/34.78  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 34.55/34.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.55/34.78  thf('76', plain,
% 34.55/34.78      (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C_1)) = (sk_C_1))),
% 34.55/34.78      inference('demod', [status(thm)], ['74', '75'])).
% 34.55/34.78  thf('77', plain,
% 34.55/34.78      ((m1_subset_1 @ sk_D_1 @ 
% 34.55/34.78        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 34.55/34.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 34.55/34.78  thf('78', plain,
% 34.55/34.78      (![X0 : $i, X1 : $i]:
% 34.55/34.78         ((r2_hidden @ X0 @ (k1_tops_2 @ sk_A @ sk_C_1 @ sk_D_1))
% 34.55/34.78          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_D_1 @ sk_C_1 @ sk_A)
% 34.55/34.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_C_1)))),
% 34.55/34.78      inference('demod', [status(thm)],
% 34.55/34.78                ['67', '68', '69', '70', '71', '76', '77'])).
% 34.55/34.78  thf('79', plain,
% 34.55/34.78      ((~ (m1_subset_1 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ (k1_zfmisc_1 @ sk_C_1))
% 34.55/34.78        | (r2_hidden @ (k3_xboole_0 @ sk_B @ sk_C_1) @ 
% 34.55/34.78           (k1_tops_2 @ sk_A @ sk_C_1 @ sk_D_1)))),
% 34.55/34.78      inference('sup-', [status(thm)], ['12', '78'])).
% 34.55/34.78  thf('80', plain,
% 34.55/34.78      (![X0 : $i, X1 : $i]:
% 34.55/34.78         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 34.55/34.78      inference('sup-', [status(thm)], ['56', '57'])).
% 34.55/34.78  thf('81', plain,
% 34.55/34.78      ((r2_hidden @ (k3_xboole_0 @ sk_B @ sk_C_1) @ 
% 34.55/34.78        (k1_tops_2 @ sk_A @ sk_C_1 @ sk_D_1))),
% 34.55/34.78      inference('demod', [status(thm)], ['79', '80'])).
% 34.55/34.78  thf('82', plain, ($false), inference('demod', [status(thm)], ['4', '81'])).
% 34.55/34.78  
% 34.55/34.78  % SZS output end Refutation
% 34.55/34.78  
% 34.55/34.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
