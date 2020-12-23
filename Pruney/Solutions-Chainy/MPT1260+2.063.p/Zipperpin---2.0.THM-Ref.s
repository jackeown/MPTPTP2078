%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WAmLn97j8e

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 312 expanded)
%              Number of leaves         :   33 ( 100 expanded)
%              Depth                    :   20
%              Number of atoms          : 1148 (4056 expanded)
%              Number of equality atoms :   73 ( 231 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t76_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l78_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k1_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( ( k2_tops_1 @ X31 @ X30 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X31 ) @ ( k2_pre_topc @ X31 @ X30 ) @ ( k1_tops_1 @ X31 @ X30 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[l78_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k7_subset_1 @ X22 @ X21 @ X23 )
        = ( k4_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t56_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r1_tarski @ B @ C ) )
               => ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( v3_pre_topc @ X32 @ X33 )
      | ~ ( r1_tarski @ X32 @ X34 )
      | ( r1_tarski @ X32 @ ( k1_tops_1 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t56_tops_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_B @ X0 )
        | ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_B @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('23',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tarski @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['21','24'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('29',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k1_tops_1 @ X36 @ X35 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X36 ) @ X35 @ ( k2_tops_1 @ X36 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ( ( k7_subset_1 @ X22 @ X21 @ X23 )
        = ( k4_xboole_0 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31','34'])).

thf('36',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('37',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['27','37'])).

thf('39',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31','34'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('42',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('43',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('44',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('45',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('46',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('51',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf('52',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0
          = ( k3_xboole_0 @ X0 @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
        | ~ ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,
    ( ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','55'])).

thf('57',plain,
    ( ( ( k1_xboole_0
        = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['47'])).

thf('59',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('60',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('61',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('62',plain,(
    ! [X17: $i] :
      ( ( k3_xboole_0 @ X17 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('63',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','66'])).

thf('68',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['41','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('70',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X28 @ X29 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('71',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['68','74'])).

thf('76',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['39'])).

thf('77',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf('79',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['40','77','78'])).

thf('80',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['38','79'])).

thf('81',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['11','80'])).

thf('82',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(split,[status(esa)],['39'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('84',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['40','77'])).

thf('86',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['84','85'])).

thf('87',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['81','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WAmLn97j8e
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:27:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 228 iterations in 0.099s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 0.21/0.54  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(t76_tops_1, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ( v3_pre_topc @ B @ A ) <=>
% 0.21/0.54             ( ( k2_tops_1 @ A @ B ) =
% 0.21/0.54               ( k7_subset_1 @
% 0.21/0.54                 ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54              ( ( v3_pre_topc @ B @ A ) <=>
% 0.21/0.54                ( ( k2_tops_1 @ A @ B ) =
% 0.21/0.54                  ( k7_subset_1 @
% 0.21/0.54                    ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ B ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t76_tops_1])).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(l78_tops_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( l1_pre_topc @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.54           ( ( k2_tops_1 @ A @ B ) =
% 0.21/0.54             ( k7_subset_1 @
% 0.21/0.54               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.21/0.54               ( k1_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (![X30 : $i, X31 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.21/0.54          | ((k2_tops_1 @ X31 @ X30)
% 0.21/0.54              = (k7_subset_1 @ (u1_struct_0 @ X31) @ 
% 0.21/0.54                 (k2_pre_topc @ X31 @ X30) @ (k1_tops_1 @ X31 @ X30)))
% 0.21/0.54          | ~ (l1_pre_topc @ X31))),
% 0.21/0.54      inference('cnf', [status(esa)], [l78_tops_1])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.54        | ((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.54            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.54               (k2_pre_topc @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.54  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(dt_k2_pre_topc, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.54       ( m1_subset_1 @
% 0.21/0.54         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X26 : $i, X27 : $i]:
% 0.21/0.54         (~ (l1_pre_topc @ X26)
% 0.21/0.54          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.21/0.54          | (m1_subset_1 @ (k2_pre_topc @ X26 @ X27) @ 
% 0.21/0.54             (k1_zfmisc_1 @ (u1_struct_0 @ X26))))),
% 0.21/0.54      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.54         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.54        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.55  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.55  thf(redefinition_k7_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.21/0.55          | ((k7_subset_1 @ X22 @ X21 @ X23) = (k4_xboole_0 @ X21 @ X23)))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.55           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.55            (k1_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('demod', [status(thm)], ['2', '3', '10'])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.21/0.55        | (v3_pre_topc @ sk_B @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (((v3_pre_topc @ sk_B @ sk_A)) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['13'])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t56_tops_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_pre_topc @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55           ( ![C:$i]:
% 0.21/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55               ( ( ( v3_pre_topc @ B @ A ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.55                 ( r1_tarski @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.21/0.55          | ~ (v3_pre_topc @ X32 @ X33)
% 0.21/0.55          | ~ (r1_tarski @ X32 @ X34)
% 0.21/0.55          | (r1_tarski @ X32 @ (k1_tops_1 @ X33 @ X34))
% 0.21/0.55          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.21/0.55          | ~ (l1_pre_topc @ X33))),
% 0.21/0.55      inference('cnf', [status(esa)], [t56_tops_1])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ sk_A)
% 0.21/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.55          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.55          | ~ (r1_tarski @ sk_B @ X0)
% 0.21/0.55          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.55  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.55          | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.55          | ~ (r1_tarski @ sk_B @ X0)
% 0.21/0.55          | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.21/0.55      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.55  thf('20', plain,
% 0.21/0.55      ((![X0 : $i]:
% 0.21/0.55          (~ (r1_tarski @ sk_B @ X0)
% 0.21/0.55           | (r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.55           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.21/0.55         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['14', '19'])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      ((((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 0.21/0.55         | ~ (r1_tarski @ sk_B @ sk_B))) <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['12', '20'])).
% 0.21/0.55  thf(t3_boole, axiom,
% 0.21/0.55    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.55  thf('22', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.55  thf(t36_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 0.21/0.55      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.55  thf('24', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.55      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      (((r1_tarski @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.21/0.55         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['21', '24'])).
% 0.21/0.55  thf(d10_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      (![X12 : $i, X14 : $i]:
% 0.21/0.55         (((X12) = (X14))
% 0.21/0.55          | ~ (r1_tarski @ X14 @ X12)
% 0.21/0.55          | ~ (r1_tarski @ X12 @ X14))),
% 0.21/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.21/0.55         | ((k1_tops_1 @ sk_A @ sk_B) = (sk_B))))
% 0.21/0.55         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(t74_tops_1, axiom,
% 0.21/0.55    (![A:$i]:
% 0.21/0.55     ( ( l1_pre_topc @ A ) =>
% 0.21/0.55       ( ![B:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.55           ( ( k1_tops_1 @ A @ B ) =
% 0.21/0.55             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      (![X35 : $i, X36 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.21/0.55          | ((k1_tops_1 @ X36 @ X35)
% 0.21/0.55              = (k7_subset_1 @ (u1_struct_0 @ X36) @ X35 @ 
% 0.21/0.55                 (k2_tops_1 @ X36 @ X35)))
% 0.21/0.55          | ~ (l1_pre_topc @ X36))),
% 0.21/0.55      inference('cnf', [status(esa)], [t74_tops_1])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.55        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.21/0.55            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.21/0.55               (k2_tops_1 @ sk_A @ sk_B))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.55  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('33', plain,
% 0.21/0.55      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.21/0.55          | ((k7_subset_1 @ X22 @ X21 @ X23) = (k4_xboole_0 @ X21 @ X23)))),
% 0.21/0.55      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.21/0.55  thf('34', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 0.21/0.55           = (k4_xboole_0 @ sk_B @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.55  thf('35', plain,
% 0.21/0.55      (((k1_tops_1 @ sk_A @ sk_B)
% 0.21/0.55         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('demod', [status(thm)], ['30', '31', '34'])).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 0.21/0.55      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.55  thf('37', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.21/0.55      inference('sup+', [status(thm)], ['35', '36'])).
% 0.21/0.55  thf('38', plain,
% 0.21/0.55      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 0.21/0.55         <= (((v3_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.55      inference('demod', [status(thm)], ['27', '37'])).
% 0.21/0.55  thf('39', plain,
% 0.21/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55              (k2_pre_topc @ sk_A @ sk_B) @ sk_B))
% 0.21/0.55        | ~ (v3_pre_topc @ sk_B @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('40', plain,
% 0.21/0.55      (~
% 0.21/0.55       (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55             (k2_pre_topc @ sk_A @ sk_B) @ sk_B))) | 
% 0.21/0.55       ~ ((v3_pre_topc @ sk_B @ sk_A))),
% 0.21/0.55      inference('split', [status(esa)], ['39'])).
% 0.21/0.55  thf('41', plain,
% 0.21/0.55      (((k1_tops_1 @ sk_A @ sk_B)
% 0.21/0.55         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 0.21/0.55      inference('demod', [status(thm)], ['30', '31', '34'])).
% 0.21/0.55  thf(d4_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.21/0.55       ( ![D:$i]:
% 0.21/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.55           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.55  thf('42', plain,
% 0.21/0.55      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.21/0.55         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.21/0.55          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.21/0.55          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.21/0.55         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.21/0.55          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.21/0.55          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.21/0.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.55  thf('44', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.55  thf(d5_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.55       ( ![D:$i]:
% 0.21/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.55           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.55  thf('45', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X10 @ X9)
% 0.21/0.55          | ~ (r2_hidden @ X10 @ X8)
% 0.21/0.55          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.55  thf('46', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X10 @ X8)
% 0.21/0.55          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.55  thf('47', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['44', '46'])).
% 0.21/0.55  thf('48', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.55      inference('condensation', [status(thm)], ['47'])).
% 0.21/0.55  thf('49', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.21/0.55          | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['43', '48'])).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.55           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.55  thf('51', plain,
% 0.21/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.21/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.55      inference('split', [status(esa)], ['13'])).
% 0.21/0.55  thf('52', plain,
% 0.21/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55          = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.21/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['50', '51'])).
% 0.21/0.55  thf('53', plain,
% 0.21/0.55      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X10 @ X8)
% 0.21/0.55          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.55  thf('54', plain,
% 0.21/0.55      ((![X0 : $i]:
% 0.21/0.55          (~ (r2_hidden @ X0 @ (k2_tops_1 @ sk_A @ sk_B))
% 0.21/0.55           | ~ (r2_hidden @ X0 @ sk_B)))
% 0.21/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.55  thf('55', plain,
% 0.21/0.55      ((![X0 : $i]:
% 0.21/0.55          (((k1_xboole_0) = (k3_xboole_0 @ X0 @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.21/0.55           | ~ (r2_hidden @ 
% 0.21/0.55                (sk_D @ k1_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ X0) @ sk_B)))
% 0.21/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['49', '54'])).
% 0.21/0.55  thf('56', plain,
% 0.21/0.55      ((((r2_hidden @ 
% 0.21/0.55          (sk_D @ k1_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ k1_xboole_0)
% 0.21/0.55         | ((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.21/0.55         | ((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))))
% 0.21/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['42', '55'])).
% 0.21/0.55  thf('57', plain,
% 0.21/0.55      (((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 0.21/0.55         | (r2_hidden @ 
% 0.21/0.55            (sk_D @ k1_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ 
% 0.21/0.55            k1_xboole_0)))
% 0.21/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.55      inference('simplify', [status(thm)], ['56'])).
% 0.21/0.55  thf('58', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.55      inference('condensation', [status(thm)], ['47'])).
% 0.21/0.55  thf('59', plain,
% 0.21/0.55      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 0.21/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.55      inference('clc', [status(thm)], ['57', '58'])).
% 0.21/0.55  thf(t100_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.55  thf('60', plain,
% 0.21/0.55      (![X15 : $i, X16 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X15 @ X16)
% 0.21/0.55           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.55  thf('61', plain,
% 0.21/0.55      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 0.21/0.55          = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.21/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['59', '60'])).
% 0.21/0.55  thf(t2_boole, axiom,
% 0.21/0.55    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.55  thf('62', plain,
% 0.21/0.55      (![X17 : $i]: ((k3_xboole_0 @ X17 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.55      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.55  thf('63', plain,
% 0.21/0.55      (![X15 : $i, X16 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X15 @ X16)
% 0.21/0.55           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.55  thf('64', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['62', '63'])).
% 0.21/0.55  thf('65', plain, (![X20 : $i]: ((k4_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.55  thf('66', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.21/0.55      inference('sup+', [status(thm)], ['64', '65'])).
% 0.21/0.55  thf('67', plain,
% 0.21/0.55      ((((k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 0.21/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.55      inference('demod', [status(thm)], ['61', '66'])).
% 0.21/0.55  thf('68', plain,
% 0.21/0.55      ((((k1_tops_1 @ sk_A @ sk_B) = (sk_B)))
% 0.21/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['41', '67'])).
% 0.21/0.55  thf('69', plain,
% 0.21/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(fc9_tops_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.21/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.55       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.21/0.55  thf('70', plain,
% 0.21/0.55      (![X28 : $i, X29 : $i]:
% 0.21/0.55         (~ (l1_pre_topc @ X28)
% 0.21/0.55          | ~ (v2_pre_topc @ X28)
% 0.21/0.55          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.21/0.55          | (v3_pre_topc @ (k1_tops_1 @ X28 @ X29) @ X28))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.21/0.55  thf('71', plain,
% 0.21/0.55      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.55      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.55  thf('72', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('74', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.55      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.21/0.55  thf('75', plain,
% 0.21/0.55      (((v3_pre_topc @ sk_B @ sk_A))
% 0.21/0.55         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.55      inference('sup+', [status(thm)], ['68', '74'])).
% 0.21/0.55  thf('76', plain,
% 0.21/0.55      ((~ (v3_pre_topc @ sk_B @ sk_A)) <= (~ ((v3_pre_topc @ sk_B @ sk_A)))),
% 0.21/0.55      inference('split', [status(esa)], ['39'])).
% 0.21/0.55  thf('77', plain,
% 0.21/0.55      (((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.21/0.55       ~
% 0.21/0.55       (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.55  thf('78', plain,
% 0.21/0.55      (((v3_pre_topc @ sk_B @ sk_A)) | 
% 0.21/0.55       (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.21/0.55      inference('split', [status(esa)], ['13'])).
% 0.21/0.55  thf('79', plain, (((v3_pre_topc @ sk_B @ sk_A))),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['40', '77', '78'])).
% 0.21/0.55  thf('80', plain, (((k1_tops_1 @ sk_A @ sk_B) = (sk_B))),
% 0.21/0.55      inference('simpl_trail', [status(thm)], ['38', '79'])).
% 0.21/0.55  thf('81', plain,
% 0.21/0.55      (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55         = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 0.21/0.55      inference('demod', [status(thm)], ['11', '80'])).
% 0.21/0.55  thf('82', plain,
% 0.21/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55              (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.21/0.55         <= (~
% 0.21/0.55             (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.55      inference('split', [status(esa)], ['39'])).
% 0.21/0.55  thf('83', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.55           X0) = (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.55  thf('84', plain,
% 0.21/0.55      ((((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55          != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))
% 0.21/0.55         <= (~
% 0.21/0.55             (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55                   (k2_pre_topc @ sk_A @ sk_B) @ sk_B))))),
% 0.21/0.55      inference('demod', [status(thm)], ['82', '83'])).
% 0.21/0.55  thf('85', plain,
% 0.21/0.55      (~
% 0.21/0.55       (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.55             (k2_pre_topc @ sk_A @ sk_B) @ sk_B)))),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['40', '77'])).
% 0.21/0.55  thf('86', plain,
% 0.21/0.55      (((k2_tops_1 @ sk_A @ sk_B)
% 0.21/0.55         != (k4_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 0.21/0.55      inference('simpl_trail', [status(thm)], ['84', '85'])).
% 0.21/0.55  thf('87', plain, ($false),
% 0.21/0.55      inference('simplify_reflect-', [status(thm)], ['81', '86'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
