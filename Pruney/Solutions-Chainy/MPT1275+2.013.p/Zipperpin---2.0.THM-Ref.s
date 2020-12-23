%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VDH1liTq1z

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:34 EST 2020

% Result     : Theorem 14.49s
% Output     : Refutation 14.49s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 298 expanded)
%              Number of leaves         :   32 (  97 expanded)
%              Depth                    :   14
%              Number of atoms          :  851 (3363 expanded)
%              Number of equality atoms :   46 ( 182 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t94_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( ( v3_tops_1 @ B @ A )
            <=> ( B
                = ( k2_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( ( v3_tops_1 @ B @ A )
              <=> ( B
                  = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t94_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_tops_1 @ A @ B )
            = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( ( k2_tops_1 @ X30 @ X29 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X30 ) @ ( k2_pre_topc @ X30 @ X29 ) @ ( k2_pre_topc @ X30 @ ( k3_subset_1 @ ( u1_struct_0 @ X30 ) @ X29 ) ) ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ~ ( v4_pre_topc @ X27 @ X28 )
      | ( ( k2_pre_topc @ X28 @ X27 )
        = X27 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X15 @ X16 )
        = ( k4_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3','9','12'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('16',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('23',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k9_subset_1 @ X19 @ X17 @ X18 )
        = ( k3_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X2 @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) )
        = ( k3_xboole_0 @ X2 @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['13','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k3_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t88_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('37',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( v2_tops_1 @ X33 @ X34 )
      | ( r1_tarski @ X33 @ ( k2_tops_1 @ X34 @ X33 ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('38',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('42',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v3_tops_1 @ X31 @ X32 )
      | ( v2_tops_1 @ ( k2_pre_topc @ X32 @ X31 ) @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('43',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('46',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
    | ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['46'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ~ ( r1_tarski @ X33 @ ( k2_tops_1 @ X34 @ X33 ) )
      | ( v2_tops_1 @ X33 @ X34 )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t88_tops_1])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['56','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v2_tops_1 @ ( k2_pre_topc @ X32 @ X31 ) @ X32 )
      | ( v3_tops_1 @ X31 @ X32 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_tops_1 @ sk_B @ sk_A )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('65',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
   <= ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf('67',plain,
    ( ~ ( v3_tops_1 @ sk_B @ sk_A )
   <= ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['48'])).

thf('68',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( v3_tops_1 @ sk_B @ sk_A )
    | ( sk_B
      = ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['46'])).

thf('70',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['49','68','69'])).

thf('71',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['47','70'])).

thf('72',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['43','44','45','71'])).

thf('73',plain,(
    r1_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['40','72'])).

thf('74',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('75',plain,
    ( sk_B
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['35','73','74'])).

thf('76',plain,
    ( ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( sk_B
     != ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['48'])).

thf('77',plain,(
    sk_B
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['49','68'])).

thf('78',plain,(
    sk_B
 != ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['76','77'])).

thf('79',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['75','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VDH1liTq1z
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:37:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 14.49/14.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 14.49/14.68  % Solved by: fo/fo7.sh
% 14.49/14.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.49/14.68  % done 19576 iterations in 14.212s
% 14.49/14.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 14.49/14.68  % SZS output start Refutation
% 14.49/14.68  thf(sk_A_type, type, sk_A: $i).
% 14.49/14.68  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 14.49/14.68  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 14.49/14.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 14.49/14.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 14.49/14.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 14.49/14.68  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 14.49/14.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 14.49/14.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 14.49/14.68  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 14.49/14.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 14.49/14.68  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 14.49/14.68  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 14.49/14.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 14.49/14.68  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 14.49/14.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 14.49/14.68  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 14.49/14.68  thf(sk_B_type, type, sk_B: $i).
% 14.49/14.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 14.49/14.68  thf(t94_tops_1, conjecture,
% 14.49/14.68    (![A:$i]:
% 14.49/14.68     ( ( l1_pre_topc @ A ) =>
% 14.49/14.68       ( ![B:$i]:
% 14.49/14.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 14.49/14.68           ( ( v4_pre_topc @ B @ A ) =>
% 14.49/14.68             ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 14.49/14.68  thf(zf_stmt_0, negated_conjecture,
% 14.49/14.68    (~( ![A:$i]:
% 14.49/14.68        ( ( l1_pre_topc @ A ) =>
% 14.49/14.68          ( ![B:$i]:
% 14.49/14.68            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 14.49/14.68              ( ( v4_pre_topc @ B @ A ) =>
% 14.49/14.68                ( ( v3_tops_1 @ B @ A ) <=> ( ( B ) = ( k2_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 14.49/14.68    inference('cnf.neg', [status(esa)], [t94_tops_1])).
% 14.49/14.68  thf('0', plain,
% 14.49/14.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.49/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.49/14.68  thf(d2_tops_1, axiom,
% 14.49/14.68    (![A:$i]:
% 14.49/14.68     ( ( l1_pre_topc @ A ) =>
% 14.49/14.68       ( ![B:$i]:
% 14.49/14.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 14.49/14.68           ( ( k2_tops_1 @ A @ B ) =
% 14.49/14.68             ( k9_subset_1 @
% 14.49/14.68               ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 14.49/14.68               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 14.49/14.68  thf('1', plain,
% 14.49/14.68      (![X29 : $i, X30 : $i]:
% 14.49/14.68         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 14.49/14.68          | ((k2_tops_1 @ X30 @ X29)
% 14.49/14.68              = (k9_subset_1 @ (u1_struct_0 @ X30) @ 
% 14.49/14.68                 (k2_pre_topc @ X30 @ X29) @ 
% 14.49/14.68                 (k2_pre_topc @ X30 @ (k3_subset_1 @ (u1_struct_0 @ X30) @ X29))))
% 14.49/14.68          | ~ (l1_pre_topc @ X30))),
% 14.49/14.68      inference('cnf', [status(esa)], [d2_tops_1])).
% 14.49/14.68  thf('2', plain,
% 14.49/14.68      ((~ (l1_pre_topc @ sk_A)
% 14.49/14.68        | ((k2_tops_1 @ sk_A @ sk_B)
% 14.49/14.68            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 14.49/14.68               (k2_pre_topc @ sk_A @ sk_B) @ 
% 14.49/14.68               (k2_pre_topc @ sk_A @ 
% 14.49/14.68                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 14.49/14.68      inference('sup-', [status(thm)], ['0', '1'])).
% 14.49/14.68  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 14.49/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.49/14.68  thf('4', plain,
% 14.49/14.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.49/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.49/14.68  thf(t52_pre_topc, axiom,
% 14.49/14.68    (![A:$i]:
% 14.49/14.68     ( ( l1_pre_topc @ A ) =>
% 14.49/14.68       ( ![B:$i]:
% 14.49/14.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 14.49/14.68           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 14.49/14.68             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 14.49/14.68               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 14.49/14.68  thf('5', plain,
% 14.49/14.68      (![X27 : $i, X28 : $i]:
% 14.49/14.68         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 14.49/14.68          | ~ (v4_pre_topc @ X27 @ X28)
% 14.49/14.68          | ((k2_pre_topc @ X28 @ X27) = (X27))
% 14.49/14.68          | ~ (l1_pre_topc @ X28))),
% 14.49/14.68      inference('cnf', [status(esa)], [t52_pre_topc])).
% 14.49/14.68  thf('6', plain,
% 14.49/14.68      ((~ (l1_pre_topc @ sk_A)
% 14.49/14.68        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 14.49/14.68        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 14.49/14.68      inference('sup-', [status(thm)], ['4', '5'])).
% 14.49/14.68  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 14.49/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.49/14.68  thf('8', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 14.49/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.49/14.68  thf('9', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 14.49/14.68      inference('demod', [status(thm)], ['6', '7', '8'])).
% 14.49/14.68  thf('10', plain,
% 14.49/14.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.49/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.49/14.68  thf(d5_subset_1, axiom,
% 14.49/14.68    (![A:$i,B:$i]:
% 14.49/14.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 14.49/14.68       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 14.49/14.68  thf('11', plain,
% 14.49/14.68      (![X15 : $i, X16 : $i]:
% 14.49/14.68         (((k3_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))
% 14.49/14.68          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 14.49/14.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 14.49/14.68  thf('12', plain,
% 14.49/14.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 14.49/14.68         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 14.49/14.68      inference('sup-', [status(thm)], ['10', '11'])).
% 14.49/14.68  thf('13', plain,
% 14.49/14.68      (((k2_tops_1 @ sk_A @ sk_B)
% 14.49/14.68         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 14.49/14.68            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 14.49/14.68      inference('demod', [status(thm)], ['2', '3', '9', '12'])).
% 14.49/14.68  thf(d3_tarski, axiom,
% 14.49/14.68    (![A:$i,B:$i]:
% 14.49/14.68     ( ( r1_tarski @ A @ B ) <=>
% 14.49/14.68       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 14.49/14.68  thf('14', plain,
% 14.49/14.68      (![X1 : $i, X3 : $i]:
% 14.49/14.68         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 14.49/14.68      inference('cnf', [status(esa)], [d3_tarski])).
% 14.49/14.68  thf(d5_xboole_0, axiom,
% 14.49/14.68    (![A:$i,B:$i,C:$i]:
% 14.49/14.68     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 14.49/14.68       ( ![D:$i]:
% 14.49/14.68         ( ( r2_hidden @ D @ C ) <=>
% 14.49/14.68           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 14.49/14.68  thf('15', plain,
% 14.49/14.68      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 14.49/14.68         (~ (r2_hidden @ X8 @ X7)
% 14.49/14.68          | (r2_hidden @ X8 @ X5)
% 14.49/14.68          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 14.49/14.68      inference('cnf', [status(esa)], [d5_xboole_0])).
% 14.49/14.68  thf('16', plain,
% 14.49/14.68      (![X5 : $i, X6 : $i, X8 : $i]:
% 14.49/14.68         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 14.49/14.68      inference('simplify', [status(thm)], ['15'])).
% 14.49/14.68  thf('17', plain,
% 14.49/14.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.49/14.68         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 14.49/14.68          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 14.49/14.68      inference('sup-', [status(thm)], ['14', '16'])).
% 14.49/14.68  thf('18', plain,
% 14.49/14.68      (![X1 : $i, X3 : $i]:
% 14.49/14.68         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 14.49/14.68      inference('cnf', [status(esa)], [d3_tarski])).
% 14.49/14.68  thf('19', plain,
% 14.49/14.68      (![X0 : $i, X1 : $i]:
% 14.49/14.68         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 14.49/14.68          | (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 14.49/14.68      inference('sup-', [status(thm)], ['17', '18'])).
% 14.49/14.68  thf('20', plain,
% 14.49/14.68      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 14.49/14.68      inference('simplify', [status(thm)], ['19'])).
% 14.49/14.68  thf(t3_subset, axiom,
% 14.49/14.68    (![A:$i,B:$i]:
% 14.49/14.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 14.49/14.68  thf('21', plain,
% 14.49/14.68      (![X22 : $i, X24 : $i]:
% 14.49/14.68         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 14.49/14.68      inference('cnf', [status(esa)], [t3_subset])).
% 14.49/14.68  thf('22', plain,
% 14.49/14.68      (![X0 : $i, X1 : $i]:
% 14.49/14.68         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 14.49/14.68      inference('sup-', [status(thm)], ['20', '21'])).
% 14.49/14.68  thf(dt_k2_pre_topc, axiom,
% 14.49/14.68    (![A:$i,B:$i]:
% 14.49/14.68     ( ( ( l1_pre_topc @ A ) & 
% 14.49/14.68         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 14.49/14.68       ( m1_subset_1 @
% 14.49/14.68         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 14.49/14.68  thf('23', plain,
% 14.49/14.68      (![X25 : $i, X26 : $i]:
% 14.49/14.68         (~ (l1_pre_topc @ X25)
% 14.49/14.68          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 14.49/14.68          | (m1_subset_1 @ (k2_pre_topc @ X25 @ X26) @ 
% 14.49/14.68             (k1_zfmisc_1 @ (u1_struct_0 @ X25))))),
% 14.49/14.68      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 14.49/14.68  thf('24', plain,
% 14.49/14.68      (![X0 : $i, X1 : $i]:
% 14.49/14.68         ((m1_subset_1 @ 
% 14.49/14.68           (k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 14.49/14.68           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 14.49/14.68          | ~ (l1_pre_topc @ X0))),
% 14.49/14.68      inference('sup-', [status(thm)], ['22', '23'])).
% 14.49/14.68  thf(redefinition_k9_subset_1, axiom,
% 14.49/14.68    (![A:$i,B:$i,C:$i]:
% 14.49/14.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 14.49/14.68       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 14.49/14.68  thf('25', plain,
% 14.49/14.68      (![X17 : $i, X18 : $i, X19 : $i]:
% 14.49/14.68         (((k9_subset_1 @ X19 @ X17 @ X18) = (k3_xboole_0 @ X17 @ X18))
% 14.49/14.68          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 14.49/14.68      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 14.49/14.68  thf('26', plain,
% 14.49/14.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.49/14.68         (~ (l1_pre_topc @ X0)
% 14.49/14.68          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ X2 @ 
% 14.49/14.68              (k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)))
% 14.49/14.68              = (k3_xboole_0 @ X2 @ 
% 14.49/14.68                 (k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)))))),
% 14.49/14.68      inference('sup-', [status(thm)], ['24', '25'])).
% 14.49/14.68  thf('27', plain,
% 14.49/14.68      ((((k2_tops_1 @ sk_A @ sk_B)
% 14.49/14.68          = (k3_xboole_0 @ sk_B @ 
% 14.49/14.68             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 14.49/14.68        | ~ (l1_pre_topc @ sk_A))),
% 14.49/14.68      inference('sup+', [status(thm)], ['13', '26'])).
% 14.49/14.68  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 14.49/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.49/14.68  thf('29', plain,
% 14.49/14.68      (((k2_tops_1 @ sk_A @ sk_B)
% 14.49/14.68         = (k3_xboole_0 @ sk_B @ 
% 14.49/14.68            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 14.49/14.68      inference('demod', [status(thm)], ['27', '28'])).
% 14.49/14.68  thf(t48_xboole_1, axiom,
% 14.49/14.68    (![A:$i,B:$i]:
% 14.49/14.68     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 14.49/14.68  thf('30', plain,
% 14.49/14.68      (![X13 : $i, X14 : $i]:
% 14.49/14.68         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 14.49/14.68           = (k3_xboole_0 @ X13 @ X14))),
% 14.49/14.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 14.49/14.68  thf('31', plain,
% 14.49/14.68      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 14.49/14.68      inference('simplify', [status(thm)], ['19'])).
% 14.49/14.68  thf('32', plain,
% 14.49/14.68      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 14.49/14.68      inference('sup+', [status(thm)], ['30', '31'])).
% 14.49/14.68  thf(d10_xboole_0, axiom,
% 14.49/14.68    (![A:$i,B:$i]:
% 14.49/14.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 14.49/14.68  thf('33', plain,
% 14.49/14.68      (![X10 : $i, X12 : $i]:
% 14.49/14.68         (((X10) = (X12))
% 14.49/14.68          | ~ (r1_tarski @ X12 @ X10)
% 14.49/14.68          | ~ (r1_tarski @ X10 @ X12))),
% 14.49/14.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 14.49/14.68  thf('34', plain,
% 14.49/14.68      (![X0 : $i, X1 : $i]:
% 14.49/14.68         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 14.49/14.68          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 14.49/14.68      inference('sup-', [status(thm)], ['32', '33'])).
% 14.49/14.68  thf('35', plain,
% 14.49/14.68      ((~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 14.49/14.68        | ((sk_B)
% 14.49/14.68            = (k3_xboole_0 @ sk_B @ 
% 14.49/14.68               (k2_pre_topc @ sk_A @ 
% 14.49/14.68                (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 14.49/14.68      inference('sup-', [status(thm)], ['29', '34'])).
% 14.49/14.68  thf('36', plain,
% 14.49/14.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.49/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.49/14.68  thf(t88_tops_1, axiom,
% 14.49/14.68    (![A:$i]:
% 14.49/14.68     ( ( l1_pre_topc @ A ) =>
% 14.49/14.68       ( ![B:$i]:
% 14.49/14.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 14.49/14.68           ( ( v2_tops_1 @ B @ A ) <=>
% 14.49/14.68             ( r1_tarski @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 14.49/14.68  thf('37', plain,
% 14.49/14.68      (![X33 : $i, X34 : $i]:
% 14.49/14.68         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 14.49/14.68          | ~ (v2_tops_1 @ X33 @ X34)
% 14.49/14.68          | (r1_tarski @ X33 @ (k2_tops_1 @ X34 @ X33))
% 14.49/14.68          | ~ (l1_pre_topc @ X34))),
% 14.49/14.68      inference('cnf', [status(esa)], [t88_tops_1])).
% 14.49/14.68  thf('38', plain,
% 14.49/14.68      ((~ (l1_pre_topc @ sk_A)
% 14.49/14.68        | (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 14.49/14.68        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 14.49/14.68      inference('sup-', [status(thm)], ['36', '37'])).
% 14.49/14.68  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 14.49/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.49/14.68  thf('40', plain,
% 14.49/14.68      (((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 14.49/14.68        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 14.49/14.68      inference('demod', [status(thm)], ['38', '39'])).
% 14.49/14.68  thf('41', plain,
% 14.49/14.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.49/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.49/14.68  thf(d5_tops_1, axiom,
% 14.49/14.68    (![A:$i]:
% 14.49/14.68     ( ( l1_pre_topc @ A ) =>
% 14.49/14.68       ( ![B:$i]:
% 14.49/14.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 14.49/14.68           ( ( v3_tops_1 @ B @ A ) <=>
% 14.49/14.68             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 14.49/14.68  thf('42', plain,
% 14.49/14.68      (![X31 : $i, X32 : $i]:
% 14.49/14.68         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 14.49/14.68          | ~ (v3_tops_1 @ X31 @ X32)
% 14.49/14.68          | (v2_tops_1 @ (k2_pre_topc @ X32 @ X31) @ X32)
% 14.49/14.68          | ~ (l1_pre_topc @ X32))),
% 14.49/14.68      inference('cnf', [status(esa)], [d5_tops_1])).
% 14.49/14.68  thf('43', plain,
% 14.49/14.68      ((~ (l1_pre_topc @ sk_A)
% 14.49/14.68        | (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 14.49/14.68        | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 14.49/14.68      inference('sup-', [status(thm)], ['41', '42'])).
% 14.49/14.68  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 14.49/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.49/14.68  thf('45', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 14.49/14.68      inference('demod', [status(thm)], ['6', '7', '8'])).
% 14.49/14.68  thf('46', plain,
% 14.49/14.68      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)) | (v3_tops_1 @ sk_B @ sk_A))),
% 14.49/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.49/14.68  thf('47', plain,
% 14.49/14.68      (((v3_tops_1 @ sk_B @ sk_A)) <= (((v3_tops_1 @ sk_B @ sk_A)))),
% 14.49/14.68      inference('split', [status(esa)], ['46'])).
% 14.49/14.68  thf('48', plain,
% 14.49/14.68      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)) | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 14.49/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.49/14.68  thf('49', plain,
% 14.49/14.68      (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))) | ~ ((v3_tops_1 @ sk_B @ sk_A))),
% 14.49/14.68      inference('split', [status(esa)], ['48'])).
% 14.49/14.68  thf('50', plain,
% 14.49/14.68      ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))
% 14.49/14.68         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 14.49/14.68      inference('split', [status(esa)], ['46'])).
% 14.49/14.68  thf('51', plain,
% 14.49/14.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.49/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.49/14.68  thf('52', plain,
% 14.49/14.68      (![X33 : $i, X34 : $i]:
% 14.49/14.68         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 14.49/14.68          | ~ (r1_tarski @ X33 @ (k2_tops_1 @ X34 @ X33))
% 14.49/14.68          | (v2_tops_1 @ X33 @ X34)
% 14.49/14.68          | ~ (l1_pre_topc @ X34))),
% 14.49/14.68      inference('cnf', [status(esa)], [t88_tops_1])).
% 14.49/14.68  thf('53', plain,
% 14.49/14.68      ((~ (l1_pre_topc @ sk_A)
% 14.49/14.68        | (v2_tops_1 @ sk_B @ sk_A)
% 14.49/14.68        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 14.49/14.68      inference('sup-', [status(thm)], ['51', '52'])).
% 14.49/14.68  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 14.49/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.49/14.68  thf('55', plain,
% 14.49/14.68      (((v2_tops_1 @ sk_B @ sk_A)
% 14.49/14.68        | ~ (r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 14.49/14.68      inference('demod', [status(thm)], ['53', '54'])).
% 14.49/14.68  thf('56', plain,
% 14.49/14.68      (((~ (r1_tarski @ sk_B @ sk_B) | (v2_tops_1 @ sk_B @ sk_A)))
% 14.49/14.68         <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 14.49/14.68      inference('sup-', [status(thm)], ['50', '55'])).
% 14.49/14.68  thf('57', plain,
% 14.49/14.68      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 14.49/14.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 14.49/14.68  thf('58', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 14.49/14.68      inference('simplify', [status(thm)], ['57'])).
% 14.49/14.68  thf('59', plain,
% 14.49/14.68      (((v2_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 14.49/14.68      inference('demod', [status(thm)], ['56', '58'])).
% 14.49/14.68  thf('60', plain,
% 14.49/14.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 14.49/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.49/14.68  thf('61', plain,
% 14.49/14.68      (![X31 : $i, X32 : $i]:
% 14.49/14.68         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 14.49/14.68          | ~ (v2_tops_1 @ (k2_pre_topc @ X32 @ X31) @ X32)
% 14.49/14.68          | (v3_tops_1 @ X31 @ X32)
% 14.49/14.68          | ~ (l1_pre_topc @ X32))),
% 14.49/14.68      inference('cnf', [status(esa)], [d5_tops_1])).
% 14.49/14.68  thf('62', plain,
% 14.49/14.68      ((~ (l1_pre_topc @ sk_A)
% 14.49/14.68        | (v3_tops_1 @ sk_B @ sk_A)
% 14.49/14.68        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 14.49/14.68      inference('sup-', [status(thm)], ['60', '61'])).
% 14.49/14.68  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 14.49/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.49/14.68  thf('64', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 14.49/14.68      inference('demod', [status(thm)], ['6', '7', '8'])).
% 14.49/14.68  thf('65', plain, (((v3_tops_1 @ sk_B @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 14.49/14.68      inference('demod', [status(thm)], ['62', '63', '64'])).
% 14.49/14.68  thf('66', plain,
% 14.49/14.68      (((v3_tops_1 @ sk_B @ sk_A)) <= ((((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 14.49/14.68      inference('sup-', [status(thm)], ['59', '65'])).
% 14.49/14.68  thf('67', plain,
% 14.49/14.68      ((~ (v3_tops_1 @ sk_B @ sk_A)) <= (~ ((v3_tops_1 @ sk_B @ sk_A)))),
% 14.49/14.68      inference('split', [status(esa)], ['48'])).
% 14.49/14.68  thf('68', plain,
% 14.49/14.68      (((v3_tops_1 @ sk_B @ sk_A)) | ~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 14.49/14.68      inference('sup-', [status(thm)], ['66', '67'])).
% 14.49/14.68  thf('69', plain,
% 14.49/14.68      (((v3_tops_1 @ sk_B @ sk_A)) | (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 14.49/14.68      inference('split', [status(esa)], ['46'])).
% 14.49/14.68  thf('70', plain, (((v3_tops_1 @ sk_B @ sk_A))),
% 14.49/14.68      inference('sat_resolution*', [status(thm)], ['49', '68', '69'])).
% 14.49/14.68  thf('71', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 14.49/14.68      inference('simpl_trail', [status(thm)], ['47', '70'])).
% 14.49/14.68  thf('72', plain, ((v2_tops_1 @ sk_B @ sk_A)),
% 14.49/14.68      inference('demod', [status(thm)], ['43', '44', '45', '71'])).
% 14.49/14.68  thf('73', plain, ((r1_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))),
% 14.49/14.68      inference('demod', [status(thm)], ['40', '72'])).
% 14.49/14.68  thf('74', plain,
% 14.49/14.68      (((k2_tops_1 @ sk_A @ sk_B)
% 14.49/14.68         = (k3_xboole_0 @ sk_B @ 
% 14.49/14.68            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 14.49/14.68      inference('demod', [status(thm)], ['27', '28'])).
% 14.49/14.68  thf('75', plain, (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))),
% 14.49/14.68      inference('demod', [status(thm)], ['35', '73', '74'])).
% 14.49/14.68  thf('76', plain,
% 14.49/14.68      ((((sk_B) != (k2_tops_1 @ sk_A @ sk_B)))
% 14.49/14.68         <= (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B))))),
% 14.49/14.68      inference('split', [status(esa)], ['48'])).
% 14.49/14.68  thf('77', plain, (~ (((sk_B) = (k2_tops_1 @ sk_A @ sk_B)))),
% 14.49/14.68      inference('sat_resolution*', [status(thm)], ['49', '68'])).
% 14.49/14.68  thf('78', plain, (((sk_B) != (k2_tops_1 @ sk_A @ sk_B))),
% 14.49/14.68      inference('simpl_trail', [status(thm)], ['76', '77'])).
% 14.49/14.68  thf('79', plain, ($false),
% 14.49/14.68      inference('simplify_reflect-', [status(thm)], ['75', '78'])).
% 14.49/14.68  
% 14.49/14.68  % SZS output end Refutation
% 14.49/14.68  
% 14.49/14.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
