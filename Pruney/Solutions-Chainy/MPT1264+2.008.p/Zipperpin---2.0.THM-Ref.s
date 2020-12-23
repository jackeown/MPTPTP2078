%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TrtHa4hSRM

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:08 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 184 expanded)
%              Number of leaves         :   27 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :  850 (2477 expanded)
%              Number of equality atoms :   58 ( 123 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(t81_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( v3_pre_topc @ C @ A )
                 => ( ( k2_pre_topc @ A @ C )
                    = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v1_tops_1 @ B @ A )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( v3_pre_topc @ C @ A )
                   => ( ( k2_pre_topc @ A @ C )
                      = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( v3_pre_topc @ B @ A )
               => ( ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) )
                  = ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X20 )
      | ( ( k2_pre_topc @ X20 @ ( k9_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 @ ( k2_pre_topc @ X20 @ X21 ) ) )
        = ( k2_pre_topc @ X20 @ ( k9_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t41_tops_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k2_pre_topc @ sk_A @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X6 @ X8 @ X7 )
        = ( k9_subset_1 @ X6 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_C ) )
        = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['7','14','15'])).

thf('17',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_C ) )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v1_tops_1 @ X17 @ X18 )
      | ( ( k2_pre_topc @ X18 @ X17 )
        = ( k2_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('24',plain,(
    ! [X15: $i] :
      ( ( ( k2_struct_0 @ X15 )
        = ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('28',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('29',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X6 @ X8 @ X7 )
        = ( k9_subset_1 @ X6 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k9_subset_1 @ X0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('40',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_subset_1 @ X0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    = ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_C ) ),
    inference('sup+',[status(thm)],['32','42'])).

thf('44',plain,(
    ! [X15: $i] :
      ( ( ( k2_struct_0 @ X15 )
        = ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t20_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ! [D: $i] :
            ( ( ( r1_tarski @ D @ B )
              & ( r1_tarski @ D @ C ) )
           => ( r1_tarski @ D @ A ) ) )
     => ( A
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('49',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ( r1_tarski @ ( sk_D @ X5 @ X4 @ X3 ) @ X4 )
      | ( X3
        = ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( sk_D @ X1 @ X0 @ X0 ) @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C ) @ sk_C )
    | ( sk_C
      = ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ~ ( r1_tarski @ ( sk_D @ X5 @ X4 @ X3 ) @ X3 )
      | ( X3
        = ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('53',plain,
    ( ( sk_C
      = ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_C
      = ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('55',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('56',plain,
    ( ( sk_C
      = ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_C
      = ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( sk_C
      = ( k3_xboole_0 @ sk_C @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['44','57'])).

thf('59',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['27','28'])).

thf('60',plain,
    ( sk_C
    = ( k3_xboole_0 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( sk_C
    = ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['43','60'])).

thf('62',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['17','23','61'])).

thf('63',plain,(
    ( k2_pre_topc @ sk_A @ sk_C )
 != ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X11 @ X9 @ X10 )
        = ( k3_xboole_0 @ X9 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ( k2_pre_topc @ sk_A @ sk_C )
 != ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X6 @ X8 @ X7 )
        = ( k9_subset_1 @ X6 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('74',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ( k2_pre_topc @ sk_A @ sk_C )
 != ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['67','74'])).

thf('76',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['62','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TrtHa4hSRM
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:27:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.53/0.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.75  % Solved by: fo/fo7.sh
% 0.53/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.75  % done 372 iterations in 0.269s
% 0.53/0.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.75  % SZS output start Refutation
% 0.53/0.75  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.53/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.75  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.53/0.75  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.53/0.75  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.53/0.75  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.53/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.75  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.53/0.75  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.53/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.75  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.53/0.75  thf(sk_C_type, type, sk_C: $i).
% 0.53/0.75  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.53/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.75  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.53/0.75  thf(t81_tops_1, conjecture,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.75       ( ![B:$i]:
% 0.53/0.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.75           ( ( v1_tops_1 @ B @ A ) =>
% 0.53/0.75             ( ![C:$i]:
% 0.53/0.75               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.75                 ( ( v3_pre_topc @ C @ A ) =>
% 0.53/0.75                   ( ( k2_pre_topc @ A @ C ) =
% 0.53/0.75                     ( k2_pre_topc @
% 0.53/0.75                       A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ))).
% 0.53/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.75    (~( ![A:$i]:
% 0.53/0.75        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.75          ( ![B:$i]:
% 0.53/0.75            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.75              ( ( v1_tops_1 @ B @ A ) =>
% 0.53/0.75                ( ![C:$i]:
% 0.53/0.75                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.75                    ( ( v3_pre_topc @ C @ A ) =>
% 0.53/0.75                      ( ( k2_pre_topc @ A @ C ) =
% 0.53/0.75                        ( k2_pre_topc @
% 0.53/0.75                          A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.53/0.75    inference('cnf.neg', [status(esa)], [t81_tops_1])).
% 0.53/0.75  thf('0', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('1', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(t41_tops_1, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.75       ( ![B:$i]:
% 0.53/0.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.75           ( ![C:$i]:
% 0.53/0.75             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.75               ( ( v3_pre_topc @ B @ A ) =>
% 0.53/0.75                 ( ( k2_pre_topc @
% 0.53/0.75                     A @ 
% 0.53/0.75                     ( k9_subset_1 @
% 0.53/0.75                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) ) =
% 0.53/0.75                   ( k2_pre_topc @
% 0.53/0.75                     A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.53/0.75  thf('2', plain,
% 0.53/0.75      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.53/0.75         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.53/0.75          | ~ (v3_pre_topc @ X19 @ X20)
% 0.53/0.75          | ((k2_pre_topc @ X20 @ 
% 0.53/0.75              (k9_subset_1 @ (u1_struct_0 @ X20) @ X19 @ 
% 0.53/0.75               (k2_pre_topc @ X20 @ X21)))
% 0.53/0.75              = (k2_pre_topc @ X20 @ 
% 0.53/0.75                 (k9_subset_1 @ (u1_struct_0 @ X20) @ X19 @ X21)))
% 0.53/0.75          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.53/0.75          | ~ (l1_pre_topc @ X20)
% 0.53/0.75          | ~ (v2_pre_topc @ X20))),
% 0.53/0.75      inference('cnf', [status(esa)], [t41_tops_1])).
% 0.53/0.75  thf('3', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (v2_pre_topc @ sk_A)
% 0.53/0.75          | ~ (l1_pre_topc @ sk_A)
% 0.53/0.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.53/0.75          | ((k2_pre_topc @ sk_A @ 
% 0.53/0.75              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.53/0.75               (k2_pre_topc @ sk_A @ X0)))
% 0.53/0.75              = (k2_pre_topc @ sk_A @ 
% 0.53/0.75                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)))
% 0.53/0.75          | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['1', '2'])).
% 0.53/0.75  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('6', plain, ((v3_pre_topc @ sk_C @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('7', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.53/0.75          | ((k2_pre_topc @ sk_A @ 
% 0.53/0.75              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 0.53/0.75               (k2_pre_topc @ sk_A @ X0)))
% 0.53/0.75              = (k2_pre_topc @ sk_A @ 
% 0.53/0.75                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))))),
% 0.53/0.75      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.53/0.75  thf('8', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(commutativity_k9_subset_1, axiom,
% 0.53/0.75    (![A:$i,B:$i,C:$i]:
% 0.53/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.75       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.53/0.75  thf('9', plain,
% 0.53/0.75      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.53/0.75         (((k9_subset_1 @ X6 @ X8 @ X7) = (k9_subset_1 @ X6 @ X7 @ X8))
% 0.53/0.75          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.53/0.75      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.53/0.75  thf('10', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.53/0.75           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['8', '9'])).
% 0.53/0.75  thf('11', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(redefinition_k9_subset_1, axiom,
% 0.53/0.75    (![A:$i,B:$i,C:$i]:
% 0.53/0.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.75       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.53/0.75  thf('12', plain,
% 0.53/0.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.53/0.75         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.53/0.75          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.53/0.75      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.53/0.75  thf('13', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.53/0.75           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.53/0.75      inference('sup-', [status(thm)], ['11', '12'])).
% 0.53/0.75  thf('14', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((k3_xboole_0 @ X0 @ sk_C)
% 0.53/0.75           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.53/0.75      inference('demod', [status(thm)], ['10', '13'])).
% 0.53/0.75  thf('15', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((k3_xboole_0 @ X0 @ sk_C)
% 0.53/0.75           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.53/0.75      inference('demod', [status(thm)], ['10', '13'])).
% 0.53/0.75  thf('16', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.53/0.75          | ((k2_pre_topc @ sk_A @ 
% 0.53/0.75              (k3_xboole_0 @ (k2_pre_topc @ sk_A @ X0) @ sk_C))
% 0.53/0.75              = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C))))),
% 0.53/0.75      inference('demod', [status(thm)], ['7', '14', '15'])).
% 0.53/0.75  thf('17', plain,
% 0.53/0.75      (((k2_pre_topc @ sk_A @ 
% 0.53/0.75         (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_C))
% 0.53/0.75         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['0', '16'])).
% 0.53/0.75  thf('18', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(d3_tops_1, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( l1_pre_topc @ A ) =>
% 0.53/0.75       ( ![B:$i]:
% 0.53/0.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.75           ( ( v1_tops_1 @ B @ A ) <=>
% 0.53/0.75             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.53/0.75  thf('19', plain,
% 0.53/0.75      (![X17 : $i, X18 : $i]:
% 0.53/0.75         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.53/0.75          | ~ (v1_tops_1 @ X17 @ X18)
% 0.53/0.75          | ((k2_pre_topc @ X18 @ X17) = (k2_struct_0 @ X18))
% 0.53/0.75          | ~ (l1_pre_topc @ X18))),
% 0.53/0.75      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.53/0.75  thf('20', plain,
% 0.53/0.75      ((~ (l1_pre_topc @ sk_A)
% 0.53/0.75        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 0.53/0.75        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['18', '19'])).
% 0.53/0.75  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('22', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('23', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.53/0.75      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.53/0.75  thf(d3_struct_0, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.53/0.75  thf('24', plain,
% 0.53/0.75      (![X15 : $i]:
% 0.53/0.75         (((k2_struct_0 @ X15) = (u1_struct_0 @ X15)) | ~ (l1_struct_0 @ X15))),
% 0.53/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.53/0.75  thf('25', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('26', plain,
% 0.53/0.75      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.53/0.75        | ~ (l1_struct_0 @ sk_A))),
% 0.53/0.75      inference('sup+', [status(thm)], ['24', '25'])).
% 0.53/0.75  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(dt_l1_pre_topc, axiom,
% 0.53/0.75    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.53/0.75  thf('28', plain,
% 0.53/0.75      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.53/0.75      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.53/0.75  thf('29', plain, ((l1_struct_0 @ sk_A)),
% 0.53/0.75      inference('sup-', [status(thm)], ['27', '28'])).
% 0.53/0.75  thf('30', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.53/0.75      inference('demod', [status(thm)], ['26', '29'])).
% 0.53/0.75  thf('31', plain,
% 0.53/0.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.53/0.75         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.53/0.75          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.53/0.75      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.53/0.75  thf('32', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.53/0.75           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.53/0.75      inference('sup-', [status(thm)], ['30', '31'])).
% 0.53/0.75  thf(d10_xboole_0, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.53/0.75  thf('33', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.53/0.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.75  thf('34', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.53/0.75      inference('simplify', [status(thm)], ['33'])).
% 0.53/0.75  thf(t3_subset, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.53/0.75  thf('35', plain,
% 0.53/0.75      (![X12 : $i, X14 : $i]:
% 0.53/0.75         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.53/0.75      inference('cnf', [status(esa)], [t3_subset])).
% 0.53/0.75  thf('36', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['34', '35'])).
% 0.53/0.75  thf('37', plain,
% 0.53/0.75      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.53/0.75         (((k9_subset_1 @ X6 @ X8 @ X7) = (k9_subset_1 @ X6 @ X7 @ X8))
% 0.53/0.75          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.53/0.75      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.53/0.75  thf('38', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((k9_subset_1 @ X0 @ X1 @ X0) = (k9_subset_1 @ X0 @ X0 @ X1))),
% 0.53/0.75      inference('sup-', [status(thm)], ['36', '37'])).
% 0.53/0.75  thf('39', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['34', '35'])).
% 0.53/0.75  thf('40', plain,
% 0.53/0.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.53/0.75         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.53/0.75          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.53/0.75      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.53/0.75  thf('41', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['39', '40'])).
% 0.53/0.75  thf('42', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((k3_xboole_0 @ X1 @ X0) = (k9_subset_1 @ X0 @ X0 @ X1))),
% 0.53/0.75      inference('demod', [status(thm)], ['38', '41'])).
% 0.53/0.75  thf('43', plain,
% 0.53/0.75      (((k3_xboole_0 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.53/0.75         = (k3_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_C))),
% 0.53/0.75      inference('sup+', [status(thm)], ['32', '42'])).
% 0.53/0.75  thf('44', plain,
% 0.53/0.75      (![X15 : $i]:
% 0.53/0.75         (((k2_struct_0 @ X15) = (u1_struct_0 @ X15)) | ~ (l1_struct_0 @ X15))),
% 0.53/0.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.53/0.75  thf('45', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('46', plain,
% 0.53/0.75      (![X12 : $i, X13 : $i]:
% 0.53/0.75         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.53/0.75      inference('cnf', [status(esa)], [t3_subset])).
% 0.53/0.75  thf('47', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['45', '46'])).
% 0.53/0.75  thf('48', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.53/0.75      inference('simplify', [status(thm)], ['33'])).
% 0.53/0.75  thf(t20_xboole_1, axiom,
% 0.53/0.75    (![A:$i,B:$i,C:$i]:
% 0.53/0.75     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.53/0.75         ( ![D:$i]:
% 0.53/0.75           ( ( ( r1_tarski @ D @ B ) & ( r1_tarski @ D @ C ) ) =>
% 0.53/0.75             ( r1_tarski @ D @ A ) ) ) ) =>
% 0.53/0.75       ( ( A ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.53/0.75  thf('49', plain,
% 0.53/0.75      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.53/0.75         (~ (r1_tarski @ X3 @ X4)
% 0.53/0.75          | ~ (r1_tarski @ X3 @ X5)
% 0.53/0.75          | (r1_tarski @ (sk_D @ X5 @ X4 @ X3) @ X4)
% 0.53/0.75          | ((X3) = (k3_xboole_0 @ X4 @ X5)))),
% 0.53/0.75      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.53/0.75  thf('50', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         (((X0) = (k3_xboole_0 @ X0 @ X1))
% 0.53/0.75          | (r1_tarski @ (sk_D @ X1 @ X0 @ X0) @ X0)
% 0.53/0.75          | ~ (r1_tarski @ X0 @ X1))),
% 0.53/0.75      inference('sup-', [status(thm)], ['48', '49'])).
% 0.53/0.75  thf('51', plain,
% 0.53/0.75      (((r1_tarski @ (sk_D @ (u1_struct_0 @ sk_A) @ sk_C @ sk_C) @ sk_C)
% 0.53/0.75        | ((sk_C) = (k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A))))),
% 0.53/0.75      inference('sup-', [status(thm)], ['47', '50'])).
% 0.53/0.75  thf('52', plain,
% 0.53/0.75      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.53/0.75         (~ (r1_tarski @ X3 @ X4)
% 0.53/0.75          | ~ (r1_tarski @ X3 @ X5)
% 0.53/0.75          | ~ (r1_tarski @ (sk_D @ X5 @ X4 @ X3) @ X3)
% 0.53/0.75          | ((X3) = (k3_xboole_0 @ X4 @ X5)))),
% 0.53/0.75      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.53/0.75  thf('53', plain,
% 0.53/0.75      ((((sk_C) = (k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A)))
% 0.53/0.75        | ((sk_C) = (k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A)))
% 0.53/0.75        | ~ (r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))
% 0.53/0.75        | ~ (r1_tarski @ sk_C @ sk_C))),
% 0.53/0.75      inference('sup-', [status(thm)], ['51', '52'])).
% 0.53/0.75  thf('54', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['45', '46'])).
% 0.53/0.75  thf('55', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.53/0.75      inference('simplify', [status(thm)], ['33'])).
% 0.53/0.75  thf('56', plain,
% 0.53/0.75      ((((sk_C) = (k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A)))
% 0.53/0.75        | ((sk_C) = (k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A))))),
% 0.53/0.75      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.53/0.75  thf('57', plain, (((sk_C) = (k3_xboole_0 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('simplify', [status(thm)], ['56'])).
% 0.53/0.75  thf('58', plain,
% 0.53/0.75      ((((sk_C) = (k3_xboole_0 @ sk_C @ (k2_struct_0 @ sk_A)))
% 0.53/0.75        | ~ (l1_struct_0 @ sk_A))),
% 0.53/0.75      inference('sup+', [status(thm)], ['44', '57'])).
% 0.53/0.75  thf('59', plain, ((l1_struct_0 @ sk_A)),
% 0.53/0.75      inference('sup-', [status(thm)], ['27', '28'])).
% 0.53/0.75  thf('60', plain, (((sk_C) = (k3_xboole_0 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.53/0.75      inference('demod', [status(thm)], ['58', '59'])).
% 0.53/0.75  thf('61', plain, (((sk_C) = (k3_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_C))),
% 0.53/0.75      inference('demod', [status(thm)], ['43', '60'])).
% 0.53/0.75  thf('62', plain,
% 0.53/0.75      (((k2_pre_topc @ sk_A @ sk_C)
% 0.53/0.75         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.53/0.75      inference('demod', [status(thm)], ['17', '23', '61'])).
% 0.53/0.75  thf('63', plain,
% 0.53/0.75      (((k2_pre_topc @ sk_A @ sk_C)
% 0.53/0.75         != (k2_pre_topc @ sk_A @ 
% 0.53/0.75             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('64', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('65', plain,
% 0.53/0.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.53/0.75         (((k9_subset_1 @ X11 @ X9 @ X10) = (k3_xboole_0 @ X9 @ X10))
% 0.53/0.75          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.53/0.75      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.53/0.75  thf('66', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.53/0.75           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.53/0.75      inference('sup-', [status(thm)], ['64', '65'])).
% 0.53/0.75  thf('67', plain,
% 0.53/0.75      (((k2_pre_topc @ sk_A @ sk_C)
% 0.53/0.75         != (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C @ sk_B)))),
% 0.53/0.75      inference('demod', [status(thm)], ['63', '66'])).
% 0.53/0.75  thf('68', plain,
% 0.53/0.75      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('69', plain,
% 0.53/0.75      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.53/0.75         (((k9_subset_1 @ X6 @ X8 @ X7) = (k9_subset_1 @ X6 @ X7 @ X8))
% 0.53/0.75          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.53/0.75      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.53/0.75  thf('70', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.53/0.75           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['68', '69'])).
% 0.53/0.75  thf('71', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.53/0.75           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.53/0.75      inference('sup-', [status(thm)], ['64', '65'])).
% 0.53/0.75  thf('72', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((k3_xboole_0 @ X0 @ sk_B)
% 0.53/0.75           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.53/0.75      inference('demod', [status(thm)], ['70', '71'])).
% 0.53/0.75  thf('73', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.53/0.75           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.53/0.75      inference('sup-', [status(thm)], ['11', '12'])).
% 0.53/0.75  thf('74', plain,
% 0.53/0.75      (((k3_xboole_0 @ sk_C @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.53/0.75      inference('sup+', [status(thm)], ['72', '73'])).
% 0.53/0.75  thf('75', plain,
% 0.53/0.75      (((k2_pre_topc @ sk_A @ sk_C)
% 0.53/0.75         != (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 0.53/0.75      inference('demod', [status(thm)], ['67', '74'])).
% 0.53/0.75  thf('76', plain, ($false),
% 0.53/0.75      inference('simplify_reflect-', [status(thm)], ['62', '75'])).
% 0.53/0.75  
% 0.53/0.75  % SZS output end Refutation
% 0.53/0.75  
% 0.53/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
