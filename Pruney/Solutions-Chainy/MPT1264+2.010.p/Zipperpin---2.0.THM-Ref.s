%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T3wr0MPDNw

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:08 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 140 expanded)
%              Number of leaves         :   32 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  693 (1746 expanded)
%              Number of equality atoms :   41 (  76 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('3',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v3_pre_topc @ X24 @ X25 )
      | ( ( k2_pre_topc @ X25 @ ( k9_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 @ ( k2_pre_topc @ X25 @ X26 ) ) )
        = ( k2_pre_topc @ X25 @ ( k9_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t41_tops_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( k2_pre_topc @ sk_A @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v3_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( k2_pre_topc @ sk_A @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5','6','7'])).

thf('9',plain,
    ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v1_tops_1 @ X22 @ X23 )
      | ( ( k2_pre_topc @ X23 @ X22 )
        = ( k2_struct_0 @ X23 ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k9_subset_1 @ X17 @ X15 @ X16 )
        = ( k3_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ) )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','15','18'])).

thf('20',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ) )
      = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','19'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X11 ) @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('22',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('23',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k9_subset_1 @ X17 @ X15 @ X16 )
        = ( k3_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X20: $i] :
      ( ( ( k2_struct_0 @ X20 )
        = ( u1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,
    ( ( r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['33'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['35'])).

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

thf('37',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X9 )
      | ( r1_tarski @ ( sk_D @ X9 @ X8 @ X7 ) @ X8 )
      | ( X7
        = ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( sk_D @ X1 @ X0 @ X0 ) @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r1_tarski @ ( sk_D @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_C_1 ) @ sk_C_1 )
    | ( sk_C_1
      = ( k3_xboole_0 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X9 )
      | ~ ( r1_tarski @ ( sk_D @ X9 @ X8 @ X7 ) @ X7 )
      | ( X7
        = ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('41',plain,
    ( ( sk_C_1
      = ( k3_xboole_0 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_C_1
      = ( k3_xboole_0 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r1_tarski @ sk_C_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['33'])).

thf('43',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('44',plain,
    ( ( sk_C_1
      = ( k3_xboole_0 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( sk_C_1
      = ( k3_xboole_0 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( sk_C_1
      = ( k3_xboole_0 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('48',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('49',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('52',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C_1 )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','25','50','51'])).

thf('53',plain,(
    ( k2_pre_topc @ sk_A @ sk_C_1 )
 != ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('55',plain,(
    ( k2_pre_topc @ sk_A @ sk_C_1 )
 != ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['52','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T3wr0MPDNw
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:41:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.72  % Solved by: fo/fo7.sh
% 0.44/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.72  % done 264 iterations in 0.225s
% 0.44/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.72  % SZS output start Refutation
% 0.44/0.72  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.44/0.72  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.44/0.72  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.44/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.72  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.44/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.72  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.44/0.72  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.44/0.72  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.44/0.72  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.44/0.72  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.44/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.44/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.72  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.72  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.44/0.72  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.44/0.72  thf(d3_struct_0, axiom,
% 0.44/0.72    (![A:$i]:
% 0.44/0.72     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.44/0.72  thf('0', plain,
% 0.44/0.72      (![X20 : $i]:
% 0.44/0.72         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.44/0.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.72  thf(t81_tops_1, conjecture,
% 0.44/0.72    (![A:$i]:
% 0.44/0.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.72       ( ![B:$i]:
% 0.44/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.72           ( ( v1_tops_1 @ B @ A ) =>
% 0.44/0.72             ( ![C:$i]:
% 0.44/0.72               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.72                 ( ( v3_pre_topc @ C @ A ) =>
% 0.44/0.72                   ( ( k2_pre_topc @ A @ C ) =
% 0.44/0.72                     ( k2_pre_topc @
% 0.44/0.72                       A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.72    (~( ![A:$i]:
% 0.44/0.72        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.72          ( ![B:$i]:
% 0.44/0.72            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.72              ( ( v1_tops_1 @ B @ A ) =>
% 0.44/0.72                ( ![C:$i]:
% 0.44/0.72                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.72                    ( ( v3_pre_topc @ C @ A ) =>
% 0.44/0.72                      ( ( k2_pre_topc @ A @ C ) =
% 0.44/0.72                        ( k2_pre_topc @
% 0.44/0.72                          A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.44/0.72    inference('cnf.neg', [status(esa)], [t81_tops_1])).
% 0.44/0.72  thf('1', plain,
% 0.44/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.72  thf('2', plain,
% 0.44/0.72      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.72  thf(t41_tops_1, axiom,
% 0.44/0.72    (![A:$i]:
% 0.44/0.72     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.72       ( ![B:$i]:
% 0.44/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.72           ( ![C:$i]:
% 0.44/0.72             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.72               ( ( v3_pre_topc @ B @ A ) =>
% 0.44/0.72                 ( ( k2_pre_topc @
% 0.44/0.72                     A @ 
% 0.44/0.72                     ( k9_subset_1 @
% 0.44/0.72                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) ) =
% 0.44/0.72                   ( k2_pre_topc @
% 0.44/0.72                     A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.44/0.72  thf('3', plain,
% 0.44/0.72      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.44/0.72         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.44/0.72          | ~ (v3_pre_topc @ X24 @ X25)
% 0.44/0.72          | ((k2_pre_topc @ X25 @ 
% 0.44/0.72              (k9_subset_1 @ (u1_struct_0 @ X25) @ X24 @ 
% 0.44/0.72               (k2_pre_topc @ X25 @ X26)))
% 0.44/0.72              = (k2_pre_topc @ X25 @ 
% 0.44/0.72                 (k9_subset_1 @ (u1_struct_0 @ X25) @ X24 @ X26)))
% 0.44/0.72          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.44/0.72          | ~ (l1_pre_topc @ X25)
% 0.44/0.72          | ~ (v2_pre_topc @ X25))),
% 0.44/0.72      inference('cnf', [status(esa)], [t41_tops_1])).
% 0.44/0.72  thf('4', plain,
% 0.44/0.72      (![X0 : $i]:
% 0.44/0.72         (~ (v2_pre_topc @ sk_A)
% 0.44/0.72          | ~ (l1_pre_topc @ sk_A)
% 0.44/0.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.72          | ((k2_pre_topc @ sk_A @ 
% 0.44/0.72              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.44/0.72               (k2_pre_topc @ sk_A @ X0)))
% 0.44/0.72              = (k2_pre_topc @ sk_A @ 
% 0.44/0.72                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0)))
% 0.44/0.72          | ~ (v3_pre_topc @ sk_C_1 @ sk_A))),
% 0.44/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.44/0.72  thf('5', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.72  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.72  thf('7', plain, ((v3_pre_topc @ sk_C_1 @ sk_A)),
% 0.44/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.72  thf('8', plain,
% 0.44/0.72      (![X0 : $i]:
% 0.44/0.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.72          | ((k2_pre_topc @ sk_A @ 
% 0.44/0.72              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.44/0.72               (k2_pre_topc @ sk_A @ X0)))
% 0.44/0.72              = (k2_pre_topc @ sk_A @ 
% 0.44/0.72                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0))))),
% 0.44/0.72      inference('demod', [status(thm)], ['4', '5', '6', '7'])).
% 0.44/0.72  thf('9', plain,
% 0.44/0.72      (((k2_pre_topc @ sk_A @ 
% 0.44/0.72         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.44/0.72          (k2_pre_topc @ sk_A @ sk_B)))
% 0.44/0.72         = (k2_pre_topc @ sk_A @ 
% 0.44/0.72            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_B)))),
% 0.44/0.72      inference('sup-', [status(thm)], ['1', '8'])).
% 0.44/0.72  thf('10', plain,
% 0.44/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.72  thf(d3_tops_1, axiom,
% 0.44/0.72    (![A:$i]:
% 0.44/0.72     ( ( l1_pre_topc @ A ) =>
% 0.44/0.72       ( ![B:$i]:
% 0.44/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.72           ( ( v1_tops_1 @ B @ A ) <=>
% 0.44/0.72             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.44/0.72  thf('11', plain,
% 0.44/0.72      (![X22 : $i, X23 : $i]:
% 0.44/0.72         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.44/0.72          | ~ (v1_tops_1 @ X22 @ X23)
% 0.44/0.72          | ((k2_pre_topc @ X23 @ X22) = (k2_struct_0 @ X23))
% 0.44/0.72          | ~ (l1_pre_topc @ X23))),
% 0.44/0.72      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.44/0.72  thf('12', plain,
% 0.44/0.72      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.72        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 0.44/0.72        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.44/0.72      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.72  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.72  thf('14', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.44/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.72  thf('15', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.44/0.72      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.44/0.72  thf('16', plain,
% 0.44/0.72      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.72  thf(redefinition_k9_subset_1, axiom,
% 0.44/0.72    (![A:$i,B:$i,C:$i]:
% 0.44/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.72       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.44/0.72  thf('17', plain,
% 0.44/0.72      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.72         (((k9_subset_1 @ X17 @ X15 @ X16) = (k3_xboole_0 @ X15 @ X16))
% 0.44/0.72          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.44/0.72      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.44/0.72  thf('18', plain,
% 0.44/0.72      (![X0 : $i]:
% 0.44/0.72         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.44/0.72           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.44/0.72      inference('sup-', [status(thm)], ['16', '17'])).
% 0.44/0.72  thf('19', plain,
% 0.44/0.72      (((k2_pre_topc @ sk_A @ 
% 0.44/0.72         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ (k2_struct_0 @ sk_A)))
% 0.44/0.72         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_B)))),
% 0.44/0.72      inference('demod', [status(thm)], ['9', '15', '18'])).
% 0.44/0.72  thf('20', plain,
% 0.44/0.72      ((((k2_pre_topc @ sk_A @ 
% 0.44/0.72          (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C_1 @ (k2_struct_0 @ sk_A)))
% 0.44/0.72          = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_B)))
% 0.44/0.72        | ~ (l1_struct_0 @ sk_A))),
% 0.44/0.72      inference('sup+', [status(thm)], ['0', '19'])).
% 0.44/0.72  thf(dt_k2_subset_1, axiom,
% 0.44/0.72    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.44/0.72  thf('21', plain,
% 0.44/0.72      (![X11 : $i]: (m1_subset_1 @ (k2_subset_1 @ X11) @ (k1_zfmisc_1 @ X11))),
% 0.44/0.72      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.44/0.72  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.44/0.72  thf('22', plain, (![X10 : $i]: ((k2_subset_1 @ X10) = (X10))),
% 0.44/0.72      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.44/0.72  thf('23', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 0.44/0.72      inference('demod', [status(thm)], ['21', '22'])).
% 0.44/0.72  thf('24', plain,
% 0.44/0.72      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.72         (((k9_subset_1 @ X17 @ X15 @ X16) = (k3_xboole_0 @ X15 @ X16))
% 0.44/0.72          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.44/0.72      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.44/0.72  thf('25', plain,
% 0.44/0.72      (![X0 : $i, X1 : $i]:
% 0.44/0.72         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.44/0.72      inference('sup-', [status(thm)], ['23', '24'])).
% 0.44/0.72  thf('26', plain,
% 0.44/0.72      (![X20 : $i]:
% 0.44/0.72         (((k2_struct_0 @ X20) = (u1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.44/0.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.72  thf(d3_tarski, axiom,
% 0.44/0.72    (![A:$i,B:$i]:
% 0.44/0.72     ( ( r1_tarski @ A @ B ) <=>
% 0.44/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.44/0.72  thf('27', plain,
% 0.44/0.72      (![X1 : $i, X3 : $i]:
% 0.44/0.72         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.44/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.72  thf('28', plain,
% 0.44/0.72      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.72  thf(l3_subset_1, axiom,
% 0.44/0.72    (![A:$i,B:$i]:
% 0.44/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.44/0.72  thf('29', plain,
% 0.44/0.72      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.44/0.72         (~ (r2_hidden @ X12 @ X13)
% 0.44/0.72          | (r2_hidden @ X12 @ X14)
% 0.44/0.72          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.44/0.72      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.44/0.72  thf('30', plain,
% 0.44/0.72      (![X0 : $i]:
% 0.44/0.72         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.44/0.72      inference('sup-', [status(thm)], ['28', '29'])).
% 0.44/0.72  thf('31', plain,
% 0.44/0.72      (![X0 : $i]:
% 0.44/0.72         ((r1_tarski @ sk_C_1 @ X0)
% 0.44/0.72          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (u1_struct_0 @ sk_A)))),
% 0.44/0.72      inference('sup-', [status(thm)], ['27', '30'])).
% 0.44/0.72  thf('32', plain,
% 0.44/0.72      (![X1 : $i, X3 : $i]:
% 0.44/0.72         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.44/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.72  thf('33', plain,
% 0.44/0.72      (((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.44/0.72        | (r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.72      inference('sup-', [status(thm)], ['31', '32'])).
% 0.44/0.72  thf('34', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.44/0.72      inference('simplify', [status(thm)], ['33'])).
% 0.44/0.72  thf(d10_xboole_0, axiom,
% 0.44/0.72    (![A:$i,B:$i]:
% 0.44/0.72     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.44/0.72  thf('35', plain,
% 0.44/0.72      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.44/0.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.72  thf('36', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.44/0.72      inference('simplify', [status(thm)], ['35'])).
% 0.44/0.72  thf(t20_xboole_1, axiom,
% 0.44/0.72    (![A:$i,B:$i,C:$i]:
% 0.44/0.72     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.44/0.72         ( ![D:$i]:
% 0.44/0.72           ( ( ( r1_tarski @ D @ B ) & ( r1_tarski @ D @ C ) ) =>
% 0.44/0.72             ( r1_tarski @ D @ A ) ) ) ) =>
% 0.44/0.72       ( ( A ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.44/0.72  thf('37', plain,
% 0.44/0.72      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.44/0.72         (~ (r1_tarski @ X7 @ X8)
% 0.44/0.72          | ~ (r1_tarski @ X7 @ X9)
% 0.44/0.72          | (r1_tarski @ (sk_D @ X9 @ X8 @ X7) @ X8)
% 0.44/0.72          | ((X7) = (k3_xboole_0 @ X8 @ X9)))),
% 0.44/0.72      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.44/0.72  thf('38', plain,
% 0.44/0.72      (![X0 : $i, X1 : $i]:
% 0.44/0.72         (((X0) = (k3_xboole_0 @ X0 @ X1))
% 0.44/0.72          | (r1_tarski @ (sk_D @ X1 @ X0 @ X0) @ X0)
% 0.44/0.72          | ~ (r1_tarski @ X0 @ X1))),
% 0.44/0.72      inference('sup-', [status(thm)], ['36', '37'])).
% 0.44/0.72  thf('39', plain,
% 0.44/0.72      (((r1_tarski @ (sk_D @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_C_1) @ sk_C_1)
% 0.44/0.72        | ((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.72      inference('sup-', [status(thm)], ['34', '38'])).
% 0.44/0.72  thf('40', plain,
% 0.44/0.72      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.44/0.72         (~ (r1_tarski @ X7 @ X8)
% 0.44/0.72          | ~ (r1_tarski @ X7 @ X9)
% 0.44/0.72          | ~ (r1_tarski @ (sk_D @ X9 @ X8 @ X7) @ X7)
% 0.44/0.72          | ((X7) = (k3_xboole_0 @ X8 @ X9)))),
% 0.44/0.72      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.44/0.72  thf('41', plain,
% 0.44/0.72      ((((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.72        | ((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.72        | ~ (r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.44/0.72        | ~ (r1_tarski @ sk_C_1 @ sk_C_1))),
% 0.44/0.72      inference('sup-', [status(thm)], ['39', '40'])).
% 0.44/0.72  thf('42', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.44/0.72      inference('simplify', [status(thm)], ['33'])).
% 0.44/0.72  thf('43', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.44/0.72      inference('simplify', [status(thm)], ['35'])).
% 0.44/0.72  thf('44', plain,
% 0.44/0.72      ((((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.72        | ((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ (u1_struct_0 @ sk_A))))),
% 0.44/0.72      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.44/0.72  thf('45', plain,
% 0.44/0.72      (((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.72      inference('simplify', [status(thm)], ['44'])).
% 0.44/0.72  thf('46', plain,
% 0.44/0.72      ((((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ (k2_struct_0 @ sk_A)))
% 0.44/0.72        | ~ (l1_struct_0 @ sk_A))),
% 0.44/0.72      inference('sup+', [status(thm)], ['26', '45'])).
% 0.44/0.72  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.72  thf(dt_l1_pre_topc, axiom,
% 0.44/0.72    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.44/0.72  thf('48', plain,
% 0.44/0.72      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.44/0.72      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.44/0.72  thf('49', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.72      inference('sup-', [status(thm)], ['47', '48'])).
% 0.44/0.72  thf('50', plain,
% 0.44/0.72      (((sk_C_1) = (k3_xboole_0 @ sk_C_1 @ (k2_struct_0 @ sk_A)))),
% 0.44/0.72      inference('demod', [status(thm)], ['46', '49'])).
% 0.44/0.72  thf('51', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.72      inference('sup-', [status(thm)], ['47', '48'])).
% 0.44/0.72  thf('52', plain,
% 0.44/0.72      (((k2_pre_topc @ sk_A @ sk_C_1)
% 0.44/0.72         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_B)))),
% 0.44/0.72      inference('demod', [status(thm)], ['20', '25', '50', '51'])).
% 0.44/0.72  thf('53', plain,
% 0.44/0.72      (((k2_pre_topc @ sk_A @ sk_C_1)
% 0.44/0.72         != (k2_pre_topc @ sk_A @ 
% 0.44/0.72             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_B)))),
% 0.44/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.72  thf('54', plain,
% 0.44/0.72      (![X0 : $i]:
% 0.44/0.72         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.44/0.72           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.44/0.72      inference('sup-', [status(thm)], ['16', '17'])).
% 0.44/0.72  thf('55', plain,
% 0.44/0.72      (((k2_pre_topc @ sk_A @ sk_C_1)
% 0.44/0.72         != (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_B)))),
% 0.44/0.72      inference('demod', [status(thm)], ['53', '54'])).
% 0.44/0.72  thf('56', plain, ($false),
% 0.44/0.72      inference('simplify_reflect-', [status(thm)], ['52', '55'])).
% 0.44/0.72  
% 0.44/0.72  % SZS output end Refutation
% 0.44/0.72  
% 0.55/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
