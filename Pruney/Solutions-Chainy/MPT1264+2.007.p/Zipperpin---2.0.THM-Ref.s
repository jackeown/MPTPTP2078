%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VtAZwlA2om

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:07 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 315 expanded)
%              Number of leaves         :   30 ( 106 expanded)
%              Depth                    :   15
%              Number of atoms          : 1049 (4119 expanded)
%              Number of equality atoms :   70 ( 195 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X23 @ X24 )
      | ( ( k2_pre_topc @ X24 @ ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 @ ( k2_pre_topc @ X24 @ X25 ) ) )
        = ( k2_pre_topc @ X24 @ ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t41_tops_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( k2_pre_topc @ sk_A @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) ) )
      | ~ ( v3_pre_topc @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v3_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( k2_pre_topc @ sk_A @ X0 ) ) )
        = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('8',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X10 @ X12 @ X11 )
        = ( k9_subset_1 @ X10 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_C_1 )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('14',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('15',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_C_1 )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k9_subset_1 @ X18 @ X16 @ X17 )
        = ( k3_xboole_0 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_C_1 )
      = ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_C_1 )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_C_1 )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','23'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_C_1 ) )
        = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['7','24','25'])).

thf('27',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_C_1 ) )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','26'])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v1_tops_1 @ X21 @ X22 )
      | ( ( k2_pre_topc @ X22 @ X21 )
        = ( k2_struct_0 @ X22 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('37',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('39',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( r2_hidden @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,
    ( ( r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['36','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('47',plain,(
    r1_tarski @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

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

thf('48',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X9 )
      | ( r1_tarski @ ( sk_D @ X9 @ X8 @ X7 ) @ X9 )
      | ( X7
        = ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( sk_C_1
        = ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ X0 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_tarski @ ( sk_D @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_C_1 )
    | ( sk_C_1
      = ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['35','49'])).

thf('51',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X9 )
      | ~ ( r1_tarski @ ( sk_D @ X9 @ X8 @ X7 ) @ X7 )
      | ( X7
        = ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('52',plain,
    ( ( sk_C_1
      = ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( sk_C_1
      = ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ~ ( r1_tarski @ sk_C_1 @ sk_C_1 )
    | ~ ( r1_tarski @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('54',plain,(
    r1_tarski @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('55',plain,
    ( ( sk_C_1
      = ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ( sk_C_1
      = ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( sk_C_1
    = ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C_1 )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['27','33','56'])).

thf('58',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('59',plain,(
    ( k2_pre_topc @ sk_A @ sk_C_1 )
 != ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X10 @ X12 @ X11 )
        = ( k9_subset_1 @ X10 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ( k2_pre_topc @ sk_A @ sk_C_1 )
 != ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_C_1 )
     != ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('66',plain,(
    ( k2_pre_topc @ sk_A @ sk_C_1 )
 != ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k9_subset_1 @ X18 @ X16 @ X17 )
        = ( k3_xboole_0 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_C_1 )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('71',plain,
    ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k3_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ( k2_pre_topc @ sk_A @ sk_C_1 )
 != ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k9_subset_1 @ X18 @ X16 @ X17 )
        = ( k3_xboole_0 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 )
      = ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['75','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('83',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
        = ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ X0 ) )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['82','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('90',plain,
    ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 @ sk_B )
    = ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k3_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('92',plain,
    ( ( k9_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 @ sk_B )
    = ( k3_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k3_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['81','92'])).

thf('94',plain,(
    ( k2_pre_topc @ sk_A @ sk_C_1 )
 != ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['72','93'])).

thf('95',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['57','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VtAZwlA2om
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.62  % Solved by: fo/fo7.sh
% 0.44/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.62  % done 315 iterations in 0.164s
% 0.44/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.62  % SZS output start Refutation
% 0.44/0.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.44/0.62  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.44/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.62  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.44/0.62  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.44/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.44/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.44/0.62  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.44/0.62  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.44/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.62  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.44/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.44/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.44/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.62  thf(t81_tops_1, conjecture,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62           ( ( v1_tops_1 @ B @ A ) =>
% 0.44/0.62             ( ![C:$i]:
% 0.44/0.62               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62                 ( ( v3_pre_topc @ C @ A ) =>
% 0.44/0.62                   ( ( k2_pre_topc @ A @ C ) =
% 0.44/0.62                     ( k2_pre_topc @
% 0.44/0.62                       A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.62    (~( ![A:$i]:
% 0.44/0.62        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.62          ( ![B:$i]:
% 0.44/0.62            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62              ( ( v1_tops_1 @ B @ A ) =>
% 0.44/0.62                ( ![C:$i]:
% 0.44/0.62                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62                    ( ( v3_pre_topc @ C @ A ) =>
% 0.44/0.62                      ( ( k2_pre_topc @ A @ C ) =
% 0.44/0.62                        ( k2_pre_topc @
% 0.44/0.62                          A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ C @ B ) ) ) ) ) ) ) ) ) ) )),
% 0.44/0.62    inference('cnf.neg', [status(esa)], [t81_tops_1])).
% 0.44/0.62  thf('0', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('1', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(t41_tops_1, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62           ( ![C:$i]:
% 0.44/0.62             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62               ( ( v3_pre_topc @ B @ A ) =>
% 0.44/0.62                 ( ( k2_pre_topc @
% 0.44/0.62                     A @ 
% 0.44/0.62                     ( k9_subset_1 @
% 0.44/0.62                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) ) =
% 0.44/0.62                   ( k2_pre_topc @
% 0.44/0.62                     A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) ) ) ) ) ) ) ))).
% 0.44/0.62  thf('2', plain,
% 0.44/0.62      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.44/0.62          | ~ (v3_pre_topc @ X23 @ X24)
% 0.44/0.62          | ((k2_pre_topc @ X24 @ 
% 0.44/0.62              (k9_subset_1 @ (u1_struct_0 @ X24) @ X23 @ 
% 0.44/0.62               (k2_pre_topc @ X24 @ X25)))
% 0.44/0.62              = (k2_pre_topc @ X24 @ 
% 0.44/0.62                 (k9_subset_1 @ (u1_struct_0 @ X24) @ X23 @ X25)))
% 0.44/0.62          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.44/0.62          | ~ (l1_pre_topc @ X24)
% 0.44/0.62          | ~ (v2_pre_topc @ X24))),
% 0.44/0.62      inference('cnf', [status(esa)], [t41_tops_1])).
% 0.44/0.62  thf('3', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (v2_pre_topc @ sk_A)
% 0.44/0.62          | ~ (l1_pre_topc @ sk_A)
% 0.44/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.62          | ((k2_pre_topc @ sk_A @ 
% 0.44/0.62              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.44/0.62               (k2_pre_topc @ sk_A @ X0)))
% 0.44/0.62              = (k2_pre_topc @ sk_A @ 
% 0.44/0.62                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0)))
% 0.44/0.62          | ~ (v3_pre_topc @ sk_C_1 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.62  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('6', plain, ((v3_pre_topc @ sk_C_1 @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('7', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.62          | ((k2_pre_topc @ sk_A @ 
% 0.44/0.62              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.44/0.62               (k2_pre_topc @ sk_A @ X0)))
% 0.44/0.62              = (k2_pre_topc @ sk_A @ 
% 0.44/0.62                 (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0))))),
% 0.44/0.62      inference('demod', [status(thm)], ['3', '4', '5', '6'])).
% 0.44/0.62  thf(d3_struct_0, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.44/0.62  thf('8', plain,
% 0.44/0.62      (![X19 : $i]:
% 0.44/0.62         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.44/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.62  thf('9', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(commutativity_k9_subset_1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.62       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.44/0.62  thf('10', plain,
% 0.44/0.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.44/0.62         (((k9_subset_1 @ X10 @ X12 @ X11) = (k9_subset_1 @ X10 @ X11 @ X12))
% 0.44/0.62          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.44/0.62      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.44/0.62  thf('11', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1)
% 0.44/0.62           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.44/0.62  thf('12', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_C_1)
% 0.44/0.62            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0))
% 0.44/0.62          | ~ (l1_struct_0 @ sk_A))),
% 0.44/0.62      inference('sup+', [status(thm)], ['8', '11'])).
% 0.44/0.62  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(dt_l1_pre_topc, axiom,
% 0.44/0.62    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.44/0.62  thf('14', plain,
% 0.44/0.62      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.44/0.62      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.44/0.62  thf('15', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.44/0.62  thf('16', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_C_1)
% 0.44/0.62           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['12', '15'])).
% 0.44/0.62  thf('17', plain,
% 0.44/0.62      (![X19 : $i]:
% 0.44/0.62         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.44/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.62  thf('18', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('19', plain,
% 0.44/0.62      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.44/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.44/0.62      inference('sup+', [status(thm)], ['17', '18'])).
% 0.44/0.62  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.44/0.62  thf('21', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.44/0.62      inference('demod', [status(thm)], ['19', '20'])).
% 0.44/0.62  thf(redefinition_k9_subset_1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.62       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.44/0.62  thf('22', plain,
% 0.44/0.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.44/0.62         (((k9_subset_1 @ X18 @ X16 @ X17) = (k3_xboole_0 @ X16 @ X17))
% 0.44/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.44/0.62      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.44/0.62  thf('23', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_C_1)
% 0.44/0.62           = (k3_xboole_0 @ X0 @ sk_C_1))),
% 0.44/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.44/0.62  thf('24', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k3_xboole_0 @ X0 @ sk_C_1)
% 0.44/0.62           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['16', '23'])).
% 0.44/0.62  thf('25', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k3_xboole_0 @ X0 @ sk_C_1)
% 0.44/0.62           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['16', '23'])).
% 0.44/0.62  thf('26', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.62          | ((k2_pre_topc @ sk_A @ 
% 0.44/0.62              (k3_xboole_0 @ (k2_pre_topc @ sk_A @ X0) @ sk_C_1))
% 0.44/0.62              = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ X0 @ sk_C_1))))),
% 0.44/0.62      inference('demod', [status(thm)], ['7', '24', '25'])).
% 0.44/0.62  thf('27', plain,
% 0.44/0.62      (((k2_pre_topc @ sk_A @ 
% 0.44/0.62         (k3_xboole_0 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_C_1))
% 0.44/0.62         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['0', '26'])).
% 0.44/0.62  thf('28', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(d3_tops_1, axiom,
% 0.44/0.62    (![A:$i]:
% 0.44/0.62     ( ( l1_pre_topc @ A ) =>
% 0.44/0.62       ( ![B:$i]:
% 0.44/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.62           ( ( v1_tops_1 @ B @ A ) <=>
% 0.44/0.62             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.44/0.62  thf('29', plain,
% 0.44/0.62      (![X21 : $i, X22 : $i]:
% 0.44/0.62         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.44/0.62          | ~ (v1_tops_1 @ X21 @ X22)
% 0.44/0.62          | ((k2_pre_topc @ X22 @ X21) = (k2_struct_0 @ X22))
% 0.44/0.62          | ~ (l1_pre_topc @ X22))),
% 0.44/0.62      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.44/0.62  thf('30', plain,
% 0.44/0.62      ((~ (l1_pre_topc @ sk_A)
% 0.44/0.62        | ((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))
% 0.44/0.62        | ~ (v1_tops_1 @ sk_B @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.44/0.62  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('32', plain, ((v1_tops_1 @ sk_B @ sk_A)),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('33', plain, (((k2_pre_topc @ sk_A @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.44/0.62  thf(d10_xboole_0, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.44/0.62  thf('34', plain,
% 0.44/0.62      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.44/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.44/0.62  thf('35', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.44/0.62      inference('simplify', [status(thm)], ['34'])).
% 0.44/0.62  thf('36', plain,
% 0.44/0.62      (![X19 : $i]:
% 0.44/0.62         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.44/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.62  thf(d3_tarski, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.44/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.44/0.62  thf('37', plain,
% 0.44/0.62      (![X1 : $i, X3 : $i]:
% 0.44/0.62         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.44/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.62  thf('38', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf(l3_subset_1, axiom,
% 0.44/0.62    (![A:$i,B:$i]:
% 0.44/0.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.44/0.62  thf('39', plain,
% 0.44/0.62      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.44/0.62         (~ (r2_hidden @ X13 @ X14)
% 0.44/0.62          | (r2_hidden @ X13 @ X15)
% 0.44/0.62          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.44/0.62      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.44/0.62  thf('40', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.44/0.62      inference('sup-', [status(thm)], ['38', '39'])).
% 0.44/0.62  thf('41', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((r1_tarski @ sk_C_1 @ X0)
% 0.44/0.62          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['37', '40'])).
% 0.44/0.62  thf('42', plain,
% 0.44/0.62      (![X1 : $i, X3 : $i]:
% 0.44/0.62         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.44/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.62  thf('43', plain,
% 0.44/0.62      (((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.44/0.62        | (r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.44/0.62  thf('44', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.44/0.62      inference('simplify', [status(thm)], ['43'])).
% 0.44/0.62  thf('45', plain,
% 0.44/0.62      (((r1_tarski @ sk_C_1 @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.44/0.62      inference('sup+', [status(thm)], ['36', '44'])).
% 0.44/0.62  thf('46', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.44/0.62  thf('47', plain, ((r1_tarski @ sk_C_1 @ (k2_struct_0 @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)], ['45', '46'])).
% 0.44/0.62  thf(t20_xboole_1, axiom,
% 0.44/0.62    (![A:$i,B:$i,C:$i]:
% 0.44/0.62     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.44/0.62         ( ![D:$i]:
% 0.44/0.62           ( ( ( r1_tarski @ D @ B ) & ( r1_tarski @ D @ C ) ) =>
% 0.44/0.62             ( r1_tarski @ D @ A ) ) ) ) =>
% 0.44/0.62       ( ( A ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.44/0.62  thf('48', plain,
% 0.44/0.62      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.44/0.62         (~ (r1_tarski @ X7 @ X8)
% 0.44/0.62          | ~ (r1_tarski @ X7 @ X9)
% 0.44/0.62          | (r1_tarski @ (sk_D @ X9 @ X8 @ X7) @ X9)
% 0.44/0.62          | ((X7) = (k3_xboole_0 @ X8 @ X9)))),
% 0.44/0.62      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.44/0.62  thf('49', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (((sk_C_1) = (k3_xboole_0 @ (k2_struct_0 @ sk_A) @ X0))
% 0.44/0.62          | (r1_tarski @ (sk_D @ X0 @ (k2_struct_0 @ sk_A) @ sk_C_1) @ X0)
% 0.44/0.62          | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['47', '48'])).
% 0.44/0.62  thf('50', plain,
% 0.44/0.62      (((r1_tarski @ (sk_D @ sk_C_1 @ (k2_struct_0 @ sk_A) @ sk_C_1) @ sk_C_1)
% 0.44/0.62        | ((sk_C_1) = (k3_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_C_1)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['35', '49'])).
% 0.44/0.62  thf('51', plain,
% 0.44/0.62      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.44/0.62         (~ (r1_tarski @ X7 @ X8)
% 0.44/0.62          | ~ (r1_tarski @ X7 @ X9)
% 0.44/0.62          | ~ (r1_tarski @ (sk_D @ X9 @ X8 @ X7) @ X7)
% 0.44/0.62          | ((X7) = (k3_xboole_0 @ X8 @ X9)))),
% 0.44/0.62      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.44/0.62  thf('52', plain,
% 0.44/0.62      ((((sk_C_1) = (k3_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_C_1))
% 0.44/0.62        | ((sk_C_1) = (k3_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_C_1))
% 0.44/0.62        | ~ (r1_tarski @ sk_C_1 @ sk_C_1)
% 0.44/0.62        | ~ (r1_tarski @ sk_C_1 @ (k2_struct_0 @ sk_A)))),
% 0.44/0.62      inference('sup-', [status(thm)], ['50', '51'])).
% 0.44/0.62  thf('53', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.44/0.62      inference('simplify', [status(thm)], ['34'])).
% 0.44/0.62  thf('54', plain, ((r1_tarski @ sk_C_1 @ (k2_struct_0 @ sk_A))),
% 0.44/0.62      inference('demod', [status(thm)], ['45', '46'])).
% 0.44/0.62  thf('55', plain,
% 0.44/0.62      ((((sk_C_1) = (k3_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_C_1))
% 0.44/0.62        | ((sk_C_1) = (k3_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_C_1)))),
% 0.44/0.62      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.44/0.62  thf('56', plain,
% 0.44/0.62      (((sk_C_1) = (k3_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_C_1))),
% 0.44/0.62      inference('simplify', [status(thm)], ['55'])).
% 0.44/0.62  thf('57', plain,
% 0.44/0.62      (((k2_pre_topc @ sk_A @ sk_C_1)
% 0.44/0.62         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)))),
% 0.44/0.62      inference('demod', [status(thm)], ['27', '33', '56'])).
% 0.44/0.62  thf('58', plain,
% 0.44/0.62      (![X19 : $i]:
% 0.44/0.62         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.44/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.62  thf('59', plain,
% 0.44/0.62      (((k2_pre_topc @ sk_A @ sk_C_1)
% 0.44/0.62         != (k2_pre_topc @ sk_A @ 
% 0.44/0.62             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_B)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('60', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('61', plain,
% 0.44/0.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.44/0.62         (((k9_subset_1 @ X10 @ X12 @ X11) = (k9_subset_1 @ X10 @ X11 @ X12))
% 0.44/0.62          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.44/0.62      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.44/0.62  thf('62', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.44/0.62           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['60', '61'])).
% 0.44/0.62  thf('63', plain,
% 0.44/0.62      (((k2_pre_topc @ sk_A @ sk_C_1)
% 0.44/0.62         != (k2_pre_topc @ sk_A @ 
% 0.44/0.62             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C_1)))),
% 0.44/0.62      inference('demod', [status(thm)], ['59', '62'])).
% 0.44/0.62  thf('64', plain,
% 0.44/0.62      ((((k2_pre_topc @ sk_A @ sk_C_1)
% 0.44/0.62          != (k2_pre_topc @ sk_A @ 
% 0.44/0.62              (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ sk_C_1)))
% 0.44/0.62        | ~ (l1_struct_0 @ sk_A))),
% 0.44/0.62      inference('sup-', [status(thm)], ['58', '63'])).
% 0.44/0.62  thf('65', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.44/0.62  thf('66', plain,
% 0.44/0.62      (((k2_pre_topc @ sk_A @ sk_C_1)
% 0.44/0.62         != (k2_pre_topc @ sk_A @ 
% 0.44/0.62             (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ sk_C_1)))),
% 0.44/0.62      inference('demod', [status(thm)], ['64', '65'])).
% 0.44/0.62  thf('67', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('68', plain,
% 0.44/0.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.44/0.62         (((k9_subset_1 @ X18 @ X16 @ X17) = (k3_xboole_0 @ X16 @ X17))
% 0.44/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.44/0.62      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.44/0.62  thf('69', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.44/0.62           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.44/0.62      inference('sup-', [status(thm)], ['67', '68'])).
% 0.44/0.62  thf('70', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_C_1)
% 0.44/0.62           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['12', '15'])).
% 0.44/0.62  thf('71', plain,
% 0.44/0.62      (((k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ sk_C_1)
% 0.44/0.62         = (k3_xboole_0 @ sk_C_1 @ sk_B))),
% 0.44/0.62      inference('sup+', [status(thm)], ['69', '70'])).
% 0.44/0.62  thf('72', plain,
% 0.44/0.62      (((k2_pre_topc @ sk_A @ sk_C_1)
% 0.44/0.62         != (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_C_1 @ sk_B)))),
% 0.44/0.62      inference('demod', [status(thm)], ['66', '71'])).
% 0.44/0.62  thf('73', plain,
% 0.44/0.62      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.62  thf('74', plain,
% 0.44/0.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.44/0.62         (((k9_subset_1 @ X18 @ X16 @ X17) = (k3_xboole_0 @ X16 @ X17))
% 0.44/0.62          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.44/0.62      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.44/0.62  thf('75', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1)
% 0.44/0.62           = (k3_xboole_0 @ X0 @ sk_C_1))),
% 0.44/0.62      inference('sup-', [status(thm)], ['73', '74'])).
% 0.44/0.62  thf('76', plain,
% 0.44/0.62      (![X19 : $i]:
% 0.44/0.62         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.44/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.62  thf('77', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.44/0.62           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['60', '61'])).
% 0.44/0.62  thf('78', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.44/0.62            = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))
% 0.44/0.62          | ~ (l1_struct_0 @ sk_A))),
% 0.44/0.62      inference('sup+', [status(thm)], ['76', '77'])).
% 0.44/0.62  thf('79', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.44/0.62  thf('80', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.44/0.62           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['78', '79'])).
% 0.44/0.62  thf('81', plain,
% 0.44/0.62      (((k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C_1 @ sk_B)
% 0.44/0.62         = (k3_xboole_0 @ sk_B @ sk_C_1))),
% 0.44/0.62      inference('sup+', [status(thm)], ['75', '80'])).
% 0.44/0.62  thf('82', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1)
% 0.44/0.62           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['9', '10'])).
% 0.44/0.62  thf('83', plain,
% 0.44/0.62      (![X19 : $i]:
% 0.44/0.62         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.44/0.62      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.62  thf('84', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.44/0.62           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.44/0.62      inference('sup-', [status(thm)], ['60', '61'])).
% 0.44/0.62  thf('85', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.44/0.62            = (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ X0))
% 0.44/0.62          | ~ (l1_struct_0 @ sk_A))),
% 0.44/0.62      inference('sup+', [status(thm)], ['83', '84'])).
% 0.44/0.62  thf('86', plain, ((l1_struct_0 @ sk_A)),
% 0.44/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.44/0.62  thf('87', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.44/0.62           = (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['85', '86'])).
% 0.44/0.62  thf('88', plain,
% 0.44/0.62      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C_1)
% 0.44/0.62         = (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ sk_C_1))),
% 0.44/0.62      inference('sup+', [status(thm)], ['82', '87'])).
% 0.44/0.62  thf('89', plain,
% 0.44/0.62      (![X0 : $i]:
% 0.44/0.62         ((k9_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.44/0.62           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 0.44/0.62      inference('demod', [status(thm)], ['78', '79'])).
% 0.44/0.62  thf('90', plain,
% 0.44/0.62      (((k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C_1 @ sk_B)
% 0.44/0.62         = (k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ sk_C_1))),
% 0.44/0.62      inference('demod', [status(thm)], ['88', '89'])).
% 0.44/0.62  thf('91', plain,
% 0.44/0.62      (((k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B @ sk_C_1)
% 0.44/0.62         = (k3_xboole_0 @ sk_C_1 @ sk_B))),
% 0.44/0.62      inference('sup+', [status(thm)], ['69', '70'])).
% 0.44/0.62  thf('92', plain,
% 0.44/0.62      (((k9_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C_1 @ sk_B)
% 0.44/0.62         = (k3_xboole_0 @ sk_C_1 @ sk_B))),
% 0.44/0.62      inference('demod', [status(thm)], ['90', '91'])).
% 0.44/0.62  thf('93', plain,
% 0.44/0.62      (((k3_xboole_0 @ sk_B @ sk_C_1) = (k3_xboole_0 @ sk_C_1 @ sk_B))),
% 0.44/0.62      inference('sup+', [status(thm)], ['81', '92'])).
% 0.44/0.62  thf('94', plain,
% 0.44/0.62      (((k2_pre_topc @ sk_A @ sk_C_1)
% 0.44/0.62         != (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)))),
% 0.44/0.62      inference('demod', [status(thm)], ['72', '93'])).
% 0.44/0.62  thf('95', plain, ($false),
% 0.44/0.62      inference('simplify_reflect-', [status(thm)], ['57', '94'])).
% 0.44/0.62  
% 0.44/0.62  % SZS output end Refutation
% 0.44/0.62  
% 0.44/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
