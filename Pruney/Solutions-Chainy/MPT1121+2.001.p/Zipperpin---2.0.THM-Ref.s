%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rESj2c16FI

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:20 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 523 expanded)
%              Number of leaves         :   24 ( 143 expanded)
%              Depth                    :   27
%              Number of atoms          : 1478 (8482 expanded)
%              Number of equality atoms :   53 ( 512 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t52_pre_topc,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( v4_pre_topc @ B @ A )
               => ( ( k2_pre_topc @ A @ B )
                  = B ) )
              & ( ( ( v2_pre_topc @ A )
                  & ( ( k2_pre_topc @ A @ B )
                    = B ) )
               => ( v4_pre_topc @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_pre_topc])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r1_tarski @ X21 @ ( k2_pre_topc @ X22 @ X21 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t45_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( r2_hidden @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( ( v4_pre_topc @ D @ A )
                        & ( r1_tarski @ B @ D ) )
                     => ( r2_hidden @ C @ D ) ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( r2_hidden @ X16 @ ( k2_pre_topc @ X15 @ X14 ) )
      | ~ ( v4_pre_topc @ X17 @ X15 )
      | ~ ( r1_tarski @ X14 @ X17 )
      | ( r2_hidden @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( r2_hidden @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t45_pre_topc])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_tarski @ sk_B @ X1 )
      | ~ ( v4_pre_topc @ X1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_tarski @ sk_B @ X1 )
      | ~ ( v4_pre_topc @ X1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( v4_pre_topc @ sk_B @ sk_A )
      | ~ ( r1_tarski @ sk_B @ sk_B )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ( v2_pre_topc @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v2_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ( v2_pre_topc @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ? [C: $i] :
              ( ( ( k2_pre_topc @ A @ B )
                = ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ C ) )
              & ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( r2_hidden @ D @ C )
                  <=> ( ( v4_pre_topc @ D @ A )
                      & ( r1_tarski @ B @ D ) ) ) )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( sk_C_2 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t46_pre_topc])).

thf('24',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( m1_subset_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf(t44_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r2_hidden @ C @ B )
                 => ( v4_pre_topc @ C @ A ) ) )
           => ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ X13 ) @ X12 ) @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X13 ) @ X12 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t44_pre_topc])).

thf('29',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v2_pre_topc @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( r2_hidden @ ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( v2_pre_topc @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k2_pre_topc @ X19 @ X18 )
        = ( k6_setfam_1 @ ( u1_struct_0 @ X19 ) @ ( sk_C_2 @ X18 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t46_pre_topc])).

thf('36',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,
    ( ( ( r2_hidden @ ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['32','39'])).

thf('41',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('42',plain,
    ( ( v2_pre_topc @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('45',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( sk_C_2 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t46_pre_topc])).

thf('49',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_C_2 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( sk_C_2 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( m1_subset_1 @ ( sk_C_2 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['42','51'])).

thf('53',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ X13 ) @ X12 ) @ X13 )
      | ( m1_subset_1 @ ( sk_C_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t44_pre_topc])).

thf('54',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_subset_1 @ ( sk_C_1 @ ( sk_C_2 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_2 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v2_pre_topc @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( m1_subset_1 @ ( sk_C_1 @ ( sk_C_2 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_2 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( v2_pre_topc @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('59',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('60',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k2_pre_topc @ X19 @ X18 )
        = ( k6_setfam_1 @ ( u1_struct_0 @ X19 ) @ ( sk_C_2 @ X18 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t46_pre_topc])).

thf('61',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_2 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_2 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_2 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,
    ( ( ( m1_subset_1 @ ( sk_C_1 @ ( sk_C_2 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['57','64'])).

thf('66',plain,
    ( ( ( m1_subset_1 @ ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ) )
   <= ( ( ( k2_pre_topc @ sk_A @ sk_B )
        = sk_B )
      & ( v2_pre_topc @ sk_A ) ) ),
    inference('sup+',[status(thm)],['41','65'])).

thf('67',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('68',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('69',plain,
    ( ( ( m1_subset_1 @ ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( ( k2_pre_topc @ sk_A @ sk_B )
        = sk_B )
      & ( v2_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( v2_pre_topc @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v4_pre_topc @ X20 @ X19 )
      | ~ ( r2_hidden @ X20 @ ( sk_C_2 @ X18 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t46_pre_topc])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( sk_C_2 @ sk_B @ sk_A ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( sk_C_2 @ sk_B @ sk_A ) )
      | ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( sk_C_2 @ sk_B @ sk_A ) ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,
    ( ( ( v4_pre_topc @ sk_B @ sk_A )
      | ~ ( r2_hidden @ ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) )
      | ( v4_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
   <= ( ( ( k2_pre_topc @ sk_A @ sk_B )
        = sk_B )
      & ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','76'])).

thf('78',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('79',plain,
    ( ( m1_subset_1 @ ( sk_C_2 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['42','51'])).

thf('80',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ X13 ) @ X12 ) @ X13 )
      | ~ ( v4_pre_topc @ ( sk_C_1 @ X12 @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t44_pre_topc])).

thf('81',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v4_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_2 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( v2_pre_topc @ sk_A )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ~ ( v4_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
      | ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_2 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = ( k6_setfam_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C_2 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('86',plain,
    ( ( ~ ( v4_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) @ sk_A ) @ sk_A )
      | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ) )
   <= ( v2_pre_topc @ sk_A ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ~ ( v4_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_A ) )
   <= ( ( ( k2_pre_topc @ sk_A @ sk_B )
        = sk_B )
      & ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','86'])).

thf('88',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('89',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('90',plain,
    ( ( ~ ( v4_pre_topc @ ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( ( k2_pre_topc @ sk_A @ sk_B )
        = sk_B )
      & ( v2_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,
    ( ( ~ ( r2_hidden @ ( sk_C_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ) @ ( sk_C_2 @ sk_B @ sk_A ) )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( ( k2_pre_topc @ sk_A @ sk_B )
        = sk_B )
      & ( v2_pre_topc @ sk_A ) ) ),
    inference(clc,[status(thm)],['77','90'])).

thf('92',plain,
    ( ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( ( k2_pre_topc @ sk_A @ sk_B )
        = sk_B )
      & ( v2_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','91'])).

thf('93',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('94',plain,
    ( ( ( v4_pre_topc @ sk_B @ sk_A )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( ( k2_pre_topc @ sk_A @ sk_B )
        = sk_B )
      & ( v2_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( ( k2_pre_topc @ sk_A @ sk_B )
        = sk_B )
      & ( v2_pre_topc @ sk_A ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['17'])).

thf('97',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('99',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['18','20','97','98'])).

thf('100',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(simpl_trail,[status(thm)],['16','99'])).

thf('101',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('102',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['14','100','102'])).

thf('104',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('105',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['103','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','107'])).

thf('109',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('110',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['6','111'])).

thf('113',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
   <= ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf('114',plain,(
    ( k2_pre_topc @ sk_A @ sk_B )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['18','20','97'])).

thf('115',plain,(
    ( k2_pre_topc @ sk_A @ sk_B )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['113','114'])).

thf('116',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['112','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rESj2c16FI
% 0.15/0.39  % Computer   : n020.cluster.edu
% 0.15/0.39  % Model      : x86_64 x86_64
% 0.15/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.39  % Memory     : 8042.1875MB
% 0.15/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.39  % CPULimit   : 60
% 0.15/0.39  % DateTime   : Tue Dec  1 13:34:52 EST 2020
% 0.15/0.39  % CPUTime    : 
% 0.15/0.39  % Running portfolio for 600 s
% 0.15/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.39  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.53/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.70  % Solved by: fo/fo7.sh
% 0.53/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.70  % done 361 iterations in 0.201s
% 0.53/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.70  % SZS output start Refutation
% 0.53/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.70  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.53/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.53/0.70  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.53/0.70  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.53/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.70  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.53/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.53/0.70  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.53/0.70  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.53/0.70  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.53/0.70  thf(t52_pre_topc, conjecture,
% 0.53/0.70    (![A:$i]:
% 0.53/0.70     ( ( l1_pre_topc @ A ) =>
% 0.53/0.70       ( ![B:$i]:
% 0.53/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.70           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.53/0.70             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.53/0.70               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.53/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.70    (~( ![A:$i]:
% 0.53/0.70        ( ( l1_pre_topc @ A ) =>
% 0.53/0.70          ( ![B:$i]:
% 0.53/0.70            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.70              ( ( ( v4_pre_topc @ B @ A ) =>
% 0.53/0.70                  ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.53/0.70                ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.53/0.70                  ( v4_pre_topc @ B @ A ) ) ) ) ) ) )),
% 0.53/0.70    inference('cnf.neg', [status(esa)], [t52_pre_topc])).
% 0.53/0.70  thf('0', plain,
% 0.53/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf(t48_pre_topc, axiom,
% 0.53/0.70    (![A:$i]:
% 0.53/0.70     ( ( l1_pre_topc @ A ) =>
% 0.53/0.70       ( ![B:$i]:
% 0.53/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.70           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.53/0.70  thf('1', plain,
% 0.53/0.70      (![X21 : $i, X22 : $i]:
% 0.53/0.70         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.53/0.70          | (r1_tarski @ X21 @ (k2_pre_topc @ X22 @ X21))
% 0.53/0.70          | ~ (l1_pre_topc @ X22))),
% 0.53/0.70      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.53/0.70  thf('2', plain,
% 0.53/0.70      ((~ (l1_pre_topc @ sk_A)
% 0.53/0.70        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.53/0.70      inference('sup-', [status(thm)], ['0', '1'])).
% 0.53/0.70  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('4', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.53/0.70      inference('demod', [status(thm)], ['2', '3'])).
% 0.53/0.70  thf(d10_xboole_0, axiom,
% 0.53/0.70    (![A:$i,B:$i]:
% 0.53/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.53/0.70  thf('5', plain,
% 0.53/0.70      (![X4 : $i, X6 : $i]:
% 0.53/0.70         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.53/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.70  thf('6', plain,
% 0.53/0.70      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 0.53/0.70        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))),
% 0.53/0.70      inference('sup-', [status(thm)], ['4', '5'])).
% 0.53/0.70  thf(d3_tarski, axiom,
% 0.53/0.70    (![A:$i,B:$i]:
% 0.53/0.70     ( ( r1_tarski @ A @ B ) <=>
% 0.53/0.70       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.53/0.70  thf('7', plain,
% 0.53/0.70      (![X1 : $i, X3 : $i]:
% 0.53/0.70         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.53/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.70  thf('8', plain,
% 0.53/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('9', plain,
% 0.53/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf(t45_pre_topc, axiom,
% 0.53/0.70    (![A:$i]:
% 0.53/0.70     ( ( l1_pre_topc @ A ) =>
% 0.53/0.70       ( ![B:$i]:
% 0.53/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.70           ( ![C:$i]:
% 0.53/0.70             ( ( r2_hidden @ C @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.70               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 0.53/0.70                 ( ![D:$i]:
% 0.53/0.70                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.70                     ( ( ( v4_pre_topc @ D @ A ) & ( r1_tarski @ B @ D ) ) =>
% 0.53/0.70                       ( r2_hidden @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.53/0.70  thf('10', plain,
% 0.53/0.70      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.53/0.70         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.53/0.70          | ~ (r2_hidden @ X16 @ (k2_pre_topc @ X15 @ X14))
% 0.53/0.70          | ~ (v4_pre_topc @ X17 @ X15)
% 0.53/0.70          | ~ (r1_tarski @ X14 @ X17)
% 0.53/0.70          | (r2_hidden @ X16 @ X17)
% 0.53/0.70          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.53/0.70          | ~ (r2_hidden @ X16 @ (u1_struct_0 @ X15))
% 0.53/0.70          | ~ (l1_pre_topc @ X15))),
% 0.53/0.70      inference('cnf', [status(esa)], [t45_pre_topc])).
% 0.53/0.70  thf('11', plain,
% 0.53/0.70      (![X0 : $i, X1 : $i]:
% 0.53/0.70         (~ (l1_pre_topc @ sk_A)
% 0.53/0.70          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.53/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.53/0.70          | (r2_hidden @ X0 @ X1)
% 0.53/0.70          | ~ (r1_tarski @ sk_B @ X1)
% 0.53/0.70          | ~ (v4_pre_topc @ X1 @ sk_A)
% 0.53/0.70          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.53/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.53/0.70  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('13', plain,
% 0.53/0.70      (![X0 : $i, X1 : $i]:
% 0.53/0.70         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.53/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.53/0.70          | (r2_hidden @ X0 @ X1)
% 0.53/0.70          | ~ (r1_tarski @ sk_B @ X1)
% 0.53/0.70          | ~ (v4_pre_topc @ X1 @ sk_A)
% 0.53/0.70          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.53/0.70      inference('demod', [status(thm)], ['11', '12'])).
% 0.53/0.70  thf('14', plain,
% 0.53/0.70      (![X0 : $i]:
% 0.53/0.70         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.53/0.70          | ~ (v4_pre_topc @ sk_B @ sk_A)
% 0.53/0.70          | ~ (r1_tarski @ sk_B @ sk_B)
% 0.53/0.70          | (r2_hidden @ X0 @ sk_B)
% 0.53/0.70          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.70      inference('sup-', [status(thm)], ['8', '13'])).
% 0.53/0.70  thf('15', plain,
% 0.53/0.70      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('16', plain,
% 0.53/0.70      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.70      inference('split', [status(esa)], ['15'])).
% 0.53/0.70  thf('17', plain,
% 0.53/0.70      ((((k2_pre_topc @ sk_A @ sk_B) != (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('18', plain,
% 0.53/0.70      (~ (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))) | 
% 0.53/0.70       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 0.53/0.70      inference('split', [status(esa)], ['17'])).
% 0.53/0.70  thf('19', plain,
% 0.53/0.70      ((((k2_pre_topc @ sk_A @ sk_B) != (sk_B)) | (v2_pre_topc @ sk_A))),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('20', plain,
% 0.53/0.70      (((v2_pre_topc @ sk_A)) | ~ (((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))),
% 0.53/0.70      inference('split', [status(esa)], ['19'])).
% 0.53/0.70  thf('21', plain, (((v2_pre_topc @ sk_A)) <= (((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('split', [status(esa)], ['19'])).
% 0.53/0.70  thf('22', plain,
% 0.53/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf(t46_pre_topc, axiom,
% 0.53/0.70    (![A:$i]:
% 0.53/0.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.70       ( ![B:$i]:
% 0.53/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.70           ( ?[C:$i]:
% 0.53/0.70             ( ( ( k2_pre_topc @ A @ B ) =
% 0.53/0.70                 ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ C ) ) & 
% 0.53/0.70               ( ![D:$i]:
% 0.53/0.70                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.70                   ( ( r2_hidden @ D @ C ) <=>
% 0.53/0.70                     ( ( v4_pre_topc @ D @ A ) & ( r1_tarski @ B @ D ) ) ) ) ) & 
% 0.53/0.70               ( m1_subset_1 @
% 0.53/0.70                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.53/0.70  thf('23', plain,
% 0.53/0.70      (![X18 : $i, X19 : $i]:
% 0.53/0.70         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.53/0.70          | (m1_subset_1 @ (sk_C_2 @ X18 @ X19) @ 
% 0.53/0.70             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))
% 0.53/0.70          | ~ (l1_pre_topc @ X19)
% 0.53/0.70          | ~ (v2_pre_topc @ X19))),
% 0.53/0.70      inference('cnf', [status(esa)], [t46_pre_topc])).
% 0.53/0.70  thf('24', plain,
% 0.53/0.70      ((~ (v2_pre_topc @ sk_A)
% 0.53/0.70        | ~ (l1_pre_topc @ sk_A)
% 0.53/0.70        | (m1_subset_1 @ (sk_C_2 @ sk_B @ sk_A) @ 
% 0.53/0.70           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.53/0.70      inference('sup-', [status(thm)], ['22', '23'])).
% 0.53/0.70  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('26', plain,
% 0.53/0.70      ((~ (v2_pre_topc @ sk_A)
% 0.53/0.70        | (m1_subset_1 @ (sk_C_2 @ sk_B @ sk_A) @ 
% 0.53/0.70           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.53/0.70      inference('demod', [status(thm)], ['24', '25'])).
% 0.53/0.70  thf('27', plain,
% 0.53/0.70      (((m1_subset_1 @ (sk_C_2 @ sk_B @ sk_A) @ 
% 0.53/0.70         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.53/0.70         <= (((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('sup-', [status(thm)], ['21', '26'])).
% 0.53/0.70  thf(t44_pre_topc, axiom,
% 0.53/0.70    (![A:$i]:
% 0.53/0.70     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.53/0.70       ( ![B:$i]:
% 0.53/0.70         ( ( m1_subset_1 @
% 0.53/0.70             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.53/0.70           ( ( ![C:$i]:
% 0.53/0.70               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.53/0.70                 ( ( r2_hidden @ C @ B ) => ( v4_pre_topc @ C @ A ) ) ) ) =>
% 0.53/0.70             ( v4_pre_topc @ ( k6_setfam_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.53/0.70  thf('28', plain,
% 0.53/0.70      (![X12 : $i, X13 : $i]:
% 0.53/0.70         (~ (m1_subset_1 @ X12 @ 
% 0.53/0.70             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 0.53/0.70          | (v4_pre_topc @ (k6_setfam_1 @ (u1_struct_0 @ X13) @ X12) @ X13)
% 0.53/0.70          | (r2_hidden @ (sk_C_1 @ X12 @ X13) @ X12)
% 0.53/0.70          | ~ (l1_pre_topc @ X13)
% 0.53/0.70          | ~ (v2_pre_topc @ X13))),
% 0.53/0.70      inference('cnf', [status(esa)], [t44_pre_topc])).
% 0.53/0.70  thf('29', plain,
% 0.53/0.70      (((~ (v2_pre_topc @ sk_A)
% 0.53/0.70         | ~ (l1_pre_topc @ sk_A)
% 0.53/0.70         | (r2_hidden @ (sk_C_1 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A) @ 
% 0.53/0.70            (sk_C_2 @ sk_B @ sk_A))
% 0.53/0.70         | (v4_pre_topc @ 
% 0.53/0.70            (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ (sk_C_2 @ sk_B @ sk_A)) @ 
% 0.53/0.70            sk_A)))
% 0.53/0.70         <= (((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('sup-', [status(thm)], ['27', '28'])).
% 0.53/0.70  thf('30', plain, (((v2_pre_topc @ sk_A)) <= (((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('split', [status(esa)], ['19'])).
% 0.53/0.70  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('32', plain,
% 0.53/0.70      ((((r2_hidden @ (sk_C_1 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A) @ 
% 0.53/0.70          (sk_C_2 @ sk_B @ sk_A))
% 0.53/0.70         | (v4_pre_topc @ 
% 0.53/0.70            (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ (sk_C_2 @ sk_B @ sk_A)) @ 
% 0.53/0.70            sk_A)))
% 0.53/0.70         <= (((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.53/0.70  thf('33', plain, (((v2_pre_topc @ sk_A)) <= (((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('split', [status(esa)], ['19'])).
% 0.53/0.70  thf('34', plain,
% 0.53/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('35', plain,
% 0.53/0.70      (![X18 : $i, X19 : $i]:
% 0.53/0.70         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.53/0.70          | ((k2_pre_topc @ X19 @ X18)
% 0.53/0.70              = (k6_setfam_1 @ (u1_struct_0 @ X19) @ (sk_C_2 @ X18 @ X19)))
% 0.53/0.70          | ~ (l1_pre_topc @ X19)
% 0.53/0.70          | ~ (v2_pre_topc @ X19))),
% 0.53/0.70      inference('cnf', [status(esa)], [t46_pre_topc])).
% 0.53/0.70  thf('36', plain,
% 0.53/0.70      ((~ (v2_pre_topc @ sk_A)
% 0.53/0.70        | ~ (l1_pre_topc @ sk_A)
% 0.53/0.70        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.53/0.70            = (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ (sk_C_2 @ sk_B @ sk_A))))),
% 0.53/0.70      inference('sup-', [status(thm)], ['34', '35'])).
% 0.53/0.70  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('38', plain,
% 0.53/0.70      ((~ (v2_pre_topc @ sk_A)
% 0.53/0.70        | ((k2_pre_topc @ sk_A @ sk_B)
% 0.53/0.70            = (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ (sk_C_2 @ sk_B @ sk_A))))),
% 0.53/0.70      inference('demod', [status(thm)], ['36', '37'])).
% 0.53/0.70  thf('39', plain,
% 0.53/0.70      ((((k2_pre_topc @ sk_A @ sk_B)
% 0.53/0.70          = (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ (sk_C_2 @ sk_B @ sk_A))))
% 0.53/0.70         <= (((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('sup-', [status(thm)], ['33', '38'])).
% 0.53/0.70  thf('40', plain,
% 0.53/0.70      ((((r2_hidden @ (sk_C_1 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A) @ 
% 0.53/0.70          (sk_C_2 @ sk_B @ sk_A))
% 0.53/0.70         | (v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)))
% 0.53/0.70         <= (((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('demod', [status(thm)], ['32', '39'])).
% 0.53/0.70  thf('41', plain,
% 0.53/0.70      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.53/0.70         <= ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B))))),
% 0.53/0.70      inference('split', [status(esa)], ['15'])).
% 0.53/0.70  thf('42', plain, (((v2_pre_topc @ sk_A)) <= (((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('split', [status(esa)], ['19'])).
% 0.53/0.70  thf('43', plain,
% 0.53/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf(dt_k2_pre_topc, axiom,
% 0.53/0.70    (![A:$i,B:$i]:
% 0.53/0.70     ( ( ( l1_pre_topc @ A ) & 
% 0.53/0.70         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.53/0.70       ( m1_subset_1 @
% 0.53/0.70         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.53/0.70  thf('44', plain,
% 0.53/0.70      (![X10 : $i, X11 : $i]:
% 0.53/0.70         (~ (l1_pre_topc @ X10)
% 0.53/0.70          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.53/0.70          | (m1_subset_1 @ (k2_pre_topc @ X10 @ X11) @ 
% 0.53/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X10))))),
% 0.53/0.70      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.53/0.70  thf('45', plain,
% 0.53/0.70      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.53/0.70         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.53/0.70        | ~ (l1_pre_topc @ sk_A))),
% 0.53/0.70      inference('sup-', [status(thm)], ['43', '44'])).
% 0.53/0.70  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('47', plain,
% 0.53/0.70      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.53/0.70        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.70      inference('demod', [status(thm)], ['45', '46'])).
% 0.53/0.70  thf('48', plain,
% 0.53/0.70      (![X18 : $i, X19 : $i]:
% 0.53/0.70         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.53/0.70          | (m1_subset_1 @ (sk_C_2 @ X18 @ X19) @ 
% 0.53/0.70             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))
% 0.53/0.70          | ~ (l1_pre_topc @ X19)
% 0.53/0.70          | ~ (v2_pre_topc @ X19))),
% 0.53/0.70      inference('cnf', [status(esa)], [t46_pre_topc])).
% 0.53/0.70  thf('49', plain,
% 0.53/0.70      ((~ (v2_pre_topc @ sk_A)
% 0.53/0.70        | ~ (l1_pre_topc @ sk_A)
% 0.53/0.70        | (m1_subset_1 @ (sk_C_2 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A) @ 
% 0.53/0.70           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.53/0.70      inference('sup-', [status(thm)], ['47', '48'])).
% 0.53/0.70  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('51', plain,
% 0.53/0.70      ((~ (v2_pre_topc @ sk_A)
% 0.53/0.70        | (m1_subset_1 @ (sk_C_2 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A) @ 
% 0.53/0.70           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.53/0.70      inference('demod', [status(thm)], ['49', '50'])).
% 0.53/0.70  thf('52', plain,
% 0.53/0.70      (((m1_subset_1 @ (sk_C_2 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A) @ 
% 0.53/0.70         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.53/0.70         <= (((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('sup-', [status(thm)], ['42', '51'])).
% 0.53/0.70  thf('53', plain,
% 0.53/0.70      (![X12 : $i, X13 : $i]:
% 0.53/0.70         (~ (m1_subset_1 @ X12 @ 
% 0.53/0.70             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 0.53/0.70          | (v4_pre_topc @ (k6_setfam_1 @ (u1_struct_0 @ X13) @ X12) @ X13)
% 0.53/0.70          | (m1_subset_1 @ (sk_C_1 @ X12 @ X13) @ 
% 0.53/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.53/0.70          | ~ (l1_pre_topc @ X13)
% 0.53/0.70          | ~ (v2_pre_topc @ X13))),
% 0.53/0.70      inference('cnf', [status(esa)], [t44_pre_topc])).
% 0.53/0.70  thf('54', plain,
% 0.53/0.70      (((~ (v2_pre_topc @ sk_A)
% 0.53/0.70         | ~ (l1_pre_topc @ sk_A)
% 0.53/0.70         | (m1_subset_1 @ 
% 0.53/0.70            (sk_C_1 @ (sk_C_2 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A) @ sk_A) @ 
% 0.53/0.70            (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.53/0.70         | (v4_pre_topc @ 
% 0.53/0.70            (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.70             (sk_C_2 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)) @ 
% 0.53/0.70            sk_A)))
% 0.53/0.70         <= (((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('sup-', [status(thm)], ['52', '53'])).
% 0.53/0.70  thf('55', plain, (((v2_pre_topc @ sk_A)) <= (((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('split', [status(esa)], ['19'])).
% 0.53/0.70  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('57', plain,
% 0.53/0.70      ((((m1_subset_1 @ 
% 0.53/0.70          (sk_C_1 @ (sk_C_2 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A) @ sk_A) @ 
% 0.53/0.70          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.53/0.70         | (v4_pre_topc @ 
% 0.53/0.70            (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.70             (sk_C_2 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)) @ 
% 0.53/0.70            sk_A)))
% 0.53/0.70         <= (((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.53/0.70  thf('58', plain, (((v2_pre_topc @ sk_A)) <= (((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('split', [status(esa)], ['19'])).
% 0.53/0.70  thf('59', plain,
% 0.53/0.70      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.53/0.70        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.70      inference('demod', [status(thm)], ['45', '46'])).
% 0.53/0.70  thf('60', plain,
% 0.53/0.70      (![X18 : $i, X19 : $i]:
% 0.53/0.70         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.53/0.70          | ((k2_pre_topc @ X19 @ X18)
% 0.53/0.70              = (k6_setfam_1 @ (u1_struct_0 @ X19) @ (sk_C_2 @ X18 @ X19)))
% 0.53/0.70          | ~ (l1_pre_topc @ X19)
% 0.53/0.70          | ~ (v2_pre_topc @ X19))),
% 0.53/0.70      inference('cnf', [status(esa)], [t46_pre_topc])).
% 0.53/0.70  thf('61', plain,
% 0.53/0.70      ((~ (v2_pre_topc @ sk_A)
% 0.53/0.70        | ~ (l1_pre_topc @ sk_A)
% 0.53/0.70        | ((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.53/0.70            = (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.70               (sk_C_2 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))))),
% 0.53/0.70      inference('sup-', [status(thm)], ['59', '60'])).
% 0.53/0.70  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('63', plain,
% 0.53/0.70      ((~ (v2_pre_topc @ sk_A)
% 0.53/0.70        | ((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.53/0.70            = (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.70               (sk_C_2 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))))),
% 0.53/0.70      inference('demod', [status(thm)], ['61', '62'])).
% 0.53/0.70  thf('64', plain,
% 0.53/0.70      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.53/0.70          = (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.70             (sk_C_2 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))))
% 0.53/0.70         <= (((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('sup-', [status(thm)], ['58', '63'])).
% 0.53/0.70  thf('65', plain,
% 0.53/0.70      ((((m1_subset_1 @ 
% 0.53/0.70          (sk_C_1 @ (sk_C_2 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A) @ sk_A) @ 
% 0.53/0.70          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.53/0.70         | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.53/0.70            sk_A)))
% 0.53/0.70         <= (((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('demod', [status(thm)], ['57', '64'])).
% 0.53/0.70  thf('66', plain,
% 0.53/0.70      ((((m1_subset_1 @ (sk_C_1 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A) @ 
% 0.53/0.70          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.53/0.70         | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.53/0.70            sk_A)))
% 0.53/0.70         <= ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B))) & ((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('sup+', [status(thm)], ['41', '65'])).
% 0.53/0.70  thf('67', plain,
% 0.53/0.70      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.53/0.70         <= ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B))))),
% 0.53/0.70      inference('split', [status(esa)], ['15'])).
% 0.53/0.70  thf('68', plain,
% 0.53/0.70      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.53/0.70         <= ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B))))),
% 0.53/0.70      inference('split', [status(esa)], ['15'])).
% 0.53/0.70  thf('69', plain,
% 0.53/0.70      ((((m1_subset_1 @ (sk_C_1 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A) @ 
% 0.53/0.70          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.53/0.70         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.53/0.70         <= ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B))) & ((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.53/0.70  thf('70', plain, (((v2_pre_topc @ sk_A)) <= (((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('split', [status(esa)], ['19'])).
% 0.53/0.70  thf('71', plain,
% 0.53/0.70      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('72', plain,
% 0.53/0.70      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.53/0.70         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.53/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.53/0.70          | (v4_pre_topc @ X20 @ X19)
% 0.53/0.70          | ~ (r2_hidden @ X20 @ (sk_C_2 @ X18 @ X19))
% 0.53/0.70          | ~ (l1_pre_topc @ X19)
% 0.53/0.70          | ~ (v2_pre_topc @ X19))),
% 0.53/0.70      inference('cnf', [status(esa)], [t46_pre_topc])).
% 0.53/0.70  thf('73', plain,
% 0.53/0.70      (![X0 : $i]:
% 0.53/0.70         (~ (v2_pre_topc @ sk_A)
% 0.53/0.70          | ~ (l1_pre_topc @ sk_A)
% 0.53/0.70          | ~ (r2_hidden @ X0 @ (sk_C_2 @ sk_B @ sk_A))
% 0.53/0.70          | (v4_pre_topc @ X0 @ sk_A)
% 0.53/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.53/0.70      inference('sup-', [status(thm)], ['71', '72'])).
% 0.53/0.70  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('75', plain,
% 0.53/0.70      (![X0 : $i]:
% 0.53/0.70         (~ (v2_pre_topc @ sk_A)
% 0.53/0.70          | ~ (r2_hidden @ X0 @ (sk_C_2 @ sk_B @ sk_A))
% 0.53/0.70          | (v4_pre_topc @ X0 @ sk_A)
% 0.53/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.53/0.70      inference('demod', [status(thm)], ['73', '74'])).
% 0.53/0.70  thf('76', plain,
% 0.53/0.70      ((![X0 : $i]:
% 0.53/0.70          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.53/0.70           | (v4_pre_topc @ X0 @ sk_A)
% 0.53/0.70           | ~ (r2_hidden @ X0 @ (sk_C_2 @ sk_B @ sk_A))))
% 0.53/0.70         <= (((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('sup-', [status(thm)], ['70', '75'])).
% 0.53/0.70  thf('77', plain,
% 0.53/0.70      ((((v4_pre_topc @ sk_B @ sk_A)
% 0.53/0.70         | ~ (r2_hidden @ (sk_C_1 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A) @ 
% 0.53/0.70              (sk_C_2 @ sk_B @ sk_A))
% 0.53/0.70         | (v4_pre_topc @ (sk_C_1 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A) @ sk_A)))
% 0.53/0.70         <= ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B))) & ((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('sup-', [status(thm)], ['69', '76'])).
% 0.53/0.70  thf('78', plain,
% 0.53/0.70      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.53/0.70         <= ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B))))),
% 0.53/0.70      inference('split', [status(esa)], ['15'])).
% 0.53/0.70  thf('79', plain,
% 0.53/0.70      (((m1_subset_1 @ (sk_C_2 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A) @ 
% 0.53/0.70         (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.53/0.70         <= (((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('sup-', [status(thm)], ['42', '51'])).
% 0.53/0.70  thf('80', plain,
% 0.53/0.70      (![X12 : $i, X13 : $i]:
% 0.53/0.70         (~ (m1_subset_1 @ X12 @ 
% 0.53/0.70             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13))))
% 0.53/0.70          | (v4_pre_topc @ (k6_setfam_1 @ (u1_struct_0 @ X13) @ X12) @ X13)
% 0.53/0.70          | ~ (v4_pre_topc @ (sk_C_1 @ X12 @ X13) @ X13)
% 0.53/0.70          | ~ (l1_pre_topc @ X13)
% 0.53/0.70          | ~ (v2_pre_topc @ X13))),
% 0.53/0.70      inference('cnf', [status(esa)], [t44_pre_topc])).
% 0.53/0.70  thf('81', plain,
% 0.53/0.70      (((~ (v2_pre_topc @ sk_A)
% 0.53/0.70         | ~ (l1_pre_topc @ sk_A)
% 0.53/0.70         | ~ (v4_pre_topc @ 
% 0.53/0.70              (sk_C_1 @ (sk_C_2 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A) @ sk_A) @ 
% 0.53/0.70              sk_A)
% 0.53/0.70         | (v4_pre_topc @ 
% 0.53/0.70            (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.70             (sk_C_2 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)) @ 
% 0.53/0.70            sk_A)))
% 0.53/0.70         <= (((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('sup-', [status(thm)], ['79', '80'])).
% 0.53/0.70  thf('82', plain, (((v2_pre_topc @ sk_A)) <= (((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('split', [status(esa)], ['19'])).
% 0.53/0.70  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.53/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.70  thf('84', plain,
% 0.53/0.70      (((~ (v4_pre_topc @ 
% 0.53/0.70            (sk_C_1 @ (sk_C_2 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A) @ sk_A) @ 
% 0.53/0.70            sk_A)
% 0.53/0.70         | (v4_pre_topc @ 
% 0.53/0.70            (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.70             (sk_C_2 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)) @ 
% 0.53/0.70            sk_A)))
% 0.53/0.70         <= (((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.53/0.70  thf('85', plain,
% 0.53/0.70      ((((k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))
% 0.53/0.70          = (k6_setfam_1 @ (u1_struct_0 @ sk_A) @ 
% 0.53/0.70             (sk_C_2 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))))
% 0.53/0.70         <= (((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('sup-', [status(thm)], ['58', '63'])).
% 0.53/0.70  thf('86', plain,
% 0.53/0.70      (((~ (v4_pre_topc @ 
% 0.53/0.70            (sk_C_1 @ (sk_C_2 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A) @ sk_A) @ 
% 0.53/0.70            sk_A)
% 0.53/0.70         | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.53/0.70            sk_A)))
% 0.53/0.70         <= (((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('demod', [status(thm)], ['84', '85'])).
% 0.53/0.70  thf('87', plain,
% 0.53/0.70      (((~ (v4_pre_topc @ (sk_C_1 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A) @ sk_A)
% 0.53/0.70         | (v4_pre_topc @ (k2_pre_topc @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 0.53/0.70            sk_A)))
% 0.53/0.70         <= ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B))) & ((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('sup-', [status(thm)], ['78', '86'])).
% 0.53/0.70  thf('88', plain,
% 0.53/0.70      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.53/0.70         <= ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B))))),
% 0.53/0.70      inference('split', [status(esa)], ['15'])).
% 0.53/0.70  thf('89', plain,
% 0.53/0.70      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.53/0.70         <= ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B))))),
% 0.53/0.70      inference('split', [status(esa)], ['15'])).
% 0.53/0.70  thf('90', plain,
% 0.53/0.70      (((~ (v4_pre_topc @ (sk_C_1 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A) @ sk_A)
% 0.53/0.70         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.53/0.70         <= ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B))) & ((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.53/0.70  thf('91', plain,
% 0.53/0.70      (((~ (r2_hidden @ (sk_C_1 @ (sk_C_2 @ sk_B @ sk_A) @ sk_A) @ 
% 0.53/0.70            (sk_C_2 @ sk_B @ sk_A))
% 0.53/0.70         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.53/0.70         <= ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B))) & ((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('clc', [status(thm)], ['77', '90'])).
% 0.53/0.70  thf('92', plain,
% 0.53/0.70      ((((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.53/0.70         | (v4_pre_topc @ sk_B @ sk_A)))
% 0.53/0.70         <= ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B))) & ((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('sup-', [status(thm)], ['40', '91'])).
% 0.53/0.70  thf('93', plain,
% 0.53/0.70      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 0.53/0.70         <= ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B))))),
% 0.53/0.70      inference('split', [status(esa)], ['15'])).
% 0.53/0.70  thf('94', plain,
% 0.53/0.70      ((((v4_pre_topc @ sk_B @ sk_A) | (v4_pre_topc @ sk_B @ sk_A)))
% 0.53/0.70         <= ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B))) & ((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('demod', [status(thm)], ['92', '93'])).
% 0.53/0.70  thf('95', plain,
% 0.53/0.70      (((v4_pre_topc @ sk_B @ sk_A))
% 0.53/0.70         <= ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B))) & ((v2_pre_topc @ sk_A)))),
% 0.53/0.70      inference('simplify', [status(thm)], ['94'])).
% 0.53/0.70  thf('96', plain,
% 0.53/0.70      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 0.53/0.70      inference('split', [status(esa)], ['17'])).
% 0.53/0.70  thf('97', plain,
% 0.53/0.70      (~ (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))) | ~ ((v2_pre_topc @ sk_A)) | 
% 0.53/0.70       ((v4_pre_topc @ sk_B @ sk_A))),
% 0.53/0.70      inference('sup-', [status(thm)], ['95', '96'])).
% 0.53/0.70  thf('98', plain,
% 0.53/0.70      (((v4_pre_topc @ sk_B @ sk_A)) | (((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))),
% 0.53/0.70      inference('split', [status(esa)], ['15'])).
% 0.53/0.70  thf('99', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 0.53/0.70      inference('sat_resolution*', [status(thm)], ['18', '20', '97', '98'])).
% 0.53/0.70  thf('100', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.53/0.70      inference('simpl_trail', [status(thm)], ['16', '99'])).
% 0.53/0.70  thf('101', plain,
% 0.53/0.70      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.53/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.70  thf('102', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.53/0.70      inference('simplify', [status(thm)], ['101'])).
% 0.53/0.70  thf('103', plain,
% 0.53/0.70      (![X0 : $i]:
% 0.53/0.70         (~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B))
% 0.53/0.70          | (r2_hidden @ X0 @ sk_B)
% 0.53/0.70          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.70      inference('demod', [status(thm)], ['14', '100', '102'])).
% 0.53/0.70  thf('104', plain,
% 0.53/0.70      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 0.53/0.70        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.70      inference('demod', [status(thm)], ['45', '46'])).
% 0.53/0.70  thf(l3_subset_1, axiom,
% 0.53/0.70    (![A:$i,B:$i]:
% 0.53/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.53/0.70       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.53/0.70  thf('105', plain,
% 0.53/0.70      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.53/0.70         (~ (r2_hidden @ X7 @ X8)
% 0.53/0.70          | (r2_hidden @ X7 @ X9)
% 0.53/0.70          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.53/0.70      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.53/0.70  thf('106', plain,
% 0.53/0.70      (![X0 : $i]:
% 0.53/0.70         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 0.53/0.70          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.53/0.70      inference('sup-', [status(thm)], ['104', '105'])).
% 0.53/0.70  thf('107', plain,
% 0.53/0.70      (![X0 : $i]:
% 0.53/0.70         ((r2_hidden @ X0 @ sk_B)
% 0.53/0.70          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.53/0.70      inference('clc', [status(thm)], ['103', '106'])).
% 0.53/0.70  thf('108', plain,
% 0.53/0.70      (![X0 : $i]:
% 0.53/0.70         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 0.53/0.70          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_B))),
% 0.53/0.70      inference('sup-', [status(thm)], ['7', '107'])).
% 0.53/0.70  thf('109', plain,
% 0.53/0.70      (![X1 : $i, X3 : $i]:
% 0.53/0.70         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.53/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.70  thf('110', plain,
% 0.53/0.70      (((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 0.53/0.70        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 0.53/0.70      inference('sup-', [status(thm)], ['108', '109'])).
% 0.53/0.70  thf('111', plain, ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)),
% 0.53/0.70      inference('simplify', [status(thm)], ['110'])).
% 0.53/0.70  thf('112', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.53/0.70      inference('demod', [status(thm)], ['6', '111'])).
% 0.53/0.70  thf('113', plain,
% 0.53/0.70      ((((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))
% 0.53/0.70         <= (~ (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))))),
% 0.53/0.70      inference('split', [status(esa)], ['17'])).
% 0.53/0.70  thf('114', plain, (~ (((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))),
% 0.53/0.70      inference('sat_resolution*', [status(thm)], ['18', '20', '97'])).
% 0.53/0.70  thf('115', plain, (((k2_pre_topc @ sk_A @ sk_B) != (sk_B))),
% 0.53/0.70      inference('simpl_trail', [status(thm)], ['113', '114'])).
% 0.53/0.70  thf('116', plain, ($false),
% 0.53/0.70      inference('simplify_reflect-', [status(thm)], ['112', '115'])).
% 0.53/0.70  
% 0.53/0.70  % SZS output end Refutation
% 0.53/0.70  
% 0.53/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
