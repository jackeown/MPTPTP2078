%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ENb1LYmLs3

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:46 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 164 expanded)
%              Number of leaves         :   25 (  59 expanded)
%              Depth                    :   14
%              Number of atoms          :  838 (2638 expanded)
%              Number of equality atoms :   38 ( 101 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(t34_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( v4_pre_topc @ C @ A ) )
               => ( ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) )
                  = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v4_pre_topc @ B @ A )
                    & ( v4_pre_topc @ C @ A ) )
                 => ( ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) )
                    = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t51_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ X24 @ ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ X23 @ X25 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ X24 ) @ ( k2_pre_topc @ X24 @ X23 ) @ ( k2_pre_topc @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t51_pre_topc])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v4_pre_topc @ X26 @ X27 )
      | ( ( k2_pre_topc @ X27 @ X26 )
        = X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['3','4','10'])).

thf('12',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_subset_1 @ X15 @ X13 @ X14 )
        = ( k3_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 )
      = ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v4_pre_topc @ X26 @ X27 )
      | ( ( k2_pre_topc @ X27 @ X26 )
        = X26 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_C_1 )
      = sk_C_1 )
    | ~ ( v4_pre_topc @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v4_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 )
      = ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('23',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['12','15','21','22'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,
    ( ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) )
    | ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
      = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k3_xboole_0 @ sk_B @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('35',plain,
    ( ( sk_B
      = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_B @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['26'])).

thf('38',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('40',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('41',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('44',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['38','48'])).

thf('50',plain,(
    ! [X18: $i,X20: $i] :
      ( ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('51',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('52',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r1_tarski @ X21 @ ( k2_pre_topc @ X22 @ X21 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['25','55'])).

thf('57',plain,(
    ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) )
 != ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('59',plain,(
    ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) )
 != ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('61',plain,(
    ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) )
 != ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 )
      = ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 )
      = ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('64',plain,(
    ( k2_pre_topc @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) )
 != ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['56','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ENb1LYmLs3
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:51:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.72/1.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.72/1.95  % Solved by: fo/fo7.sh
% 1.72/1.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.72/1.95  % done 1864 iterations in 1.497s
% 1.72/1.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.72/1.95  % SZS output start Refutation
% 1.72/1.95  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.72/1.95  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.72/1.95  thf(sk_B_type, type, sk_B: $i).
% 1.72/1.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.72/1.95  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.72/1.95  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.72/1.95  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.72/1.95  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.72/1.95  thf(sk_A_type, type, sk_A: $i).
% 1.72/1.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.72/1.95  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.72/1.95  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.72/1.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.72/1.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.72/1.95  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.72/1.95  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.72/1.95  thf(t34_tops_1, conjecture,
% 1.72/1.95    (![A:$i]:
% 1.72/1.95     ( ( l1_pre_topc @ A ) =>
% 1.72/1.95       ( ![B:$i]:
% 1.72/1.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.95           ( ![C:$i]:
% 1.72/1.95             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.95               ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 1.72/1.95                 ( ( k2_pre_topc @
% 1.72/1.95                     A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) =
% 1.72/1.95                   ( k9_subset_1 @
% 1.72/1.95                     ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.72/1.95                     ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ) ))).
% 1.72/1.95  thf(zf_stmt_0, negated_conjecture,
% 1.72/1.95    (~( ![A:$i]:
% 1.72/1.95        ( ( l1_pre_topc @ A ) =>
% 1.72/1.95          ( ![B:$i]:
% 1.72/1.95            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.95              ( ![C:$i]:
% 1.72/1.95                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.95                  ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 1.72/1.95                    ( ( k2_pre_topc @
% 1.72/1.95                        A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) =
% 1.72/1.95                      ( k9_subset_1 @
% 1.72/1.95                        ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.72/1.95                        ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ) ) )),
% 1.72/1.95    inference('cnf.neg', [status(esa)], [t34_tops_1])).
% 1.72/1.95  thf('0', plain,
% 1.72/1.95      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.95  thf('1', plain,
% 1.72/1.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.95  thf(t51_pre_topc, axiom,
% 1.72/1.95    (![A:$i]:
% 1.72/1.95     ( ( l1_pre_topc @ A ) =>
% 1.72/1.95       ( ![B:$i]:
% 1.72/1.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.95           ( ![C:$i]:
% 1.72/1.95             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.95               ( r1_tarski @
% 1.72/1.95                 ( k2_pre_topc @
% 1.72/1.95                   A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 1.72/1.95                 ( k9_subset_1 @
% 1.72/1.95                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 1.72/1.95                   ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 1.72/1.95  thf('2', plain,
% 1.72/1.95      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.72/1.95         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.72/1.95          | (r1_tarski @ 
% 1.72/1.95             (k2_pre_topc @ X24 @ 
% 1.72/1.95              (k9_subset_1 @ (u1_struct_0 @ X24) @ X23 @ X25)) @ 
% 1.72/1.95             (k9_subset_1 @ (u1_struct_0 @ X24) @ (k2_pre_topc @ X24 @ X23) @ 
% 1.72/1.95              (k2_pre_topc @ X24 @ X25)))
% 1.72/1.95          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.72/1.95          | ~ (l1_pre_topc @ X24))),
% 1.72/1.95      inference('cnf', [status(esa)], [t51_pre_topc])).
% 1.72/1.95  thf('3', plain,
% 1.72/1.95      (![X0 : $i]:
% 1.72/1.95         (~ (l1_pre_topc @ sk_A)
% 1.72/1.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.72/1.95          | (r1_tarski @ 
% 1.72/1.95             (k2_pre_topc @ sk_A @ 
% 1.72/1.95              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)) @ 
% 1.72/1.95             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.95              (k2_pre_topc @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ X0))))),
% 1.72/1.95      inference('sup-', [status(thm)], ['1', '2'])).
% 1.72/1.95  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.95  thf('5', plain,
% 1.72/1.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.95  thf(t52_pre_topc, axiom,
% 1.72/1.95    (![A:$i]:
% 1.72/1.95     ( ( l1_pre_topc @ A ) =>
% 1.72/1.95       ( ![B:$i]:
% 1.72/1.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.95           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.72/1.95             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.72/1.95               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.72/1.95  thf('6', plain,
% 1.72/1.95      (![X26 : $i, X27 : $i]:
% 1.72/1.95         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.72/1.95          | ~ (v4_pre_topc @ X26 @ X27)
% 1.72/1.95          | ((k2_pre_topc @ X27 @ X26) = (X26))
% 1.72/1.95          | ~ (l1_pre_topc @ X27))),
% 1.72/1.95      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.72/1.95  thf('7', plain,
% 1.72/1.95      ((~ (l1_pre_topc @ sk_A)
% 1.72/1.95        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 1.72/1.95        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.72/1.95      inference('sup-', [status(thm)], ['5', '6'])).
% 1.72/1.95  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.95  thf('9', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 1.72/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.95  thf('10', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 1.72/1.95      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.72/1.95  thf('11', plain,
% 1.72/1.95      (![X0 : $i]:
% 1.72/1.95         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.72/1.95          | (r1_tarski @ 
% 1.72/1.95             (k2_pre_topc @ sk_A @ 
% 1.72/1.95              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)) @ 
% 1.72/1.95             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.95              (k2_pre_topc @ sk_A @ X0))))),
% 1.72/1.95      inference('demod', [status(thm)], ['3', '4', '10'])).
% 1.72/1.95  thf('12', plain,
% 1.72/1.95      ((r1_tarski @ 
% 1.72/1.95        (k2_pre_topc @ sk_A @ 
% 1.72/1.95         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C_1)) @ 
% 1.72/1.95        (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.95         (k2_pre_topc @ sk_A @ sk_C_1)))),
% 1.72/1.95      inference('sup-', [status(thm)], ['0', '11'])).
% 1.72/1.95  thf('13', plain,
% 1.72/1.95      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.95  thf(redefinition_k9_subset_1, axiom,
% 1.72/1.95    (![A:$i,B:$i,C:$i]:
% 1.72/1.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.72/1.95       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.72/1.95  thf('14', plain,
% 1.72/1.95      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.72/1.95         (((k9_subset_1 @ X15 @ X13 @ X14) = (k3_xboole_0 @ X13 @ X14))
% 1.72/1.95          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 1.72/1.95      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.72/1.95  thf('15', plain,
% 1.72/1.95      (![X0 : $i]:
% 1.72/1.95         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1)
% 1.72/1.95           = (k3_xboole_0 @ X0 @ sk_C_1))),
% 1.72/1.95      inference('sup-', [status(thm)], ['13', '14'])).
% 1.72/1.95  thf('16', plain,
% 1.72/1.95      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.95  thf('17', plain,
% 1.72/1.95      (![X26 : $i, X27 : $i]:
% 1.72/1.95         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.72/1.95          | ~ (v4_pre_topc @ X26 @ X27)
% 1.72/1.95          | ((k2_pre_topc @ X27 @ X26) = (X26))
% 1.72/1.95          | ~ (l1_pre_topc @ X27))),
% 1.72/1.95      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.72/1.95  thf('18', plain,
% 1.72/1.95      ((~ (l1_pre_topc @ sk_A)
% 1.72/1.95        | ((k2_pre_topc @ sk_A @ sk_C_1) = (sk_C_1))
% 1.72/1.95        | ~ (v4_pre_topc @ sk_C_1 @ sk_A))),
% 1.72/1.95      inference('sup-', [status(thm)], ['16', '17'])).
% 1.72/1.95  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.95  thf('20', plain, ((v4_pre_topc @ sk_C_1 @ sk_A)),
% 1.72/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.95  thf('21', plain, (((k2_pre_topc @ sk_A @ sk_C_1) = (sk_C_1))),
% 1.72/1.95      inference('demod', [status(thm)], ['18', '19', '20'])).
% 1.72/1.95  thf('22', plain,
% 1.72/1.95      (![X0 : $i]:
% 1.72/1.95         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1)
% 1.72/1.95           = (k3_xboole_0 @ X0 @ sk_C_1))),
% 1.72/1.95      inference('sup-', [status(thm)], ['13', '14'])).
% 1.72/1.95  thf('23', plain,
% 1.72/1.95      ((r1_tarski @ (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)) @ 
% 1.72/1.95        (k3_xboole_0 @ sk_B @ sk_C_1))),
% 1.72/1.95      inference('demod', [status(thm)], ['12', '15', '21', '22'])).
% 1.72/1.95  thf(d10_xboole_0, axiom,
% 1.72/1.95    (![A:$i,B:$i]:
% 1.72/1.95     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.72/1.95  thf('24', plain,
% 1.72/1.95      (![X10 : $i, X12 : $i]:
% 1.72/1.95         (((X10) = (X12))
% 1.72/1.95          | ~ (r1_tarski @ X12 @ X10)
% 1.72/1.95          | ~ (r1_tarski @ X10 @ X12))),
% 1.72/1.95      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.72/1.95  thf('25', plain,
% 1.72/1.95      ((~ (r1_tarski @ (k3_xboole_0 @ sk_B @ sk_C_1) @ 
% 1.72/1.95           (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)))
% 1.72/1.95        | ((k3_xboole_0 @ sk_B @ sk_C_1)
% 1.72/1.95            = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1))))),
% 1.72/1.95      inference('sup-', [status(thm)], ['23', '24'])).
% 1.72/1.95  thf(d4_xboole_0, axiom,
% 1.72/1.95    (![A:$i,B:$i,C:$i]:
% 1.72/1.95     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.72/1.95       ( ![D:$i]:
% 1.72/1.95         ( ( r2_hidden @ D @ C ) <=>
% 1.72/1.95           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.72/1.95  thf('26', plain,
% 1.72/1.95      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.72/1.95         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 1.72/1.95          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 1.72/1.95          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 1.72/1.95      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.72/1.95  thf('27', plain,
% 1.72/1.95      (![X0 : $i, X1 : $i]:
% 1.72/1.95         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.72/1.95          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.72/1.95      inference('eq_fact', [status(thm)], ['26'])).
% 1.72/1.95  thf('28', plain,
% 1.72/1.95      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.95  thf(t3_subset, axiom,
% 1.72/1.95    (![A:$i,B:$i]:
% 1.72/1.95     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.72/1.95  thf('29', plain,
% 1.72/1.95      (![X18 : $i, X19 : $i]:
% 1.72/1.95         ((r1_tarski @ X18 @ X19) | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 1.72/1.95      inference('cnf', [status(esa)], [t3_subset])).
% 1.72/1.95  thf('30', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.72/1.95      inference('sup-', [status(thm)], ['28', '29'])).
% 1.72/1.95  thf(d3_tarski, axiom,
% 1.72/1.95    (![A:$i,B:$i]:
% 1.72/1.95     ( ( r1_tarski @ A @ B ) <=>
% 1.72/1.95       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.72/1.95  thf('31', plain,
% 1.72/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.95         (~ (r2_hidden @ X0 @ X1)
% 1.72/1.95          | (r2_hidden @ X0 @ X2)
% 1.72/1.95          | ~ (r1_tarski @ X1 @ X2))),
% 1.72/1.95      inference('cnf', [status(esa)], [d3_tarski])).
% 1.72/1.95  thf('32', plain,
% 1.72/1.95      (![X0 : $i]:
% 1.72/1.95         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 1.72/1.95      inference('sup-', [status(thm)], ['30', '31'])).
% 1.72/1.95  thf('33', plain,
% 1.72/1.95      (![X0 : $i]:
% 1.72/1.95         (((sk_B) = (k3_xboole_0 @ sk_B @ X0))
% 1.72/1.95          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.72/1.95      inference('sup-', [status(thm)], ['27', '32'])).
% 1.72/1.95  thf('34', plain,
% 1.72/1.95      (![X5 : $i, X6 : $i, X9 : $i]:
% 1.72/1.95         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 1.72/1.95          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 1.72/1.95          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 1.72/1.95          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 1.72/1.95      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.72/1.95  thf('35', plain,
% 1.72/1.95      ((((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))
% 1.72/1.95        | ~ (r2_hidden @ (sk_D @ sk_B @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 1.72/1.95        | ~ (r2_hidden @ (sk_D @ sk_B @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 1.72/1.95        | ((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 1.72/1.95      inference('sup-', [status(thm)], ['33', '34'])).
% 1.72/1.95  thf('36', plain,
% 1.72/1.95      ((~ (r2_hidden @ (sk_D @ sk_B @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B)
% 1.72/1.95        | ((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 1.72/1.95      inference('simplify', [status(thm)], ['35'])).
% 1.72/1.95  thf('37', plain,
% 1.72/1.95      (![X0 : $i, X1 : $i]:
% 1.72/1.95         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.72/1.95          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.72/1.95      inference('eq_fact', [status(thm)], ['26'])).
% 1.72/1.95  thf('38', plain, (((sk_B) = (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.72/1.95      inference('clc', [status(thm)], ['36', '37'])).
% 1.72/1.95  thf('39', plain,
% 1.72/1.95      (![X1 : $i, X3 : $i]:
% 1.72/1.95         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.72/1.95      inference('cnf', [status(esa)], [d3_tarski])).
% 1.72/1.95  thf('40', plain,
% 1.72/1.95      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.72/1.95         (~ (r2_hidden @ X8 @ X7)
% 1.72/1.95          | (r2_hidden @ X8 @ X5)
% 1.72/1.95          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 1.72/1.95      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.72/1.95  thf('41', plain,
% 1.72/1.95      (![X5 : $i, X6 : $i, X8 : $i]:
% 1.72/1.95         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.72/1.95      inference('simplify', [status(thm)], ['40'])).
% 1.72/1.95  thf('42', plain,
% 1.72/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.95         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.72/1.95          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 1.72/1.95      inference('sup-', [status(thm)], ['39', '41'])).
% 1.72/1.95  thf('43', plain,
% 1.72/1.95      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 1.72/1.95         (~ (r2_hidden @ X8 @ X7)
% 1.72/1.95          | (r2_hidden @ X8 @ X6)
% 1.72/1.95          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 1.72/1.95      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.72/1.95  thf('44', plain,
% 1.72/1.95      (![X5 : $i, X6 : $i, X8 : $i]:
% 1.72/1.95         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.72/1.95      inference('simplify', [status(thm)], ['43'])).
% 1.72/1.95  thf('45', plain,
% 1.72/1.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.72/1.95         ((r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X3)
% 1.72/1.95          | (r2_hidden @ 
% 1.72/1.95             (sk_C @ X3 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)) @ X0))),
% 1.72/1.95      inference('sup-', [status(thm)], ['42', '44'])).
% 1.72/1.95  thf('46', plain,
% 1.72/1.95      (![X1 : $i, X3 : $i]:
% 1.72/1.95         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.72/1.95      inference('cnf', [status(esa)], [d3_tarski])).
% 1.72/1.95  thf('47', plain,
% 1.72/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.95         ((r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ X1) @ X0)
% 1.72/1.95          | (r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ X1) @ X0))),
% 1.72/1.95      inference('sup-', [status(thm)], ['45', '46'])).
% 1.72/1.95  thf('48', plain,
% 1.72/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.72/1.95         (r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X2 @ X0) @ X1) @ X0)),
% 1.72/1.95      inference('simplify', [status(thm)], ['47'])).
% 1.72/1.95  thf('49', plain,
% 1.72/1.95      (![X0 : $i]:
% 1.72/1.95         (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 1.72/1.95      inference('sup+', [status(thm)], ['38', '48'])).
% 1.72/1.95  thf('50', plain,
% 1.72/1.95      (![X18 : $i, X20 : $i]:
% 1.72/1.95         ((m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X18 @ X20))),
% 1.72/1.95      inference('cnf', [status(esa)], [t3_subset])).
% 1.72/1.95  thf('51', plain,
% 1.72/1.95      (![X0 : $i]:
% 1.72/1.95         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 1.72/1.95          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.72/1.95      inference('sup-', [status(thm)], ['49', '50'])).
% 1.72/1.95  thf(t48_pre_topc, axiom,
% 1.72/1.95    (![A:$i]:
% 1.72/1.95     ( ( l1_pre_topc @ A ) =>
% 1.72/1.95       ( ![B:$i]:
% 1.72/1.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.72/1.95           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 1.72/1.95  thf('52', plain,
% 1.72/1.95      (![X21 : $i, X22 : $i]:
% 1.72/1.95         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.72/1.95          | (r1_tarski @ X21 @ (k2_pre_topc @ X22 @ X21))
% 1.72/1.95          | ~ (l1_pre_topc @ X22))),
% 1.72/1.95      inference('cnf', [status(esa)], [t48_pre_topc])).
% 1.72/1.95  thf('53', plain,
% 1.72/1.95      (![X0 : $i]:
% 1.72/1.95         (~ (l1_pre_topc @ sk_A)
% 1.72/1.95          | (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ 
% 1.72/1.95             (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0))))),
% 1.72/1.95      inference('sup-', [status(thm)], ['51', '52'])).
% 1.72/1.95  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 1.72/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.95  thf('55', plain,
% 1.72/1.95      (![X0 : $i]:
% 1.72/1.95         (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ 
% 1.72/1.95          (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 1.72/1.95      inference('demod', [status(thm)], ['53', '54'])).
% 1.72/1.95  thf('56', plain,
% 1.72/1.95      (((k3_xboole_0 @ sk_B @ sk_C_1)
% 1.72/1.95         = (k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1)))),
% 1.72/1.95      inference('demod', [status(thm)], ['25', '55'])).
% 1.72/1.95  thf('57', plain,
% 1.72/1.95      (((k2_pre_topc @ sk_A @ 
% 1.72/1.95         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C_1))
% 1.72/1.95         != (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.72/1.95             (k2_pre_topc @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ sk_C_1)))),
% 1.72/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.72/1.95  thf('58', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 1.72/1.95      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.72/1.95  thf('59', plain,
% 1.72/1.95      (((k2_pre_topc @ sk_A @ 
% 1.72/1.95         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C_1))
% 1.72/1.95         != (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.72/1.95             (k2_pre_topc @ sk_A @ sk_C_1)))),
% 1.72/1.95      inference('demod', [status(thm)], ['57', '58'])).
% 1.72/1.95  thf('60', plain, (((k2_pre_topc @ sk_A @ sk_C_1) = (sk_C_1))),
% 1.72/1.95      inference('demod', [status(thm)], ['18', '19', '20'])).
% 1.72/1.95  thf('61', plain,
% 1.72/1.95      (((k2_pre_topc @ sk_A @ 
% 1.72/1.95         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C_1))
% 1.72/1.95         != (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C_1))),
% 1.72/1.95      inference('demod', [status(thm)], ['59', '60'])).
% 1.72/1.95  thf('62', plain,
% 1.72/1.95      (![X0 : $i]:
% 1.72/1.95         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1)
% 1.72/1.95           = (k3_xboole_0 @ X0 @ sk_C_1))),
% 1.72/1.95      inference('sup-', [status(thm)], ['13', '14'])).
% 1.72/1.95  thf('63', plain,
% 1.72/1.95      (![X0 : $i]:
% 1.72/1.95         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1)
% 1.72/1.95           = (k3_xboole_0 @ X0 @ sk_C_1))),
% 1.72/1.95      inference('sup-', [status(thm)], ['13', '14'])).
% 1.72/1.95  thf('64', plain,
% 1.72/1.95      (((k2_pre_topc @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C_1))
% 1.72/1.95         != (k3_xboole_0 @ sk_B @ sk_C_1))),
% 1.72/1.95      inference('demod', [status(thm)], ['61', '62', '63'])).
% 1.72/1.95  thf('65', plain, ($false),
% 1.72/1.95      inference('simplify_reflect-', [status(thm)], ['56', '64'])).
% 1.72/1.95  
% 1.72/1.95  % SZS output end Refutation
% 1.72/1.95  
% 1.72/1.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
