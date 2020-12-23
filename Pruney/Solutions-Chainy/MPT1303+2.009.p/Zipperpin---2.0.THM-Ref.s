%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0vRWQ195ZO

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:19 EST 2020

% Result     : Theorem 7.42s
% Output     : Refutation 7.42s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 127 expanded)
%              Number of leaves         :   21 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :  761 (1430 expanded)
%              Number of equality atoms :   24 (  43 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_tops_2_type,type,(
    v1_tops_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t21_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( v1_tops_2 @ B @ A )
               => ( v1_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
               => ( ( v1_tops_2 @ B @ A )
                 => ( v1_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t21_tops_2])).

thf('0',plain,(
    ~ ( v1_tops_2 @ ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X14 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 @ sk_C_1 )
      = ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_tops_2 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['5'])).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('8',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['5'])).

thf('11',plain,(
    ! [X5: $i,X6: $i,X9: $i] :
      ( ( X9
        = ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X9 @ X6 @ X5 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['5'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X2 ) @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup+',[status(thm)],['17','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t18_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( ( r1_tarski @ B @ C )
                  & ( v1_tops_2 @ C @ A ) )
               => ( v1_tops_2 @ B @ A ) ) ) ) ) )).

thf('33',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) )
      | ( v1_tops_2 @ X18 @ X19 )
      | ~ ( r1_tarski @ X18 @ X20 )
      | ~ ( v1_tops_2 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t18_tops_2])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_tops_2 @ X2 @ X0 )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) @ X1 ) @ X2 )
      | ( v1_tops_2 @ ( k3_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( k3_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) @ sk_B )
      | ~ ( v1_tops_2 @ sk_B @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    v1_tops_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_tops_2 @ ( k3_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) @ sk_A )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( v1_tops_2 @ ( k3_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['5'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
        = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ sk_B @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k3_xboole_0 @ sk_B @ X0 ) @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['40','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
        = ( k3_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) )
      | ( ( k3_xboole_0 @ sk_B @ X0 )
        = ( k3_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ X0 )
      = ( k3_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( v1_tops_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['39','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['4','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0vRWQ195ZO
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:13:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 7.42/7.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.42/7.60  % Solved by: fo/fo7.sh
% 7.42/7.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.42/7.60  % done 3308 iterations in 7.144s
% 7.42/7.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.42/7.60  % SZS output start Refutation
% 7.42/7.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 7.42/7.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.42/7.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 7.42/7.60  thf(v1_tops_2_type, type, v1_tops_2: $i > $i > $o).
% 7.42/7.60  thf(sk_B_type, type, sk_B: $i).
% 7.42/7.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 7.42/7.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.42/7.60  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 7.42/7.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.42/7.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 7.42/7.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 7.42/7.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.42/7.60  thf(sk_A_type, type, sk_A: $i).
% 7.42/7.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 7.42/7.60  thf(t21_tops_2, conjecture,
% 7.42/7.60    (![A:$i]:
% 7.42/7.60     ( ( l1_pre_topc @ A ) =>
% 7.42/7.60       ( ![B:$i]:
% 7.42/7.60         ( ( m1_subset_1 @
% 7.42/7.60             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.42/7.60           ( ![C:$i]:
% 7.42/7.60             ( ( m1_subset_1 @
% 7.42/7.60                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.42/7.60               ( ( v1_tops_2 @ B @ A ) =>
% 7.42/7.60                 ( v1_tops_2 @
% 7.42/7.60                   ( k9_subset_1 @
% 7.42/7.60                     ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 7.42/7.60                   A ) ) ) ) ) ) ))).
% 7.42/7.60  thf(zf_stmt_0, negated_conjecture,
% 7.42/7.60    (~( ![A:$i]:
% 7.42/7.60        ( ( l1_pre_topc @ A ) =>
% 7.42/7.60          ( ![B:$i]:
% 7.42/7.60            ( ( m1_subset_1 @
% 7.42/7.60                B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.42/7.60              ( ![C:$i]:
% 7.42/7.60                ( ( m1_subset_1 @
% 7.42/7.60                    C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.42/7.60                  ( ( v1_tops_2 @ B @ A ) =>
% 7.42/7.60                    ( v1_tops_2 @
% 7.42/7.60                      ( k9_subset_1 @
% 7.42/7.60                        ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) @ B @ C ) @ 
% 7.42/7.60                      A ) ) ) ) ) ) ) )),
% 7.42/7.60    inference('cnf.neg', [status(esa)], [t21_tops_2])).
% 7.42/7.60  thf('0', plain,
% 7.42/7.60      (~ (v1_tops_2 @ 
% 7.42/7.60          (k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ sk_B @ sk_C_1) @ 
% 7.42/7.60          sk_A)),
% 7.42/7.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.60  thf('1', plain,
% 7.42/7.60      ((m1_subset_1 @ sk_C_1 @ 
% 7.42/7.60        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 7.42/7.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.60  thf(redefinition_k9_subset_1, axiom,
% 7.42/7.60    (![A:$i,B:$i,C:$i]:
% 7.42/7.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 7.42/7.60       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 7.42/7.60  thf('2', plain,
% 7.42/7.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 7.42/7.60         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 7.42/7.60          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 7.42/7.60      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 7.42/7.60  thf('3', plain,
% 7.42/7.60      (![X0 : $i]:
% 7.42/7.60         ((k9_subset_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0 @ sk_C_1)
% 7.42/7.60           = (k3_xboole_0 @ X0 @ sk_C_1))),
% 7.42/7.60      inference('sup-', [status(thm)], ['1', '2'])).
% 7.42/7.60  thf('4', plain, (~ (v1_tops_2 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 7.42/7.60      inference('demod', [status(thm)], ['0', '3'])).
% 7.42/7.60  thf(d4_xboole_0, axiom,
% 7.42/7.60    (![A:$i,B:$i,C:$i]:
% 7.42/7.60     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 7.42/7.60       ( ![D:$i]:
% 7.42/7.60         ( ( r2_hidden @ D @ C ) <=>
% 7.42/7.60           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 7.42/7.60  thf('5', plain,
% 7.42/7.60      (![X5 : $i, X6 : $i, X9 : $i]:
% 7.42/7.60         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 7.42/7.60          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 7.42/7.60          | (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 7.42/7.60      inference('cnf', [status(esa)], [d4_xboole_0])).
% 7.42/7.60  thf('6', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i]:
% 7.42/7.60         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 7.42/7.60          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 7.42/7.60      inference('eq_fact', [status(thm)], ['5'])).
% 7.42/7.60  thf('7', plain,
% 7.42/7.60      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 7.42/7.60         (~ (r2_hidden @ X8 @ X7)
% 7.42/7.60          | (r2_hidden @ X8 @ X6)
% 7.42/7.60          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 7.42/7.60      inference('cnf', [status(esa)], [d4_xboole_0])).
% 7.42/7.60  thf('8', plain,
% 7.42/7.60      (![X5 : $i, X6 : $i, X8 : $i]:
% 7.42/7.60         ((r2_hidden @ X8 @ X6) | ~ (r2_hidden @ X8 @ (k3_xboole_0 @ X5 @ X6)))),
% 7.42/7.60      inference('simplify', [status(thm)], ['7'])).
% 7.42/7.60  thf('9', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.60         (((k3_xboole_0 @ X1 @ X0)
% 7.42/7.60            = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 7.42/7.60          | (r2_hidden @ 
% 7.42/7.60             (sk_D @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0) @ X2) @ 
% 7.42/7.60             X0))),
% 7.42/7.60      inference('sup-', [status(thm)], ['6', '8'])).
% 7.42/7.60  thf('10', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i]:
% 7.42/7.60         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 7.42/7.60          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 7.42/7.60      inference('eq_fact', [status(thm)], ['5'])).
% 7.42/7.60  thf('11', plain,
% 7.42/7.60      (![X5 : $i, X6 : $i, X9 : $i]:
% 7.42/7.60         (((X9) = (k3_xboole_0 @ X5 @ X6))
% 7.42/7.60          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X6)
% 7.42/7.60          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X5)
% 7.42/7.60          | ~ (r2_hidden @ (sk_D @ X9 @ X6 @ X5) @ X9))),
% 7.42/7.60      inference('cnf', [status(esa)], [d4_xboole_0])).
% 7.42/7.60  thf('12', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i]:
% 7.42/7.60         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 7.42/7.60          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 7.42/7.60          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 7.42/7.60          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 7.42/7.60      inference('sup-', [status(thm)], ['10', '11'])).
% 7.42/7.60  thf('13', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i]:
% 7.42/7.60         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 7.42/7.60          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 7.42/7.60          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 7.42/7.60      inference('simplify', [status(thm)], ['12'])).
% 7.42/7.60  thf('14', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i]:
% 7.42/7.60         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 7.42/7.60          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 7.42/7.60      inference('eq_fact', [status(thm)], ['5'])).
% 7.42/7.60  thf('15', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i]:
% 7.42/7.60         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 7.42/7.60          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 7.42/7.60      inference('clc', [status(thm)], ['13', '14'])).
% 7.42/7.60  thf('16', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i]:
% 7.42/7.60         (((k3_xboole_0 @ X1 @ X0)
% 7.42/7.60            = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 7.42/7.60          | ((k3_xboole_0 @ X1 @ X0)
% 7.42/7.60              = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 7.42/7.60      inference('sup-', [status(thm)], ['9', '15'])).
% 7.42/7.60  thf('17', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i]:
% 7.42/7.60         ((k3_xboole_0 @ X1 @ X0)
% 7.42/7.60           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 7.42/7.60      inference('simplify', [status(thm)], ['16'])).
% 7.42/7.60  thf(d3_tarski, axiom,
% 7.42/7.60    (![A:$i,B:$i]:
% 7.42/7.60     ( ( r1_tarski @ A @ B ) <=>
% 7.42/7.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 7.42/7.60  thf('18', plain,
% 7.42/7.60      (![X1 : $i, X3 : $i]:
% 7.42/7.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 7.42/7.60      inference('cnf', [status(esa)], [d3_tarski])).
% 7.42/7.60  thf(t17_xboole_1, axiom,
% 7.42/7.60    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 7.42/7.60  thf('19', plain,
% 7.42/7.60      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 7.42/7.60      inference('cnf', [status(esa)], [t17_xboole_1])).
% 7.42/7.60  thf('20', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.60         (~ (r2_hidden @ X0 @ X1)
% 7.42/7.60          | (r2_hidden @ X0 @ X2)
% 7.42/7.60          | ~ (r1_tarski @ X1 @ X2))),
% 7.42/7.60      inference('cnf', [status(esa)], [d3_tarski])).
% 7.42/7.60  thf('21', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.60         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 7.42/7.60      inference('sup-', [status(thm)], ['19', '20'])).
% 7.42/7.60  thf('22', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.60         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 7.42/7.60          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 7.42/7.60      inference('sup-', [status(thm)], ['18', '21'])).
% 7.42/7.60  thf('23', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.60         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 7.42/7.60      inference('sup-', [status(thm)], ['19', '20'])).
% 7.42/7.60  thf('24', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.42/7.60         ((r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2) @ X3)
% 7.42/7.60          | (r2_hidden @ 
% 7.42/7.60             (sk_C @ X3 @ (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)) @ X1))),
% 7.42/7.60      inference('sup-', [status(thm)], ['22', '23'])).
% 7.42/7.60  thf('25', plain,
% 7.42/7.60      (![X1 : $i, X3 : $i]:
% 7.42/7.60         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 7.42/7.60      inference('cnf', [status(esa)], [d3_tarski])).
% 7.42/7.60  thf('26', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.60         ((r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ X1) @ X0)
% 7.42/7.60          | (r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ X1) @ X0))),
% 7.42/7.60      inference('sup-', [status(thm)], ['24', '25'])).
% 7.42/7.60  thf('27', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.60         (r1_tarski @ (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X2) @ X1) @ X0)),
% 7.42/7.60      inference('simplify', [status(thm)], ['26'])).
% 7.42/7.60  thf('28', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.60         (r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1)),
% 7.42/7.60      inference('sup+', [status(thm)], ['17', '27'])).
% 7.42/7.60  thf('29', plain,
% 7.42/7.60      ((m1_subset_1 @ sk_B @ 
% 7.42/7.60        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 7.42/7.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.60  thf('30', plain,
% 7.42/7.60      (![X10 : $i, X11 : $i]: (r1_tarski @ (k3_xboole_0 @ X10 @ X11) @ X10)),
% 7.42/7.60      inference('cnf', [status(esa)], [t17_xboole_1])).
% 7.42/7.60  thf(t3_subset, axiom,
% 7.42/7.60    (![A:$i,B:$i]:
% 7.42/7.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 7.42/7.60  thf('31', plain,
% 7.42/7.60      (![X15 : $i, X17 : $i]:
% 7.42/7.60         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 7.42/7.60      inference('cnf', [status(esa)], [t3_subset])).
% 7.42/7.60  thf('32', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i]:
% 7.42/7.60         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 7.42/7.60      inference('sup-', [status(thm)], ['30', '31'])).
% 7.42/7.60  thf(t18_tops_2, axiom,
% 7.42/7.60    (![A:$i]:
% 7.42/7.60     ( ( l1_pre_topc @ A ) =>
% 7.42/7.60       ( ![B:$i]:
% 7.42/7.60         ( ( m1_subset_1 @
% 7.42/7.60             B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.42/7.60           ( ![C:$i]:
% 7.42/7.60             ( ( m1_subset_1 @
% 7.42/7.60                 C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 7.42/7.60               ( ( ( r1_tarski @ B @ C ) & ( v1_tops_2 @ C @ A ) ) =>
% 7.42/7.60                 ( v1_tops_2 @ B @ A ) ) ) ) ) ) ))).
% 7.42/7.60  thf('33', plain,
% 7.42/7.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 7.42/7.60         (~ (m1_subset_1 @ X18 @ 
% 7.42/7.60             (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))
% 7.42/7.60          | (v1_tops_2 @ X18 @ X19)
% 7.42/7.60          | ~ (r1_tarski @ X18 @ X20)
% 7.42/7.60          | ~ (v1_tops_2 @ X20 @ X19)
% 7.42/7.60          | ~ (m1_subset_1 @ X20 @ 
% 7.42/7.60               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))
% 7.42/7.60          | ~ (l1_pre_topc @ X19))),
% 7.42/7.60      inference('cnf', [status(esa)], [t18_tops_2])).
% 7.42/7.60  thf('34', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.60         (~ (l1_pre_topc @ X0)
% 7.42/7.60          | ~ (m1_subset_1 @ X2 @ 
% 7.42/7.60               (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))
% 7.42/7.60          | ~ (v1_tops_2 @ X2 @ X0)
% 7.42/7.60          | ~ (r1_tarski @ 
% 7.42/7.60               (k3_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)) @ X1) @ X2)
% 7.42/7.60          | (v1_tops_2 @ 
% 7.42/7.60             (k3_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)) @ X1) @ X0))),
% 7.42/7.60      inference('sup-', [status(thm)], ['32', '33'])).
% 7.42/7.60  thf('35', plain,
% 7.42/7.60      (![X0 : $i]:
% 7.42/7.60         ((v1_tops_2 @ 
% 7.42/7.60           (k3_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0) @ sk_A)
% 7.42/7.60          | ~ (r1_tarski @ 
% 7.42/7.60               (k3_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0) @ sk_B)
% 7.42/7.60          | ~ (v1_tops_2 @ sk_B @ sk_A)
% 7.42/7.60          | ~ (l1_pre_topc @ sk_A))),
% 7.42/7.60      inference('sup-', [status(thm)], ['29', '34'])).
% 7.42/7.60  thf('36', plain, ((v1_tops_2 @ sk_B @ sk_A)),
% 7.42/7.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.60  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 7.42/7.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.60  thf('38', plain,
% 7.42/7.60      (![X0 : $i]:
% 7.42/7.60         ((v1_tops_2 @ 
% 7.42/7.60           (k3_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0) @ sk_A)
% 7.42/7.60          | ~ (r1_tarski @ 
% 7.42/7.60               (k3_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ X0) @ sk_B))),
% 7.42/7.60      inference('demod', [status(thm)], ['35', '36', '37'])).
% 7.42/7.60  thf('39', plain,
% 7.42/7.60      (![X0 : $i]:
% 7.42/7.60         (v1_tops_2 @ 
% 7.42/7.60          (k3_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 7.42/7.60           (k3_xboole_0 @ sk_B @ X0)) @ 
% 7.42/7.60          sk_A)),
% 7.42/7.60      inference('sup-', [status(thm)], ['28', '38'])).
% 7.42/7.60  thf('40', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i]:
% 7.42/7.60         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 7.42/7.60          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 7.42/7.60      inference('eq_fact', [status(thm)], ['5'])).
% 7.42/7.60  thf('41', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.60         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 7.42/7.60          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 7.42/7.60      inference('sup-', [status(thm)], ['18', '21'])).
% 7.42/7.60  thf('42', plain,
% 7.42/7.60      ((m1_subset_1 @ sk_B @ 
% 7.42/7.60        (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 7.42/7.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.42/7.60  thf('43', plain,
% 7.42/7.60      (![X15 : $i, X16 : $i]:
% 7.42/7.60         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 7.42/7.60      inference('cnf', [status(esa)], [t3_subset])).
% 7.42/7.60  thf('44', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.42/7.60      inference('sup-', [status(thm)], ['42', '43'])).
% 7.42/7.60  thf('45', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.60         (~ (r2_hidden @ X0 @ X1)
% 7.42/7.60          | (r2_hidden @ X0 @ X2)
% 7.42/7.60          | ~ (r1_tarski @ X1 @ X2))),
% 7.42/7.60      inference('cnf', [status(esa)], [d3_tarski])).
% 7.42/7.60  thf('46', plain,
% 7.42/7.60      (![X0 : $i]:
% 7.42/7.60         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.42/7.60          | ~ (r2_hidden @ X0 @ sk_B))),
% 7.42/7.60      inference('sup-', [status(thm)], ['44', '45'])).
% 7.42/7.60  thf('47', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i]:
% 7.42/7.60         ((r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ X1)
% 7.42/7.60          | (r2_hidden @ (sk_C @ X1 @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 7.42/7.60             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 7.42/7.60      inference('sup-', [status(thm)], ['41', '46'])).
% 7.42/7.60  thf('48', plain,
% 7.42/7.60      (![X1 : $i, X3 : $i]:
% 7.42/7.60         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 7.42/7.60      inference('cnf', [status(esa)], [d3_tarski])).
% 7.42/7.60  thf('49', plain,
% 7.42/7.60      (![X0 : $i]:
% 7.42/7.60         ((r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ 
% 7.42/7.60           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.42/7.60          | (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ 
% 7.42/7.60             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 7.42/7.60      inference('sup-', [status(thm)], ['47', '48'])).
% 7.42/7.60  thf('50', plain,
% 7.42/7.60      (![X0 : $i]:
% 7.42/7.60         (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ 
% 7.42/7.60          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 7.42/7.60      inference('simplify', [status(thm)], ['49'])).
% 7.42/7.60  thf('51', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.42/7.60         (~ (r2_hidden @ X0 @ X1)
% 7.42/7.60          | (r2_hidden @ X0 @ X2)
% 7.42/7.60          | ~ (r1_tarski @ X1 @ X2))),
% 7.42/7.60      inference('cnf', [status(esa)], [d3_tarski])).
% 7.42/7.60  thf('52', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i]:
% 7.42/7.60         ((r2_hidden @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 7.42/7.60          | ~ (r2_hidden @ X1 @ (k3_xboole_0 @ sk_B @ X0)))),
% 7.42/7.60      inference('sup-', [status(thm)], ['50', '51'])).
% 7.42/7.60  thf('53', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i]:
% 7.42/7.60         (((k3_xboole_0 @ sk_B @ X0)
% 7.42/7.60            = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ sk_B @ X0)))
% 7.42/7.60          | (r2_hidden @ 
% 7.42/7.60             (sk_D @ (k3_xboole_0 @ sk_B @ X0) @ (k3_xboole_0 @ sk_B @ X0) @ X1) @ 
% 7.42/7.60             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 7.42/7.60      inference('sup-', [status(thm)], ['40', '52'])).
% 7.42/7.60  thf('54', plain,
% 7.42/7.60      (![X0 : $i, X1 : $i]:
% 7.42/7.60         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 7.42/7.60          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 7.42/7.60      inference('clc', [status(thm)], ['13', '14'])).
% 7.42/7.60  thf('55', plain,
% 7.42/7.60      (![X0 : $i]:
% 7.42/7.60         (((k3_xboole_0 @ sk_B @ X0)
% 7.42/7.60            = (k3_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 7.42/7.60               (k3_xboole_0 @ sk_B @ X0)))
% 7.42/7.60          | ((k3_xboole_0 @ sk_B @ X0)
% 7.42/7.60              = (k3_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 7.42/7.60                 (k3_xboole_0 @ sk_B @ X0))))),
% 7.42/7.60      inference('sup-', [status(thm)], ['53', '54'])).
% 7.42/7.60  thf('56', plain,
% 7.42/7.60      (![X0 : $i]:
% 7.42/7.60         ((k3_xboole_0 @ sk_B @ X0)
% 7.42/7.60           = (k3_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)) @ 
% 7.42/7.60              (k3_xboole_0 @ sk_B @ X0)))),
% 7.42/7.60      inference('simplify', [status(thm)], ['55'])).
% 7.42/7.60  thf('57', plain,
% 7.42/7.60      (![X0 : $i]: (v1_tops_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)),
% 7.42/7.60      inference('demod', [status(thm)], ['39', '56'])).
% 7.42/7.60  thf('58', plain, ($false), inference('demod', [status(thm)], ['4', '57'])).
% 7.42/7.60  
% 7.42/7.60  % SZS output end Refutation
% 7.42/7.60  
% 7.42/7.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
