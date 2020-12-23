%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VBpcaW1Sak

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:12 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 147 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :   19
%              Number of atoms          :  701 (1525 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t29_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v2_tex_2 @ B @ A )
                  | ( v2_tex_2 @ C @ A ) )
               => ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v2_tex_2 @ B @ A )
                    | ( v2_tex_2 @ C @ A ) )
                 => ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_tex_2])).

thf('0',plain,(
    ~ ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X14 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 )
      = ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X15 @ X16 ) )
      = ( k3_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ sk_C_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k4_xboole_0 @ sk_C_1 @ X0 ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ sk_C_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k4_xboole_0 @ sk_C_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_C_1 @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v2_tex_2 @ sk_C_1 @ sk_A )
   <= ( v2_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( r1_tarski @ C @ B )
                  & ( v2_tex_2 @ B @ A ) )
               => ( v2_tex_2 @ C @ A ) ) ) ) ) )).

thf('30',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_tex_2 @ X20 @ X21 )
      | ~ ( r1_tarski @ X22 @ X20 )
      | ( v2_tex_2 @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ~ ( v2_tex_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ~ ( v2_tex_2 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_C_1 )
        | ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k4_xboole_0 @ X6 @ X7 ) )
      = ( k3_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['27'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_tex_2 @ X20 @ X21 )
      | ~ ( r1_tarski @ X22 @ X20 )
      | ( v2_tex_2 @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( v2_tex_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A )
        | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('57',plain,
    ( ! [X0: $i] :
        ( v2_tex_2 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['35','57'])).

thf('59',plain,(
    ~ ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('60',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v2_tex_2 @ sk_C_1 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['27'])).

thf('62',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(simpl_trail,[status(thm)],['34','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k4_xboole_0 @ sk_C_1 @ X0 ) @ sk_A )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_C_1 @ X0 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['26','63'])).

thf('65',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( v2_tex_2 @ ( k4_xboole_0 @ sk_C_1 @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( v2_tex_2 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['10','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ sk_C_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['9','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['4','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VBpcaW1Sak
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:51:23 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.70/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.70/0.88  % Solved by: fo/fo7.sh
% 0.70/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.88  % done 653 iterations in 0.429s
% 0.70/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.70/0.88  % SZS output start Refutation
% 0.70/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.70/0.88  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.70/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.88  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.70/0.88  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.70/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.70/0.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.70/0.88  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.70/0.88  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.70/0.88  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.70/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.88  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.70/0.88  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.70/0.88  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.70/0.88  thf(t29_tex_2, conjecture,
% 0.70/0.88    (![A:$i]:
% 0.70/0.88     ( ( l1_pre_topc @ A ) =>
% 0.70/0.88       ( ![B:$i]:
% 0.70/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.88           ( ![C:$i]:
% 0.70/0.88             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.88               ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 0.70/0.88                 ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.70/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.88    (~( ![A:$i]:
% 0.70/0.88        ( ( l1_pre_topc @ A ) =>
% 0.70/0.88          ( ![B:$i]:
% 0.70/0.88            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.88              ( ![C:$i]:
% 0.70/0.88                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.88                  ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 0.70/0.88                    ( v2_tex_2 @
% 0.70/0.88                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.70/0.88    inference('cnf.neg', [status(esa)], [t29_tex_2])).
% 0.70/0.88  thf('0', plain,
% 0.70/0.88      (~ (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C_1) @ 
% 0.70/0.88          sk_A)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('1', plain,
% 0.70/0.88      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf(redefinition_k9_subset_1, axiom,
% 0.70/0.88    (![A:$i,B:$i,C:$i]:
% 0.70/0.88     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.70/0.88       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.70/0.88  thf('2', plain,
% 0.70/0.88      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.70/0.88         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 0.70/0.88          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.70/0.88      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.70/0.88  thf('3', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1)
% 0.70/0.88           = (k3_xboole_0 @ X0 @ sk_C_1))),
% 0.70/0.88      inference('sup-', [status(thm)], ['1', '2'])).
% 0.70/0.88  thf('4', plain, (~ (v2_tex_2 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 0.70/0.88      inference('demod', [status(thm)], ['0', '3'])).
% 0.70/0.88  thf(commutativity_k2_tarski, axiom,
% 0.70/0.88    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.70/0.88  thf('5', plain,
% 0.70/0.88      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 0.70/0.88      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.70/0.88  thf(t12_setfam_1, axiom,
% 0.70/0.88    (![A:$i,B:$i]:
% 0.70/0.88     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.70/0.88  thf('6', plain,
% 0.70/0.88      (![X15 : $i, X16 : $i]:
% 0.70/0.88         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.70/0.88      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.70/0.88  thf('7', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.88      inference('sup+', [status(thm)], ['5', '6'])).
% 0.70/0.88  thf('8', plain,
% 0.70/0.88      (![X15 : $i, X16 : $i]:
% 0.70/0.88         ((k1_setfam_1 @ (k2_tarski @ X15 @ X16)) = (k3_xboole_0 @ X15 @ X16))),
% 0.70/0.88      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.70/0.88  thf('9', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.70/0.88      inference('sup+', [status(thm)], ['7', '8'])).
% 0.70/0.88  thf(t48_xboole_1, axiom,
% 0.70/0.88    (![A:$i,B:$i]:
% 0.70/0.88     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.70/0.88  thf('10', plain,
% 0.70/0.88      (![X6 : $i, X7 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.70/0.88           = (k3_xboole_0 @ X6 @ X7))),
% 0.70/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.70/0.88  thf(d3_tarski, axiom,
% 0.70/0.88    (![A:$i,B:$i]:
% 0.70/0.88     ( ( r1_tarski @ A @ B ) <=>
% 0.70/0.88       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.70/0.88  thf('11', plain,
% 0.70/0.88      (![X1 : $i, X3 : $i]:
% 0.70/0.88         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.70/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.88  thf(t36_xboole_1, axiom,
% 0.70/0.88    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.70/0.88  thf('12', plain,
% 0.70/0.88      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.70/0.88      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.70/0.88  thf('13', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.88         (~ (r2_hidden @ X0 @ X1)
% 0.70/0.88          | (r2_hidden @ X0 @ X2)
% 0.70/0.88          | ~ (r1_tarski @ X1 @ X2))),
% 0.70/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.88  thf('14', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.88         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['12', '13'])).
% 0.70/0.88  thf('15', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.88         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.70/0.88          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.70/0.88      inference('sup-', [status(thm)], ['11', '14'])).
% 0.70/0.88  thf('16', plain,
% 0.70/0.88      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf(t3_subset, axiom,
% 0.70/0.88    (![A:$i,B:$i]:
% 0.70/0.88     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.70/0.88  thf('17', plain,
% 0.70/0.88      (![X17 : $i, X18 : $i]:
% 0.70/0.88         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.70/0.88      inference('cnf', [status(esa)], [t3_subset])).
% 0.70/0.88  thf('18', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.70/0.88      inference('sup-', [status(thm)], ['16', '17'])).
% 0.70/0.88  thf('19', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.88         (~ (r2_hidden @ X0 @ X1)
% 0.70/0.88          | (r2_hidden @ X0 @ X2)
% 0.70/0.88          | ~ (r1_tarski @ X1 @ X2))),
% 0.70/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.88  thf('20', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.70/0.88      inference('sup-', [status(thm)], ['18', '19'])).
% 0.70/0.88  thf('21', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((r1_tarski @ (k4_xboole_0 @ sk_C_1 @ X0) @ X1)
% 0.70/0.88          | (r2_hidden @ (sk_C @ X1 @ (k4_xboole_0 @ sk_C_1 @ X0)) @ 
% 0.70/0.88             (u1_struct_0 @ sk_A)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['15', '20'])).
% 0.70/0.88  thf('22', plain,
% 0.70/0.88      (![X1 : $i, X3 : $i]:
% 0.70/0.88         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.70/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.88  thf('23', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         ((r1_tarski @ (k4_xboole_0 @ sk_C_1 @ X0) @ (u1_struct_0 @ sk_A))
% 0.70/0.88          | (r1_tarski @ (k4_xboole_0 @ sk_C_1 @ X0) @ (u1_struct_0 @ sk_A)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['21', '22'])).
% 0.70/0.88  thf('24', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (r1_tarski @ (k4_xboole_0 @ sk_C_1 @ X0) @ (u1_struct_0 @ sk_A))),
% 0.70/0.88      inference('simplify', [status(thm)], ['23'])).
% 0.70/0.88  thf('25', plain,
% 0.70/0.88      (![X17 : $i, X19 : $i]:
% 0.70/0.88         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 0.70/0.88      inference('cnf', [status(esa)], [t3_subset])).
% 0.70/0.88  thf('26', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (m1_subset_1 @ (k4_xboole_0 @ sk_C_1 @ X0) @ 
% 0.70/0.88          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['24', '25'])).
% 0.70/0.88  thf('27', plain, (((v2_tex_2 @ sk_B @ sk_A) | (v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('28', plain,
% 0.70/0.88      (((v2_tex_2 @ sk_C_1 @ sk_A)) <= (((v2_tex_2 @ sk_C_1 @ sk_A)))),
% 0.70/0.88      inference('split', [status(esa)], ['27'])).
% 0.70/0.88  thf('29', plain,
% 0.70/0.88      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf(t28_tex_2, axiom,
% 0.70/0.88    (![A:$i]:
% 0.70/0.88     ( ( l1_pre_topc @ A ) =>
% 0.70/0.88       ( ![B:$i]:
% 0.70/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.88           ( ![C:$i]:
% 0.70/0.88             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.88               ( ( ( r1_tarski @ C @ B ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.70/0.88                 ( v2_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.70/0.88  thf('30', plain,
% 0.70/0.88      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.70/0.88         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.70/0.88          | ~ (v2_tex_2 @ X20 @ X21)
% 0.70/0.88          | ~ (r1_tarski @ X22 @ X20)
% 0.70/0.88          | (v2_tex_2 @ X22 @ X21)
% 0.70/0.88          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.70/0.88          | ~ (l1_pre_topc @ X21))),
% 0.70/0.88      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.70/0.88  thf('31', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (~ (l1_pre_topc @ sk_A)
% 0.70/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.88          | (v2_tex_2 @ X0 @ sk_A)
% 0.70/0.88          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.70/0.88          | ~ (v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.70/0.88      inference('sup-', [status(thm)], ['29', '30'])).
% 0.70/0.88  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('33', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.88          | (v2_tex_2 @ X0 @ sk_A)
% 0.70/0.88          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.70/0.88          | ~ (v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.70/0.88      inference('demod', [status(thm)], ['31', '32'])).
% 0.70/0.88  thf('34', plain,
% 0.70/0.88      ((![X0 : $i]:
% 0.70/0.88          (~ (r1_tarski @ X0 @ sk_C_1)
% 0.70/0.88           | (v2_tex_2 @ X0 @ sk_A)
% 0.70/0.88           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.70/0.88         <= (((v2_tex_2 @ sk_C_1 @ sk_A)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['28', '33'])).
% 0.70/0.88  thf('35', plain,
% 0.70/0.88      (![X6 : $i, X7 : $i]:
% 0.70/0.88         ((k4_xboole_0 @ X6 @ (k4_xboole_0 @ X6 @ X7))
% 0.70/0.88           = (k3_xboole_0 @ X6 @ X7))),
% 0.70/0.88      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.70/0.88  thf('36', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.88         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.70/0.88          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.70/0.88      inference('sup-', [status(thm)], ['11', '14'])).
% 0.70/0.88  thf('37', plain,
% 0.70/0.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('38', plain,
% 0.70/0.88      (![X17 : $i, X18 : $i]:
% 0.70/0.88         ((r1_tarski @ X17 @ X18) | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18)))),
% 0.70/0.88      inference('cnf', [status(esa)], [t3_subset])).
% 0.70/0.88  thf('39', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.70/0.88      inference('sup-', [status(thm)], ['37', '38'])).
% 0.70/0.88  thf('40', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.88         (~ (r2_hidden @ X0 @ X1)
% 0.70/0.88          | (r2_hidden @ X0 @ X2)
% 0.70/0.88          | ~ (r1_tarski @ X1 @ X2))),
% 0.70/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.88  thf('41', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.70/0.88      inference('sup-', [status(thm)], ['39', '40'])).
% 0.70/0.88  thf('42', plain,
% 0.70/0.88      (![X0 : $i, X1 : $i]:
% 0.70/0.88         ((r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1)
% 0.70/0.88          | (r2_hidden @ (sk_C @ X1 @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 0.70/0.88             (u1_struct_0 @ sk_A)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['36', '41'])).
% 0.70/0.88  thf('43', plain,
% 0.70/0.88      (![X1 : $i, X3 : $i]:
% 0.70/0.88         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.70/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.70/0.88  thf('44', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         ((r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))
% 0.70/0.88          | (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['42', '43'])).
% 0.70/0.88  thf('45', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 0.70/0.88      inference('simplify', [status(thm)], ['44'])).
% 0.70/0.88  thf('46', plain,
% 0.70/0.88      (![X17 : $i, X19 : $i]:
% 0.70/0.88         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 0.70/0.88      inference('cnf', [status(esa)], [t3_subset])).
% 0.70/0.88  thf('47', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 0.70/0.88          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['45', '46'])).
% 0.70/0.88  thf('48', plain,
% 0.70/0.88      (((v2_tex_2 @ sk_B @ sk_A)) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.70/0.88      inference('split', [status(esa)], ['27'])).
% 0.70/0.88  thf('49', plain,
% 0.70/0.88      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('50', plain,
% 0.70/0.88      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.70/0.88         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.70/0.88          | ~ (v2_tex_2 @ X20 @ X21)
% 0.70/0.88          | ~ (r1_tarski @ X22 @ X20)
% 0.70/0.88          | (v2_tex_2 @ X22 @ X21)
% 0.70/0.88          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.70/0.88          | ~ (l1_pre_topc @ X21))),
% 0.70/0.88      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.70/0.88  thf('51', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (~ (l1_pre_topc @ sk_A)
% 0.70/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.88          | (v2_tex_2 @ X0 @ sk_A)
% 0.70/0.88          | ~ (r1_tarski @ X0 @ sk_B)
% 0.70/0.88          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.70/0.88      inference('sup-', [status(thm)], ['49', '50'])).
% 0.70/0.88  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.88  thf('53', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.70/0.88          | (v2_tex_2 @ X0 @ sk_A)
% 0.70/0.88          | ~ (r1_tarski @ X0 @ sk_B)
% 0.70/0.88          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.70/0.88      inference('demod', [status(thm)], ['51', '52'])).
% 0.70/0.88  thf('54', plain,
% 0.70/0.88      ((![X0 : $i]:
% 0.70/0.88          (~ (r1_tarski @ X0 @ sk_B)
% 0.70/0.88           | (v2_tex_2 @ X0 @ sk_A)
% 0.70/0.88           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.70/0.88         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['48', '53'])).
% 0.70/0.88  thf('55', plain,
% 0.70/0.88      ((![X0 : $i]:
% 0.70/0.88          ((v2_tex_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.70/0.88           | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)))
% 0.70/0.88         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.70/0.88      inference('sup-', [status(thm)], ['47', '54'])).
% 0.70/0.88  thf('56', plain,
% 0.70/0.88      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.70/0.88      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.70/0.88  thf('57', plain,
% 0.70/0.88      ((![X0 : $i]: (v2_tex_2 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A))
% 0.70/0.88         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.70/0.88      inference('demod', [status(thm)], ['55', '56'])).
% 0.70/0.88  thf('58', plain,
% 0.70/0.88      ((![X0 : $i]: (v2_tex_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))
% 0.70/0.88         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.70/0.88      inference('sup+', [status(thm)], ['35', '57'])).
% 0.70/0.88  thf('59', plain, (~ (v2_tex_2 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 0.70/0.88      inference('demod', [status(thm)], ['0', '3'])).
% 0.70/0.88  thf('60', plain, (~ ((v2_tex_2 @ sk_B @ sk_A))),
% 0.70/0.88      inference('sup-', [status(thm)], ['58', '59'])).
% 0.70/0.88  thf('61', plain, (((v2_tex_2 @ sk_C_1 @ sk_A)) | ((v2_tex_2 @ sk_B @ sk_A))),
% 0.70/0.88      inference('split', [status(esa)], ['27'])).
% 0.70/0.88  thf('62', plain, (((v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.70/0.88      inference('sat_resolution*', [status(thm)], ['60', '61'])).
% 0.70/0.88  thf('63', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         (~ (r1_tarski @ X0 @ sk_C_1)
% 0.70/0.88          | (v2_tex_2 @ X0 @ sk_A)
% 0.70/0.88          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.70/0.88      inference('simpl_trail', [status(thm)], ['34', '62'])).
% 0.70/0.88  thf('64', plain,
% 0.70/0.88      (![X0 : $i]:
% 0.70/0.88         ((v2_tex_2 @ (k4_xboole_0 @ sk_C_1 @ X0) @ sk_A)
% 0.70/0.88          | ~ (r1_tarski @ (k4_xboole_0 @ sk_C_1 @ X0) @ sk_C_1))),
% 0.70/0.88      inference('sup-', [status(thm)], ['26', '63'])).
% 0.70/0.88  thf('65', plain,
% 0.70/0.88      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 0.70/0.88      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.70/0.88  thf('66', plain,
% 0.70/0.88      (![X0 : $i]: (v2_tex_2 @ (k4_xboole_0 @ sk_C_1 @ X0) @ sk_A)),
% 0.70/0.88      inference('demod', [status(thm)], ['64', '65'])).
% 0.70/0.88  thf('67', plain,
% 0.70/0.88      (![X0 : $i]: (v2_tex_2 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_A)),
% 0.70/0.88      inference('sup+', [status(thm)], ['10', '66'])).
% 0.70/0.88  thf('68', plain,
% 0.70/0.88      (![X0 : $i]: (v2_tex_2 @ (k3_xboole_0 @ X0 @ sk_C_1) @ sk_A)),
% 0.70/0.88      inference('sup+', [status(thm)], ['9', '67'])).
% 0.70/0.88  thf('69', plain, ($false), inference('demod', [status(thm)], ['4', '68'])).
% 0.70/0.88  
% 0.70/0.88  % SZS output end Refutation
% 0.70/0.88  
% 0.70/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
