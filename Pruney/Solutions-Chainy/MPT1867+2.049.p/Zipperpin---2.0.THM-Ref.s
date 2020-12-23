%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JJiWjNSm3x

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:32 EST 2020

% Result     : Theorem 6.31s
% Output     : Refutation 6.31s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 120 expanded)
%              Number of leaves         :   29 (  48 expanded)
%              Depth                    :   16
%              Number of atoms          :  586 ( 895 expanded)
%              Number of equality atoms :   37 (  49 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t35_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_tex_2])).

thf('0',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(d6_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( r1_tarski @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( r1_tarski @ ( sk_C @ X19 @ X20 ) @ X19 )
      | ( v2_tex_2 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_C @ X0 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X0 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_tex_2 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('24',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_C @ X0 @ sk_A )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_C @ X0 @ sk_A )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ sk_A )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v4_pre_topc @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X17 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('36',plain,(
    ! [X19: $i,X20: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v4_pre_topc @ X22 @ X20 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 @ X22 )
       != ( sk_C @ X19 @ X20 ) )
      | ( v2_tex_2 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ X2 )
       != ( sk_C @ X1 @ X0 ) )
      | ~ ( v4_pre_topc @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ k1_xboole_0 )
       != ( sk_C @ X1 @ X0 ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('40',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ X1 @ X0 ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','44'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( sk_C @ X1 @ X0 ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_tex_2 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','48'])).

thf('50',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_tex_2 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('55',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference('simplify_reflect+',[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['4','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JJiWjNSm3x
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.31/6.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.31/6.54  % Solved by: fo/fo7.sh
% 6.31/6.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.31/6.54  % done 13281 iterations in 6.054s
% 6.31/6.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.31/6.54  % SZS output start Refutation
% 6.31/6.54  thf(sk_A_type, type, sk_A: $i).
% 6.31/6.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.31/6.54  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 6.31/6.54  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 6.31/6.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 6.31/6.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.31/6.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.31/6.54  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 6.31/6.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 6.31/6.54  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 6.31/6.54  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 6.31/6.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.31/6.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.31/6.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.31/6.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.31/6.54  thf(sk_B_type, type, sk_B: $i).
% 6.31/6.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.31/6.54  thf(t35_tex_2, conjecture,
% 6.31/6.54    (![A:$i]:
% 6.31/6.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.31/6.54       ( ![B:$i]:
% 6.31/6.54         ( ( ( v1_xboole_0 @ B ) & 
% 6.31/6.54             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.31/6.54           ( v2_tex_2 @ B @ A ) ) ) ))).
% 6.31/6.54  thf(zf_stmt_0, negated_conjecture,
% 6.31/6.54    (~( ![A:$i]:
% 6.31/6.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 6.31/6.54            ( l1_pre_topc @ A ) ) =>
% 6.31/6.54          ( ![B:$i]:
% 6.31/6.54            ( ( ( v1_xboole_0 @ B ) & 
% 6.31/6.54                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.31/6.54              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 6.31/6.54    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 6.31/6.54  thf('0', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 6.31/6.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.31/6.54  thf('1', plain, ((v1_xboole_0 @ sk_B)),
% 6.31/6.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.31/6.54  thf(l13_xboole_0, axiom,
% 6.31/6.54    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 6.31/6.54  thf('2', plain,
% 6.31/6.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.31/6.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.31/6.54  thf('3', plain, (((sk_B) = (k1_xboole_0))),
% 6.31/6.54      inference('sup-', [status(thm)], ['1', '2'])).
% 6.31/6.54  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 6.31/6.54      inference('demod', [status(thm)], ['0', '3'])).
% 6.31/6.54  thf('5', plain,
% 6.31/6.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.31/6.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.31/6.54  thf(t4_subset_1, axiom,
% 6.31/6.54    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 6.31/6.54  thf('6', plain,
% 6.31/6.54      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 6.31/6.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.31/6.54  thf('7', plain,
% 6.31/6.54      (![X0 : $i, X1 : $i]:
% 6.31/6.54         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 6.31/6.54      inference('sup+', [status(thm)], ['5', '6'])).
% 6.31/6.54  thf(d6_tex_2, axiom,
% 6.31/6.54    (![A:$i]:
% 6.31/6.54     ( ( l1_pre_topc @ A ) =>
% 6.31/6.54       ( ![B:$i]:
% 6.31/6.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.31/6.54           ( ( v2_tex_2 @ B @ A ) <=>
% 6.31/6.54             ( ![C:$i]:
% 6.31/6.54               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.31/6.54                 ( ~( ( r1_tarski @ C @ B ) & 
% 6.31/6.54                      ( ![D:$i]:
% 6.31/6.54                        ( ( m1_subset_1 @
% 6.31/6.54                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.31/6.54                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 6.31/6.54                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 6.31/6.54                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 6.31/6.54  thf('8', plain,
% 6.31/6.54      (![X19 : $i, X20 : $i]:
% 6.31/6.54         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 6.31/6.54          | (r1_tarski @ (sk_C @ X19 @ X20) @ X19)
% 6.31/6.54          | (v2_tex_2 @ X19 @ X20)
% 6.31/6.54          | ~ (l1_pre_topc @ X20))),
% 6.31/6.54      inference('cnf', [status(esa)], [d6_tex_2])).
% 6.31/6.54  thf('9', plain,
% 6.31/6.54      (![X0 : $i, X1 : $i]:
% 6.31/6.54         (~ (v1_xboole_0 @ X1)
% 6.31/6.54          | ~ (l1_pre_topc @ X0)
% 6.31/6.54          | (v2_tex_2 @ X1 @ X0)
% 6.31/6.54          | (r1_tarski @ (sk_C @ X1 @ X0) @ X1))),
% 6.31/6.54      inference('sup-', [status(thm)], ['7', '8'])).
% 6.31/6.54  thf('10', plain,
% 6.31/6.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.31/6.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.31/6.54  thf(t3_boole, axiom,
% 6.31/6.54    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 6.31/6.54  thf('11', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 6.31/6.54      inference('cnf', [status(esa)], [t3_boole])).
% 6.31/6.54  thf(t48_xboole_1, axiom,
% 6.31/6.54    (![A:$i,B:$i]:
% 6.31/6.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 6.31/6.54  thf('12', plain,
% 6.31/6.54      (![X8 : $i, X9 : $i]:
% 6.31/6.54         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 6.31/6.54           = (k3_xboole_0 @ X8 @ X9))),
% 6.31/6.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 6.31/6.54  thf('13', plain,
% 6.31/6.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 6.31/6.54      inference('sup+', [status(thm)], ['11', '12'])).
% 6.31/6.54  thf(t2_boole, axiom,
% 6.31/6.54    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 6.31/6.54  thf('14', plain,
% 6.31/6.54      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 6.31/6.54      inference('cnf', [status(esa)], [t2_boole])).
% 6.31/6.54  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 6.31/6.54      inference('demod', [status(thm)], ['13', '14'])).
% 6.31/6.54  thf(t36_xboole_1, axiom,
% 6.31/6.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 6.31/6.54  thf('16', plain,
% 6.31/6.54      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 6.31/6.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 6.31/6.54  thf('17', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 6.31/6.54      inference('sup+', [status(thm)], ['15', '16'])).
% 6.31/6.54  thf('18', plain,
% 6.31/6.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 6.31/6.54      inference('sup+', [status(thm)], ['10', '17'])).
% 6.31/6.54  thf(d10_xboole_0, axiom,
% 6.31/6.54    (![A:$i,B:$i]:
% 6.31/6.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.31/6.54  thf('19', plain,
% 6.31/6.54      (![X1 : $i, X3 : $i]:
% 6.31/6.54         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 6.31/6.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.31/6.54  thf('20', plain,
% 6.31/6.54      (![X0 : $i, X1 : $i]:
% 6.31/6.54         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 6.31/6.54      inference('sup-', [status(thm)], ['18', '19'])).
% 6.31/6.54  thf('21', plain,
% 6.31/6.54      (![X0 : $i, X1 : $i]:
% 6.31/6.54         ((v2_tex_2 @ X0 @ X1)
% 6.31/6.54          | ~ (l1_pre_topc @ X1)
% 6.31/6.54          | ~ (v1_xboole_0 @ X0)
% 6.31/6.54          | ((sk_C @ X0 @ X1) = (X0))
% 6.31/6.54          | ~ (v1_xboole_0 @ X0))),
% 6.31/6.54      inference('sup-', [status(thm)], ['9', '20'])).
% 6.31/6.54  thf('22', plain,
% 6.31/6.54      (![X0 : $i, X1 : $i]:
% 6.31/6.54         (((sk_C @ X0 @ X1) = (X0))
% 6.31/6.54          | ~ (v1_xboole_0 @ X0)
% 6.31/6.54          | ~ (l1_pre_topc @ X1)
% 6.31/6.54          | (v2_tex_2 @ X0 @ X1))),
% 6.31/6.54      inference('simplify', [status(thm)], ['21'])).
% 6.31/6.54  thf('23', plain,
% 6.31/6.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 6.31/6.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 6.31/6.54  thf('24', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 6.31/6.54      inference('demod', [status(thm)], ['0', '3'])).
% 6.31/6.54  thf('25', plain,
% 6.31/6.54      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 6.31/6.54      inference('sup-', [status(thm)], ['23', '24'])).
% 6.31/6.54  thf('26', plain,
% 6.31/6.54      (![X0 : $i]:
% 6.31/6.54         (~ (l1_pre_topc @ sk_A)
% 6.31/6.54          | ~ (v1_xboole_0 @ X0)
% 6.31/6.54          | ((sk_C @ X0 @ sk_A) = (X0))
% 6.31/6.54          | ~ (v1_xboole_0 @ X0))),
% 6.31/6.54      inference('sup-', [status(thm)], ['22', '25'])).
% 6.31/6.54  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 6.31/6.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.31/6.54  thf('28', plain,
% 6.31/6.54      (![X0 : $i]:
% 6.31/6.54         (~ (v1_xboole_0 @ X0)
% 6.31/6.54          | ((sk_C @ X0 @ sk_A) = (X0))
% 6.31/6.54          | ~ (v1_xboole_0 @ X0))),
% 6.31/6.54      inference('demod', [status(thm)], ['26', '27'])).
% 6.31/6.54  thf('29', plain,
% 6.31/6.54      (![X0 : $i]: (((sk_C @ X0 @ sk_A) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 6.31/6.54      inference('simplify', [status(thm)], ['28'])).
% 6.31/6.54  thf('30', plain,
% 6.31/6.54      (![X0 : $i, X1 : $i]:
% 6.31/6.54         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 6.31/6.54      inference('sup+', [status(thm)], ['5', '6'])).
% 6.31/6.54  thf(cc2_pre_topc, axiom,
% 6.31/6.54    (![A:$i]:
% 6.31/6.54     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.31/6.54       ( ![B:$i]:
% 6.31/6.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.31/6.54           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 6.31/6.55  thf('31', plain,
% 6.31/6.55      (![X17 : $i, X18 : $i]:
% 6.31/6.55         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 6.31/6.55          | (v4_pre_topc @ X17 @ X18)
% 6.31/6.55          | ~ (v1_xboole_0 @ X17)
% 6.31/6.55          | ~ (l1_pre_topc @ X18)
% 6.31/6.55          | ~ (v2_pre_topc @ X18))),
% 6.31/6.55      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 6.31/6.55  thf('32', plain,
% 6.31/6.55      (![X0 : $i, X1 : $i]:
% 6.31/6.55         (~ (v1_xboole_0 @ X1)
% 6.31/6.55          | ~ (v2_pre_topc @ X0)
% 6.31/6.55          | ~ (l1_pre_topc @ X0)
% 6.31/6.55          | ~ (v1_xboole_0 @ X1)
% 6.31/6.55          | (v4_pre_topc @ X1 @ X0))),
% 6.31/6.55      inference('sup-', [status(thm)], ['30', '31'])).
% 6.31/6.55  thf('33', plain,
% 6.31/6.55      (![X0 : $i, X1 : $i]:
% 6.31/6.55         ((v4_pre_topc @ X1 @ X0)
% 6.31/6.55          | ~ (l1_pre_topc @ X0)
% 6.31/6.55          | ~ (v2_pre_topc @ X0)
% 6.31/6.55          | ~ (v1_xboole_0 @ X1))),
% 6.31/6.55      inference('simplify', [status(thm)], ['32'])).
% 6.31/6.55  thf('34', plain,
% 6.31/6.55      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 6.31/6.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.31/6.55  thf('35', plain,
% 6.31/6.55      (![X0 : $i, X1 : $i]:
% 6.31/6.55         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 6.31/6.55      inference('sup+', [status(thm)], ['5', '6'])).
% 6.31/6.55  thf('36', plain,
% 6.31/6.55      (![X19 : $i, X20 : $i, X22 : $i]:
% 6.31/6.55         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 6.31/6.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 6.31/6.55          | ~ (v4_pre_topc @ X22 @ X20)
% 6.31/6.55          | ((k9_subset_1 @ (u1_struct_0 @ X20) @ X19 @ X22)
% 6.31/6.55              != (sk_C @ X19 @ X20))
% 6.31/6.55          | (v2_tex_2 @ X19 @ X20)
% 6.31/6.55          | ~ (l1_pre_topc @ X20))),
% 6.31/6.55      inference('cnf', [status(esa)], [d6_tex_2])).
% 6.31/6.55  thf('37', plain,
% 6.31/6.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.31/6.55         (~ (v1_xboole_0 @ X1)
% 6.31/6.55          | ~ (l1_pre_topc @ X0)
% 6.31/6.55          | (v2_tex_2 @ X1 @ X0)
% 6.31/6.55          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ X2) != (sk_C @ X1 @ X0))
% 6.31/6.55          | ~ (v4_pre_topc @ X2 @ X0)
% 6.31/6.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 6.31/6.55      inference('sup-', [status(thm)], ['35', '36'])).
% 6.31/6.55  thf('38', plain,
% 6.31/6.55      (![X0 : $i, X1 : $i]:
% 6.31/6.55         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 6.31/6.55          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ k1_xboole_0)
% 6.31/6.55              != (sk_C @ X1 @ X0))
% 6.31/6.55          | (v2_tex_2 @ X1 @ X0)
% 6.31/6.55          | ~ (l1_pre_topc @ X0)
% 6.31/6.55          | ~ (v1_xboole_0 @ X1))),
% 6.31/6.55      inference('sup-', [status(thm)], ['34', '37'])).
% 6.31/6.55  thf('39', plain,
% 6.31/6.55      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 6.31/6.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 6.31/6.55  thf(redefinition_k9_subset_1, axiom,
% 6.31/6.55    (![A:$i,B:$i,C:$i]:
% 6.31/6.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 6.31/6.55       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 6.31/6.55  thf('40', plain,
% 6.31/6.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 6.31/6.55         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 6.31/6.55          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 6.31/6.55      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 6.31/6.55  thf('41', plain,
% 6.31/6.55      (![X0 : $i, X1 : $i]:
% 6.31/6.55         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 6.31/6.55           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 6.31/6.55      inference('sup-', [status(thm)], ['39', '40'])).
% 6.31/6.55  thf('42', plain,
% 6.31/6.55      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 6.31/6.55      inference('cnf', [status(esa)], [t2_boole])).
% 6.31/6.55  thf('43', plain,
% 6.31/6.55      (![X0 : $i, X1 : $i]:
% 6.31/6.55         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 6.31/6.55      inference('demod', [status(thm)], ['41', '42'])).
% 6.31/6.55  thf('44', plain,
% 6.31/6.55      (![X0 : $i, X1 : $i]:
% 6.31/6.55         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 6.31/6.55          | ((k1_xboole_0) != (sk_C @ X1 @ X0))
% 6.31/6.55          | (v2_tex_2 @ X1 @ X0)
% 6.31/6.55          | ~ (l1_pre_topc @ X0)
% 6.31/6.55          | ~ (v1_xboole_0 @ X1))),
% 6.31/6.55      inference('demod', [status(thm)], ['38', '43'])).
% 6.31/6.55  thf('45', plain,
% 6.31/6.55      (![X0 : $i, X1 : $i]:
% 6.31/6.55         (~ (v1_xboole_0 @ k1_xboole_0)
% 6.31/6.55          | ~ (v2_pre_topc @ X0)
% 6.31/6.55          | ~ (l1_pre_topc @ X0)
% 6.31/6.55          | ~ (v1_xboole_0 @ X1)
% 6.31/6.55          | ~ (l1_pre_topc @ X0)
% 6.31/6.55          | (v2_tex_2 @ X1 @ X0)
% 6.31/6.55          | ((k1_xboole_0) != (sk_C @ X1 @ X0)))),
% 6.31/6.55      inference('sup-', [status(thm)], ['33', '44'])).
% 6.31/6.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 6.31/6.55  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.31/6.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.31/6.55  thf('47', plain,
% 6.31/6.55      (![X0 : $i, X1 : $i]:
% 6.31/6.55         (~ (v2_pre_topc @ X0)
% 6.31/6.55          | ~ (l1_pre_topc @ X0)
% 6.31/6.55          | ~ (v1_xboole_0 @ X1)
% 6.31/6.55          | ~ (l1_pre_topc @ X0)
% 6.31/6.55          | (v2_tex_2 @ X1 @ X0)
% 6.31/6.55          | ((k1_xboole_0) != (sk_C @ X1 @ X0)))),
% 6.31/6.55      inference('demod', [status(thm)], ['45', '46'])).
% 6.31/6.55  thf('48', plain,
% 6.31/6.55      (![X0 : $i, X1 : $i]:
% 6.31/6.55         (((k1_xboole_0) != (sk_C @ X1 @ X0))
% 6.31/6.55          | (v2_tex_2 @ X1 @ X0)
% 6.31/6.55          | ~ (v1_xboole_0 @ X1)
% 6.31/6.55          | ~ (l1_pre_topc @ X0)
% 6.31/6.55          | ~ (v2_pre_topc @ X0))),
% 6.31/6.55      inference('simplify', [status(thm)], ['47'])).
% 6.31/6.55  thf('49', plain,
% 6.31/6.55      (![X0 : $i]:
% 6.31/6.55         (((k1_xboole_0) != (X0))
% 6.31/6.55          | ~ (v1_xboole_0 @ X0)
% 6.31/6.55          | ~ (v2_pre_topc @ sk_A)
% 6.31/6.55          | ~ (l1_pre_topc @ sk_A)
% 6.31/6.55          | ~ (v1_xboole_0 @ X0)
% 6.31/6.55          | (v2_tex_2 @ X0 @ sk_A))),
% 6.31/6.55      inference('sup-', [status(thm)], ['29', '48'])).
% 6.31/6.55  thf('50', plain, ((v2_pre_topc @ sk_A)),
% 6.31/6.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.31/6.55  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 6.31/6.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.31/6.55  thf('52', plain,
% 6.31/6.55      (![X0 : $i]:
% 6.31/6.55         (((k1_xboole_0) != (X0))
% 6.31/6.55          | ~ (v1_xboole_0 @ X0)
% 6.31/6.55          | ~ (v1_xboole_0 @ X0)
% 6.31/6.55          | (v2_tex_2 @ X0 @ sk_A))),
% 6.31/6.55      inference('demod', [status(thm)], ['49', '50', '51'])).
% 6.31/6.55  thf('53', plain,
% 6.31/6.55      (((v2_tex_2 @ k1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 6.31/6.55      inference('simplify', [status(thm)], ['52'])).
% 6.31/6.55  thf('54', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.31/6.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.31/6.55  thf('55', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 6.31/6.55      inference('simplify_reflect+', [status(thm)], ['53', '54'])).
% 6.31/6.55  thf('56', plain, ($false), inference('demod', [status(thm)], ['4', '55'])).
% 6.31/6.55  
% 6.31/6.55  % SZS output end Refutation
% 6.31/6.55  
% 6.31/6.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
