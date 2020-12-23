%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QSOMuqptA6

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:30 EST 2020

% Result     : Theorem 13.03s
% Output     : Refutation 13.03s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 119 expanded)
%              Number of leaves         :   32 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  592 ( 891 expanded)
%              Number of equality atoms :   35 (  45 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( sk_C_1 @ X26 @ X27 ) @ X26 )
      | ( v2_tex_2 @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_C_1 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_1 @ X0 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_tex_2 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('18',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_C_1 @ X0 @ sk_A )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( sk_C_1 @ X0 @ sk_A )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ X0 @ sk_A )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v4_pre_topc @ X24 @ X25 )
      | ~ ( v1_xboole_0 @ X24 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('30',plain,(
    ! [X26: $i,X27: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v4_pre_topc @ X29 @ X27 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 @ X29 )
       != ( sk_C_1 @ X26 @ X27 ) )
      | ( v2_tex_2 @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ X2 )
       != ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v4_pre_topc @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ k1_xboole_0 )
       != ( sk_C_1 @ X1 @ X0 ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k9_subset_1 @ X19 @ X17 @ X18 )
        = ( k3_xboole_0 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('37',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C_1 @ X1 @ X0 ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['32','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( k1_xboole_0
       != ( sk_C_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','42'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('44',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( k1_xboole_0
       != ( sk_C_1 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( sk_C_1 @ X1 @ X0 ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_tex_2 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v2_tex_2 @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( v2_tex_2 @ k1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('53',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference('simplify_reflect+',[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['4','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QSOMuqptA6
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 13.03/13.22  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 13.03/13.22  % Solved by: fo/fo7.sh
% 13.03/13.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.03/13.22  % done 16150 iterations in 12.760s
% 13.03/13.22  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 13.03/13.22  % SZS output start Refutation
% 13.03/13.22  thf(sk_A_type, type, sk_A: $i).
% 13.03/13.22  thf(sk_B_1_type, type, sk_B_1: $i).
% 13.03/13.22  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 13.03/13.22  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 13.03/13.22  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 13.03/13.22  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 13.03/13.22  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 13.03/13.22  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 13.03/13.22  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 13.03/13.22  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 13.03/13.22  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 13.03/13.22  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 13.03/13.22  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 13.03/13.22  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 13.03/13.22  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 13.03/13.22  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 13.03/13.22  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 13.03/13.22  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 13.03/13.22  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 13.03/13.22  thf(t35_tex_2, conjecture,
% 13.03/13.22    (![A:$i]:
% 13.03/13.22     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 13.03/13.22       ( ![B:$i]:
% 13.03/13.22         ( ( ( v1_xboole_0 @ B ) & 
% 13.03/13.22             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 13.03/13.22           ( v2_tex_2 @ B @ A ) ) ) ))).
% 13.03/13.22  thf(zf_stmt_0, negated_conjecture,
% 13.03/13.22    (~( ![A:$i]:
% 13.03/13.22        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 13.03/13.22            ( l1_pre_topc @ A ) ) =>
% 13.03/13.22          ( ![B:$i]:
% 13.03/13.22            ( ( ( v1_xboole_0 @ B ) & 
% 13.03/13.22                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 13.03/13.22              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 13.03/13.22    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 13.03/13.22  thf('0', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 13.03/13.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.03/13.22  thf('1', plain, ((v1_xboole_0 @ sk_B_1)),
% 13.03/13.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.03/13.22  thf(l13_xboole_0, axiom,
% 13.03/13.22    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 13.03/13.22  thf('2', plain,
% 13.03/13.22      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X9))),
% 13.03/13.22      inference('cnf', [status(esa)], [l13_xboole_0])).
% 13.03/13.22  thf('3', plain, (((sk_B_1) = (k1_xboole_0))),
% 13.03/13.22      inference('sup-', [status(thm)], ['1', '2'])).
% 13.03/13.22  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 13.03/13.22      inference('demod', [status(thm)], ['0', '3'])).
% 13.03/13.22  thf('5', plain,
% 13.03/13.22      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X9))),
% 13.03/13.22      inference('cnf', [status(esa)], [l13_xboole_0])).
% 13.03/13.22  thf(t4_subset_1, axiom,
% 13.03/13.22    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 13.03/13.22  thf('6', plain,
% 13.03/13.22      (![X20 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 13.03/13.22      inference('cnf', [status(esa)], [t4_subset_1])).
% 13.03/13.22  thf('7', plain,
% 13.03/13.22      (![X0 : $i, X1 : $i]:
% 13.03/13.22         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 13.03/13.22      inference('sup+', [status(thm)], ['5', '6'])).
% 13.03/13.22  thf(d6_tex_2, axiom,
% 13.03/13.22    (![A:$i]:
% 13.03/13.22     ( ( l1_pre_topc @ A ) =>
% 13.03/13.22       ( ![B:$i]:
% 13.03/13.22         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 13.03/13.22           ( ( v2_tex_2 @ B @ A ) <=>
% 13.03/13.22             ( ![C:$i]:
% 13.03/13.22               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 13.03/13.22                 ( ~( ( r1_tarski @ C @ B ) & 
% 13.03/13.22                      ( ![D:$i]:
% 13.03/13.22                        ( ( m1_subset_1 @
% 13.03/13.22                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 13.03/13.22                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 13.03/13.22                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 13.03/13.22                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 13.03/13.22  thf('8', plain,
% 13.03/13.22      (![X26 : $i, X27 : $i]:
% 13.03/13.22         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 13.03/13.22          | (r1_tarski @ (sk_C_1 @ X26 @ X27) @ X26)
% 13.03/13.22          | (v2_tex_2 @ X26 @ X27)
% 13.03/13.22          | ~ (l1_pre_topc @ X27))),
% 13.03/13.22      inference('cnf', [status(esa)], [d6_tex_2])).
% 13.03/13.22  thf('9', plain,
% 13.03/13.22      (![X0 : $i, X1 : $i]:
% 13.03/13.22         (~ (v1_xboole_0 @ X1)
% 13.03/13.22          | ~ (l1_pre_topc @ X0)
% 13.03/13.22          | (v2_tex_2 @ X1 @ X0)
% 13.03/13.22          | (r1_tarski @ (sk_C_1 @ X1 @ X0) @ X1))),
% 13.03/13.22      inference('sup-', [status(thm)], ['7', '8'])).
% 13.03/13.22  thf(d3_tarski, axiom,
% 13.03/13.22    (![A:$i,B:$i]:
% 13.03/13.22     ( ( r1_tarski @ A @ B ) <=>
% 13.03/13.22       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 13.03/13.22  thf('10', plain,
% 13.03/13.22      (![X6 : $i, X8 : $i]:
% 13.03/13.22         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 13.03/13.22      inference('cnf', [status(esa)], [d3_tarski])).
% 13.03/13.22  thf(d1_xboole_0, axiom,
% 13.03/13.22    (![A:$i]:
% 13.03/13.22     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 13.03/13.22  thf('11', plain,
% 13.03/13.22      (![X2 : $i, X3 : $i]: (~ (r2_hidden @ X2 @ X3) | ~ (v1_xboole_0 @ X3))),
% 13.03/13.22      inference('cnf', [status(esa)], [d1_xboole_0])).
% 13.03/13.22  thf('12', plain,
% 13.03/13.22      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 13.03/13.22      inference('sup-', [status(thm)], ['10', '11'])).
% 13.03/13.22  thf(d10_xboole_0, axiom,
% 13.03/13.22    (![A:$i,B:$i]:
% 13.03/13.22     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 13.03/13.22  thf('13', plain,
% 13.03/13.22      (![X10 : $i, X12 : $i]:
% 13.03/13.22         (((X10) = (X12))
% 13.03/13.22          | ~ (r1_tarski @ X12 @ X10)
% 13.03/13.22          | ~ (r1_tarski @ X10 @ X12))),
% 13.03/13.22      inference('cnf', [status(esa)], [d10_xboole_0])).
% 13.03/13.22  thf('14', plain,
% 13.03/13.22      (![X0 : $i, X1 : $i]:
% 13.03/13.22         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 13.03/13.22      inference('sup-', [status(thm)], ['12', '13'])).
% 13.03/13.22  thf('15', plain,
% 13.03/13.22      (![X0 : $i, X1 : $i]:
% 13.03/13.22         ((v2_tex_2 @ X0 @ X1)
% 13.03/13.22          | ~ (l1_pre_topc @ X1)
% 13.03/13.22          | ~ (v1_xboole_0 @ X0)
% 13.03/13.22          | ((sk_C_1 @ X0 @ X1) = (X0))
% 13.03/13.22          | ~ (v1_xboole_0 @ X0))),
% 13.03/13.22      inference('sup-', [status(thm)], ['9', '14'])).
% 13.03/13.22  thf('16', plain,
% 13.03/13.22      (![X0 : $i, X1 : $i]:
% 13.03/13.22         (((sk_C_1 @ X0 @ X1) = (X0))
% 13.03/13.22          | ~ (v1_xboole_0 @ X0)
% 13.03/13.22          | ~ (l1_pre_topc @ X1)
% 13.03/13.22          | (v2_tex_2 @ X0 @ X1))),
% 13.03/13.22      inference('simplify', [status(thm)], ['15'])).
% 13.03/13.22  thf('17', plain,
% 13.03/13.22      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X9))),
% 13.03/13.22      inference('cnf', [status(esa)], [l13_xboole_0])).
% 13.03/13.22  thf('18', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 13.03/13.22      inference('demod', [status(thm)], ['0', '3'])).
% 13.03/13.22  thf('19', plain,
% 13.03/13.22      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 13.03/13.22      inference('sup-', [status(thm)], ['17', '18'])).
% 13.03/13.22  thf('20', plain,
% 13.03/13.22      (![X0 : $i]:
% 13.03/13.22         (~ (l1_pre_topc @ sk_A)
% 13.03/13.22          | ~ (v1_xboole_0 @ X0)
% 13.03/13.22          | ((sk_C_1 @ X0 @ sk_A) = (X0))
% 13.03/13.22          | ~ (v1_xboole_0 @ X0))),
% 13.03/13.22      inference('sup-', [status(thm)], ['16', '19'])).
% 13.03/13.22  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 13.03/13.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.03/13.22  thf('22', plain,
% 13.03/13.22      (![X0 : $i]:
% 13.03/13.22         (~ (v1_xboole_0 @ X0)
% 13.03/13.22          | ((sk_C_1 @ X0 @ sk_A) = (X0))
% 13.03/13.22          | ~ (v1_xboole_0 @ X0))),
% 13.03/13.22      inference('demod', [status(thm)], ['20', '21'])).
% 13.03/13.22  thf('23', plain,
% 13.03/13.22      (![X0 : $i]: (((sk_C_1 @ X0 @ sk_A) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 13.03/13.22      inference('simplify', [status(thm)], ['22'])).
% 13.03/13.22  thf('24', plain,
% 13.03/13.22      (![X0 : $i, X1 : $i]:
% 13.03/13.22         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 13.03/13.22      inference('sup+', [status(thm)], ['5', '6'])).
% 13.03/13.22  thf(cc2_pre_topc, axiom,
% 13.03/13.22    (![A:$i]:
% 13.03/13.22     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 13.03/13.22       ( ![B:$i]:
% 13.03/13.22         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 13.03/13.22           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 13.03/13.22  thf('25', plain,
% 13.03/13.22      (![X24 : $i, X25 : $i]:
% 13.03/13.22         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 13.03/13.22          | (v4_pre_topc @ X24 @ X25)
% 13.03/13.22          | ~ (v1_xboole_0 @ X24)
% 13.03/13.22          | ~ (l1_pre_topc @ X25)
% 13.03/13.22          | ~ (v2_pre_topc @ X25))),
% 13.03/13.22      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 13.03/13.22  thf('26', plain,
% 13.03/13.22      (![X0 : $i, X1 : $i]:
% 13.03/13.22         (~ (v1_xboole_0 @ X1)
% 13.03/13.22          | ~ (v2_pre_topc @ X0)
% 13.03/13.22          | ~ (l1_pre_topc @ X0)
% 13.03/13.22          | ~ (v1_xboole_0 @ X1)
% 13.03/13.22          | (v4_pre_topc @ X1 @ X0))),
% 13.03/13.22      inference('sup-', [status(thm)], ['24', '25'])).
% 13.03/13.22  thf('27', plain,
% 13.03/13.22      (![X0 : $i, X1 : $i]:
% 13.03/13.22         ((v4_pre_topc @ X1 @ X0)
% 13.03/13.22          | ~ (l1_pre_topc @ X0)
% 13.03/13.22          | ~ (v2_pre_topc @ X0)
% 13.03/13.22          | ~ (v1_xboole_0 @ X1))),
% 13.03/13.22      inference('simplify', [status(thm)], ['26'])).
% 13.03/13.22  thf('28', plain,
% 13.03/13.22      (![X20 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 13.03/13.22      inference('cnf', [status(esa)], [t4_subset_1])).
% 13.03/13.22  thf('29', plain,
% 13.03/13.22      (![X0 : $i, X1 : $i]:
% 13.03/13.22         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 13.03/13.22      inference('sup+', [status(thm)], ['5', '6'])).
% 13.03/13.22  thf('30', plain,
% 13.03/13.22      (![X26 : $i, X27 : $i, X29 : $i]:
% 13.03/13.22         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 13.03/13.22          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 13.03/13.22          | ~ (v4_pre_topc @ X29 @ X27)
% 13.03/13.22          | ((k9_subset_1 @ (u1_struct_0 @ X27) @ X26 @ X29)
% 13.03/13.22              != (sk_C_1 @ X26 @ X27))
% 13.03/13.22          | (v2_tex_2 @ X26 @ X27)
% 13.03/13.22          | ~ (l1_pre_topc @ X27))),
% 13.03/13.22      inference('cnf', [status(esa)], [d6_tex_2])).
% 13.03/13.22  thf('31', plain,
% 13.03/13.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.03/13.22         (~ (v1_xboole_0 @ X1)
% 13.03/13.22          | ~ (l1_pre_topc @ X0)
% 13.03/13.22          | (v2_tex_2 @ X1 @ X0)
% 13.03/13.22          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ X2) != (sk_C_1 @ X1 @ X0))
% 13.03/13.22          | ~ (v4_pre_topc @ X2 @ X0)
% 13.03/13.22          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 13.03/13.22      inference('sup-', [status(thm)], ['29', '30'])).
% 13.03/13.22  thf('32', plain,
% 13.03/13.22      (![X0 : $i, X1 : $i]:
% 13.03/13.22         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 13.03/13.22          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ k1_xboole_0)
% 13.03/13.22              != (sk_C_1 @ X1 @ X0))
% 13.03/13.22          | (v2_tex_2 @ X1 @ X0)
% 13.03/13.22          | ~ (l1_pre_topc @ X0)
% 13.03/13.22          | ~ (v1_xboole_0 @ X1))),
% 13.03/13.22      inference('sup-', [status(thm)], ['28', '31'])).
% 13.03/13.22  thf('33', plain,
% 13.03/13.22      (![X20 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X20))),
% 13.03/13.22      inference('cnf', [status(esa)], [t4_subset_1])).
% 13.03/13.22  thf(redefinition_k9_subset_1, axiom,
% 13.03/13.22    (![A:$i,B:$i,C:$i]:
% 13.03/13.22     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 13.03/13.22       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 13.03/13.22  thf('34', plain,
% 13.03/13.22      (![X17 : $i, X18 : $i, X19 : $i]:
% 13.03/13.22         (((k9_subset_1 @ X19 @ X17 @ X18) = (k3_xboole_0 @ X17 @ X18))
% 13.03/13.22          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 13.03/13.22      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 13.03/13.22  thf('35', plain,
% 13.03/13.22      (![X0 : $i, X1 : $i]:
% 13.03/13.22         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 13.03/13.22           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 13.03/13.22      inference('sup-', [status(thm)], ['33', '34'])).
% 13.03/13.22  thf(t48_xboole_1, axiom,
% 13.03/13.22    (![A:$i,B:$i]:
% 13.03/13.22     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 13.03/13.22  thf('36', plain,
% 13.03/13.22      (![X14 : $i, X15 : $i]:
% 13.03/13.22         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 13.03/13.22           = (k3_xboole_0 @ X14 @ X15))),
% 13.03/13.22      inference('cnf', [status(esa)], [t48_xboole_1])).
% 13.03/13.22  thf(t4_boole, axiom,
% 13.03/13.22    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 13.03/13.22  thf('37', plain,
% 13.03/13.22      (![X16 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 13.03/13.22      inference('cnf', [status(esa)], [t4_boole])).
% 13.03/13.22  thf('38', plain,
% 13.03/13.22      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 13.03/13.22      inference('sup+', [status(thm)], ['36', '37'])).
% 13.03/13.22  thf(commutativity_k3_xboole_0, axiom,
% 13.03/13.22    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 13.03/13.22  thf('39', plain,
% 13.03/13.22      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 13.03/13.22      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 13.03/13.22  thf('40', plain,
% 13.03/13.22      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 13.03/13.22      inference('sup+', [status(thm)], ['38', '39'])).
% 13.03/13.22  thf('41', plain,
% 13.03/13.22      (![X0 : $i, X1 : $i]:
% 13.03/13.22         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 13.03/13.22      inference('demod', [status(thm)], ['35', '40'])).
% 13.03/13.22  thf('42', plain,
% 13.03/13.22      (![X0 : $i, X1 : $i]:
% 13.03/13.22         (~ (v4_pre_topc @ k1_xboole_0 @ X0)
% 13.03/13.22          | ((k1_xboole_0) != (sk_C_1 @ X1 @ X0))
% 13.03/13.22          | (v2_tex_2 @ X1 @ X0)
% 13.03/13.22          | ~ (l1_pre_topc @ X0)
% 13.03/13.22          | ~ (v1_xboole_0 @ X1))),
% 13.03/13.22      inference('demod', [status(thm)], ['32', '41'])).
% 13.03/13.22  thf('43', plain,
% 13.03/13.22      (![X0 : $i, X1 : $i]:
% 13.03/13.22         (~ (v1_xboole_0 @ k1_xboole_0)
% 13.03/13.22          | ~ (v2_pre_topc @ X0)
% 13.03/13.22          | ~ (l1_pre_topc @ X0)
% 13.03/13.22          | ~ (v1_xboole_0 @ X1)
% 13.03/13.22          | ~ (l1_pre_topc @ X0)
% 13.03/13.22          | (v2_tex_2 @ X1 @ X0)
% 13.03/13.22          | ((k1_xboole_0) != (sk_C_1 @ X1 @ X0)))),
% 13.03/13.22      inference('sup-', [status(thm)], ['27', '42'])).
% 13.03/13.22  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 13.03/13.22  thf('44', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 13.03/13.22      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 13.03/13.22  thf('45', plain,
% 13.03/13.22      (![X0 : $i, X1 : $i]:
% 13.03/13.22         (~ (v2_pre_topc @ X0)
% 13.03/13.22          | ~ (l1_pre_topc @ X0)
% 13.03/13.22          | ~ (v1_xboole_0 @ X1)
% 13.03/13.22          | ~ (l1_pre_topc @ X0)
% 13.03/13.22          | (v2_tex_2 @ X1 @ X0)
% 13.03/13.22          | ((k1_xboole_0) != (sk_C_1 @ X1 @ X0)))),
% 13.03/13.22      inference('demod', [status(thm)], ['43', '44'])).
% 13.03/13.22  thf('46', plain,
% 13.03/13.22      (![X0 : $i, X1 : $i]:
% 13.03/13.22         (((k1_xboole_0) != (sk_C_1 @ X1 @ X0))
% 13.03/13.22          | (v2_tex_2 @ X1 @ X0)
% 13.03/13.22          | ~ (v1_xboole_0 @ X1)
% 13.03/13.22          | ~ (l1_pre_topc @ X0)
% 13.03/13.22          | ~ (v2_pre_topc @ X0))),
% 13.03/13.22      inference('simplify', [status(thm)], ['45'])).
% 13.03/13.22  thf('47', plain,
% 13.03/13.22      (![X0 : $i]:
% 13.03/13.22         (((k1_xboole_0) != (X0))
% 13.03/13.22          | ~ (v1_xboole_0 @ X0)
% 13.03/13.22          | ~ (v2_pre_topc @ sk_A)
% 13.03/13.22          | ~ (l1_pre_topc @ sk_A)
% 13.03/13.22          | ~ (v1_xboole_0 @ X0)
% 13.03/13.22          | (v2_tex_2 @ X0 @ sk_A))),
% 13.03/13.22      inference('sup-', [status(thm)], ['23', '46'])).
% 13.03/13.22  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 13.03/13.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.03/13.22  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 13.03/13.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.03/13.22  thf('50', plain,
% 13.03/13.22      (![X0 : $i]:
% 13.03/13.22         (((k1_xboole_0) != (X0))
% 13.03/13.22          | ~ (v1_xboole_0 @ X0)
% 13.03/13.22          | ~ (v1_xboole_0 @ X0)
% 13.03/13.22          | (v2_tex_2 @ X0 @ sk_A))),
% 13.03/13.22      inference('demod', [status(thm)], ['47', '48', '49'])).
% 13.03/13.22  thf('51', plain,
% 13.03/13.22      (((v2_tex_2 @ k1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 13.03/13.22      inference('simplify', [status(thm)], ['50'])).
% 13.03/13.22  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 13.03/13.22      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 13.03/13.22  thf('53', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 13.03/13.22      inference('simplify_reflect+', [status(thm)], ['51', '52'])).
% 13.03/13.22  thf('54', plain, ($false), inference('demod', [status(thm)], ['4', '53'])).
% 13.03/13.22  
% 13.03/13.22  % SZS output end Refutation
% 13.03/13.22  
% 13.03/13.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
