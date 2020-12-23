%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Iji4HiwVKn

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:12 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 337 expanded)
%              Number of leaves         :   36 ( 115 expanded)
%              Depth                    :   17
%              Number of atoms          :  956 (3058 expanded)
%              Number of equality atoms :   54 ( 170 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(t31_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ B @ C )
            <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X32 @ X33 )
        = ( k4_xboole_0 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ X40 )
      = ( k4_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X32 @ X33 )
        = ( k6_subset_1 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k6_subset_1 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X32 @ X33 )
        = ( k6_subset_1 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('9',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_C_2 ) @ ( k6_subset_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['1','6','9'])).

thf('11',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k6_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('13',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k6_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['12','14'])).

thf('16',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k6_subset_1 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('17',plain,
    ( ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_C_2 ) @ ( k6_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ~ ( r1_tarski @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('19',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ X40 )
      = ( k4_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ~ ( r1_tarski @ X9 @ ( k6_subset_1 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_xboole_0 @ ( k6_subset_1 @ sk_A @ sk_C_2 ) @ sk_B_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('23',plain,
    ( ( r1_xboole_0 @ sk_B_1 @ ( k6_subset_1 @ sk_A @ sk_C_2 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('24',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('25',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k3_xboole_0 @ sk_B_1 @ ( k6_subset_1 @ sk_A @ sk_C_2 ) )
      = k1_xboole_0 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('29',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ X40 )
      = ( k4_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k6_subset_1 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k6_subset_1 @ sk_B_1 @ ( k6_subset_1 @ sk_A @ sk_C_2 ) )
      = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('32',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('33',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ X40 )
      = ( k4_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('34',plain,(
    ! [X18: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X18 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('36',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ X40 )
      = ( k4_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('37',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k6_subset_1 @ X23 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('39',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k6_subset_1 @ sk_B_1 @ ( k6_subset_1 @ sk_A @ sk_C_2 ) )
      = sk_B_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['31','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('43',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ X30 )
      | ( r2_hidden @ X29 @ X30 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('45',plain,(
    ! [X36: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('46',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('47',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X26 )
      | ( r1_tarski @ X27 @ X25 )
      | ( X26
       != ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('48',plain,(
    ! [X25: $i,X27: $i] :
      ( ( r1_tarski @ X27 @ X25 )
      | ~ ( r2_hidden @ X27 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['46','48'])).

thf(t33_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('50',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ ( k4_xboole_0 @ X13 @ X15 ) @ ( k4_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t33_xboole_1])).

thf('51',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ X40 )
      = ( k4_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('52',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ X40 )
      = ( k4_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('53',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ ( k6_subset_1 @ X13 @ X15 ) @ ( k6_subset_1 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_B_1 @ X0 ) @ ( k6_subset_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','53'])).

thf('55',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k6_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ sk_C_2 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['41','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('57',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X38 @ ( k3_subset_1 @ X38 @ X37 ) )
        = X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('58',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k6_subset_1 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('60',plain,
    ( ( k3_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ sk_C_2 ) )
    = sk_C_2 ),
    inference(demod,[status(thm)],['58','59'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('61',plain,(
    ! [X34: $i,X35: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X34 @ X35 ) @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('62',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X32 @ X33 )
        = ( k6_subset_1 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k6_subset_1 @ sk_A @ ( k6_subset_1 @ sk_A @ sk_C_2 ) )
    = sk_C_2 ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['55','64'])).

thf('66',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_C_2 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['11','67'])).

thf('69',plain,(
    ~ ( r1_tarski @ ( k6_subset_1 @ sk_A @ sk_C_2 ) @ ( k6_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['10','68'])).

thf('70',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['13'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('71',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ( r1_xboole_0 @ X19 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('72',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ X40 )
      = ( k4_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('73',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ( r1_xboole_0 @ X19 @ ( k6_subset_1 @ X21 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B_1 @ ( k6_subset_1 @ X0 @ sk_C_2 ) )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('76',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k6_subset_1 @ X0 @ sk_C_2 ) @ sk_B_1 )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ ( k6_subset_1 @ X0 @ sk_C_2 ) @ sk_B_1 )
        = k1_xboole_0 )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k6_subset_1 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ( k6_subset_1 @ ( k6_subset_1 @ X0 @ sk_C_2 ) @ sk_B_1 )
        = ( k5_xboole_0 @ ( k6_subset_1 @ X0 @ sk_C_2 ) @ k1_xboole_0 ) )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ( k6_subset_1 @ ( k6_subset_1 @ X0 @ sk_C_2 ) @ sk_B_1 )
        = ( k6_subset_1 @ X0 @ sk_C_2 ) )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('84',plain,(
    r1_tarski @ sk_B_1 @ sk_C_2 ),
    inference('sat_resolution*',[status(thm)],['11','67','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X0 @ sk_C_2 ) @ sk_B_1 )
      = ( k6_subset_1 @ X0 @ sk_C_2 ) ) ),
    inference(simpl_trail,[status(thm)],['82','84'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('86',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('87',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k6_subset_1 @ X39 @ X40 )
      = ( k4_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('88',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X16 @ X17 ) @ X16 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ ( k6_subset_1 @ X13 @ X15 ) @ ( k6_subset_1 @ X14 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 ) @ ( k6_subset_1 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ sk_C_2 ) @ ( k6_subset_1 @ X0 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['85','90'])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['69','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Iji4HiwVKn
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:37:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.85/1.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.85/1.07  % Solved by: fo/fo7.sh
% 0.85/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.85/1.07  % done 1748 iterations in 0.601s
% 0.85/1.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.85/1.07  % SZS output start Refutation
% 0.85/1.07  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.85/1.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.85/1.07  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.85/1.07  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.85/1.07  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.85/1.07  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.85/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.85/1.07  thf(sk_B_type, type, sk_B: $i > $i).
% 0.85/1.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.85/1.07  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.85/1.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.85/1.07  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.85/1.07  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.85/1.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.85/1.07  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.85/1.07  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.85/1.07  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.85/1.07  thf(t31_subset_1, conjecture,
% 0.85/1.07    (![A:$i,B:$i]:
% 0.85/1.07     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.85/1.07       ( ![C:$i]:
% 0.85/1.07         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.85/1.07           ( ( r1_tarski @ B @ C ) <=>
% 0.85/1.07             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.85/1.07  thf(zf_stmt_0, negated_conjecture,
% 0.85/1.07    (~( ![A:$i,B:$i]:
% 0.85/1.07        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.85/1.07          ( ![C:$i]:
% 0.85/1.07            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.85/1.07              ( ( r1_tarski @ B @ C ) <=>
% 0.85/1.07                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.85/1.07    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 0.85/1.07  thf('0', plain,
% 0.85/1.07      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 0.85/1.07           (k3_subset_1 @ sk_A @ sk_B_1))
% 0.85/1.07        | ~ (r1_tarski @ sk_B_1 @ sk_C_2))),
% 0.85/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.07  thf('1', plain,
% 0.85/1.07      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 0.85/1.07           (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.85/1.07         <= (~
% 0.85/1.07             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 0.85/1.07               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.85/1.07      inference('split', [status(esa)], ['0'])).
% 0.85/1.07  thf('2', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.85/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.07  thf(d5_subset_1, axiom,
% 0.85/1.07    (![A:$i,B:$i]:
% 0.85/1.07     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.85/1.07       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.85/1.07  thf('3', plain,
% 0.85/1.07      (![X32 : $i, X33 : $i]:
% 0.85/1.07         (((k3_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))
% 0.85/1.07          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 0.85/1.07      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.85/1.07  thf(redefinition_k6_subset_1, axiom,
% 0.85/1.07    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.85/1.07  thf('4', plain,
% 0.85/1.07      (![X39 : $i, X40 : $i]:
% 0.85/1.07         ((k6_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))),
% 0.85/1.07      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.85/1.07  thf('5', plain,
% 0.85/1.07      (![X32 : $i, X33 : $i]:
% 0.85/1.07         (((k3_subset_1 @ X32 @ X33) = (k6_subset_1 @ X32 @ X33))
% 0.85/1.07          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 0.85/1.07      inference('demod', [status(thm)], ['3', '4'])).
% 0.85/1.07  thf('6', plain,
% 0.85/1.07      (((k3_subset_1 @ sk_A @ sk_C_2) = (k6_subset_1 @ sk_A @ sk_C_2))),
% 0.85/1.07      inference('sup-', [status(thm)], ['2', '5'])).
% 0.85/1.07  thf('7', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.85/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.07  thf('8', plain,
% 0.85/1.07      (![X32 : $i, X33 : $i]:
% 0.85/1.07         (((k3_subset_1 @ X32 @ X33) = (k6_subset_1 @ X32 @ X33))
% 0.85/1.07          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 0.85/1.07      inference('demod', [status(thm)], ['3', '4'])).
% 0.85/1.07  thf('9', plain,
% 0.85/1.07      (((k3_subset_1 @ sk_A @ sk_B_1) = (k6_subset_1 @ sk_A @ sk_B_1))),
% 0.85/1.07      inference('sup-', [status(thm)], ['7', '8'])).
% 0.85/1.07  thf('10', plain,
% 0.85/1.07      ((~ (r1_tarski @ (k6_subset_1 @ sk_A @ sk_C_2) @ 
% 0.85/1.07           (k6_subset_1 @ sk_A @ sk_B_1)))
% 0.85/1.07         <= (~
% 0.85/1.07             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 0.85/1.07               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.85/1.07      inference('demod', [status(thm)], ['1', '6', '9'])).
% 0.85/1.07  thf('11', plain,
% 0.85/1.07      (~
% 0.85/1.07       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 0.85/1.07         (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.85/1.07       ~ ((r1_tarski @ sk_B_1 @ sk_C_2))),
% 0.85/1.07      inference('split', [status(esa)], ['0'])).
% 0.85/1.07  thf('12', plain,
% 0.85/1.07      (((k3_subset_1 @ sk_A @ sk_B_1) = (k6_subset_1 @ sk_A @ sk_B_1))),
% 0.85/1.07      inference('sup-', [status(thm)], ['7', '8'])).
% 0.85/1.07  thf('13', plain,
% 0.85/1.07      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 0.85/1.07         (k3_subset_1 @ sk_A @ sk_B_1))
% 0.85/1.07        | (r1_tarski @ sk_B_1 @ sk_C_2))),
% 0.85/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.07  thf('14', plain,
% 0.85/1.07      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 0.85/1.07         (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.85/1.07         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 0.85/1.07               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.85/1.07      inference('split', [status(esa)], ['13'])).
% 0.85/1.07  thf('15', plain,
% 0.85/1.07      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 0.85/1.07         (k6_subset_1 @ sk_A @ sk_B_1)))
% 0.85/1.07         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 0.85/1.07               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.85/1.07      inference('sup+', [status(thm)], ['12', '14'])).
% 0.85/1.07  thf('16', plain,
% 0.85/1.07      (((k3_subset_1 @ sk_A @ sk_C_2) = (k6_subset_1 @ sk_A @ sk_C_2))),
% 0.85/1.07      inference('sup-', [status(thm)], ['2', '5'])).
% 0.85/1.07  thf('17', plain,
% 0.85/1.07      (((r1_tarski @ (k6_subset_1 @ sk_A @ sk_C_2) @ 
% 0.85/1.07         (k6_subset_1 @ sk_A @ sk_B_1)))
% 0.85/1.07         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 0.85/1.07               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.85/1.07      inference('demod', [status(thm)], ['15', '16'])).
% 0.85/1.07  thf(t106_xboole_1, axiom,
% 0.85/1.07    (![A:$i,B:$i,C:$i]:
% 0.85/1.07     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.85/1.07       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.85/1.07  thf('18', plain,
% 0.85/1.07      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.85/1.07         ((r1_xboole_0 @ X9 @ X11)
% 0.85/1.07          | ~ (r1_tarski @ X9 @ (k4_xboole_0 @ X10 @ X11)))),
% 0.85/1.07      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.85/1.07  thf('19', plain,
% 0.85/1.07      (![X39 : $i, X40 : $i]:
% 0.85/1.07         ((k6_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))),
% 0.85/1.07      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.85/1.07  thf('20', plain,
% 0.85/1.07      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.85/1.07         ((r1_xboole_0 @ X9 @ X11)
% 0.85/1.07          | ~ (r1_tarski @ X9 @ (k6_subset_1 @ X10 @ X11)))),
% 0.85/1.07      inference('demod', [status(thm)], ['18', '19'])).
% 0.85/1.07  thf('21', plain,
% 0.85/1.07      (((r1_xboole_0 @ (k6_subset_1 @ sk_A @ sk_C_2) @ sk_B_1))
% 0.85/1.07         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 0.85/1.07               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.85/1.07      inference('sup-', [status(thm)], ['17', '20'])).
% 0.85/1.07  thf(symmetry_r1_xboole_0, axiom,
% 0.85/1.07    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.85/1.07  thf('22', plain,
% 0.85/1.07      (![X0 : $i, X1 : $i]:
% 0.85/1.07         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.85/1.07      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.85/1.07  thf('23', plain,
% 0.85/1.07      (((r1_xboole_0 @ sk_B_1 @ (k6_subset_1 @ sk_A @ sk_C_2)))
% 0.85/1.07         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 0.85/1.07               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.85/1.07      inference('sup-', [status(thm)], ['21', '22'])).
% 0.85/1.07  thf(t7_xboole_0, axiom,
% 0.85/1.07    (![A:$i]:
% 0.85/1.07     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.85/1.07          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.85/1.07  thf('24', plain,
% 0.85/1.07      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.85/1.07      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.85/1.07  thf(t4_xboole_0, axiom,
% 0.85/1.07    (![A:$i,B:$i]:
% 0.85/1.07     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.85/1.07            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.85/1.07       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.85/1.07            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.85/1.07  thf('25', plain,
% 0.85/1.07      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.85/1.07         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.85/1.07          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.85/1.07      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.85/1.07  thf('26', plain,
% 0.85/1.07      (![X0 : $i, X1 : $i]:
% 0.85/1.07         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.85/1.07      inference('sup-', [status(thm)], ['24', '25'])).
% 0.85/1.07  thf('27', plain,
% 0.85/1.07      ((((k3_xboole_0 @ sk_B_1 @ (k6_subset_1 @ sk_A @ sk_C_2)) = (k1_xboole_0)))
% 0.85/1.07         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 0.85/1.07               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.85/1.07      inference('sup-', [status(thm)], ['23', '26'])).
% 0.85/1.07  thf(t100_xboole_1, axiom,
% 0.85/1.07    (![A:$i,B:$i]:
% 0.85/1.07     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.85/1.07  thf('28', plain,
% 0.85/1.07      (![X7 : $i, X8 : $i]:
% 0.85/1.07         ((k4_xboole_0 @ X7 @ X8)
% 0.85/1.07           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.85/1.07      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.85/1.07  thf('29', plain,
% 0.85/1.07      (![X39 : $i, X40 : $i]:
% 0.85/1.07         ((k6_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))),
% 0.85/1.07      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.85/1.07  thf('30', plain,
% 0.85/1.07      (![X7 : $i, X8 : $i]:
% 0.85/1.07         ((k6_subset_1 @ X7 @ X8)
% 0.85/1.07           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.85/1.07      inference('demod', [status(thm)], ['28', '29'])).
% 0.85/1.07  thf('31', plain,
% 0.85/1.07      ((((k6_subset_1 @ sk_B_1 @ (k6_subset_1 @ sk_A @ sk_C_2))
% 0.85/1.07          = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0)))
% 0.85/1.07         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 0.85/1.07               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.85/1.07      inference('sup+', [status(thm)], ['27', '30'])).
% 0.85/1.07  thf(t4_boole, axiom,
% 0.85/1.07    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.85/1.07  thf('32', plain,
% 0.85/1.07      (![X18 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X18) = (k1_xboole_0))),
% 0.85/1.07      inference('cnf', [status(esa)], [t4_boole])).
% 0.85/1.07  thf('33', plain,
% 0.85/1.07      (![X39 : $i, X40 : $i]:
% 0.85/1.07         ((k6_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))),
% 0.85/1.07      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.85/1.07  thf('34', plain,
% 0.85/1.07      (![X18 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X18) = (k1_xboole_0))),
% 0.85/1.07      inference('demod', [status(thm)], ['32', '33'])).
% 0.85/1.07  thf(t98_xboole_1, axiom,
% 0.85/1.07    (![A:$i,B:$i]:
% 0.85/1.07     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.85/1.07  thf('35', plain,
% 0.85/1.07      (![X22 : $i, X23 : $i]:
% 0.85/1.07         ((k2_xboole_0 @ X22 @ X23)
% 0.85/1.07           = (k5_xboole_0 @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.85/1.07      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.85/1.07  thf('36', plain,
% 0.85/1.07      (![X39 : $i, X40 : $i]:
% 0.85/1.07         ((k6_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))),
% 0.85/1.07      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.85/1.07  thf('37', plain,
% 0.85/1.07      (![X22 : $i, X23 : $i]:
% 0.85/1.07         ((k2_xboole_0 @ X22 @ X23)
% 0.85/1.07           = (k5_xboole_0 @ X22 @ (k6_subset_1 @ X23 @ X22)))),
% 0.85/1.07      inference('demod', [status(thm)], ['35', '36'])).
% 0.85/1.07  thf('38', plain,
% 0.85/1.07      (![X0 : $i]:
% 0.85/1.07         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.85/1.07      inference('sup+', [status(thm)], ['34', '37'])).
% 0.85/1.07  thf(t1_boole, axiom,
% 0.85/1.07    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.85/1.07  thf('39', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.85/1.07      inference('cnf', [status(esa)], [t1_boole])).
% 0.85/1.07  thf('40', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.85/1.07      inference('sup+', [status(thm)], ['38', '39'])).
% 0.85/1.07  thf('41', plain,
% 0.85/1.07      ((((k6_subset_1 @ sk_B_1 @ (k6_subset_1 @ sk_A @ sk_C_2)) = (sk_B_1)))
% 0.85/1.07         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 0.85/1.07               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.85/1.07      inference('demod', [status(thm)], ['31', '40'])).
% 0.85/1.07  thf('42', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.85/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.07  thf(d2_subset_1, axiom,
% 0.85/1.07    (![A:$i,B:$i]:
% 0.85/1.07     ( ( ( v1_xboole_0 @ A ) =>
% 0.85/1.07         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.85/1.07       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.85/1.07         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.85/1.07  thf('43', plain,
% 0.85/1.07      (![X29 : $i, X30 : $i]:
% 0.85/1.07         (~ (m1_subset_1 @ X29 @ X30)
% 0.85/1.07          | (r2_hidden @ X29 @ X30)
% 0.85/1.07          | (v1_xboole_0 @ X30))),
% 0.85/1.07      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.85/1.07  thf('44', plain,
% 0.85/1.07      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.85/1.07        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.85/1.07      inference('sup-', [status(thm)], ['42', '43'])).
% 0.85/1.07  thf(fc1_subset_1, axiom,
% 0.85/1.07    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.85/1.07  thf('45', plain, (![X36 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 0.85/1.07      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.85/1.07  thf('46', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.85/1.07      inference('clc', [status(thm)], ['44', '45'])).
% 0.85/1.07  thf(d1_zfmisc_1, axiom,
% 0.85/1.07    (![A:$i,B:$i]:
% 0.85/1.07     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.85/1.07       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.85/1.07  thf('47', plain,
% 0.85/1.07      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.85/1.07         (~ (r2_hidden @ X27 @ X26)
% 0.85/1.07          | (r1_tarski @ X27 @ X25)
% 0.85/1.07          | ((X26) != (k1_zfmisc_1 @ X25)))),
% 0.85/1.07      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.85/1.07  thf('48', plain,
% 0.85/1.07      (![X25 : $i, X27 : $i]:
% 0.85/1.07         ((r1_tarski @ X27 @ X25) | ~ (r2_hidden @ X27 @ (k1_zfmisc_1 @ X25)))),
% 0.85/1.07      inference('simplify', [status(thm)], ['47'])).
% 0.85/1.07  thf('49', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.85/1.07      inference('sup-', [status(thm)], ['46', '48'])).
% 0.85/1.07  thf(t33_xboole_1, axiom,
% 0.85/1.07    (![A:$i,B:$i,C:$i]:
% 0.85/1.07     ( ( r1_tarski @ A @ B ) =>
% 0.85/1.07       ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.85/1.07  thf('50', plain,
% 0.85/1.07      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.85/1.07         (~ (r1_tarski @ X13 @ X14)
% 0.85/1.07          | (r1_tarski @ (k4_xboole_0 @ X13 @ X15) @ (k4_xboole_0 @ X14 @ X15)))),
% 0.85/1.07      inference('cnf', [status(esa)], [t33_xboole_1])).
% 0.85/1.07  thf('51', plain,
% 0.85/1.07      (![X39 : $i, X40 : $i]:
% 0.85/1.07         ((k6_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))),
% 0.85/1.07      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.85/1.07  thf('52', plain,
% 0.85/1.07      (![X39 : $i, X40 : $i]:
% 0.85/1.07         ((k6_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))),
% 0.85/1.07      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.85/1.07  thf('53', plain,
% 0.85/1.07      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.85/1.07         (~ (r1_tarski @ X13 @ X14)
% 0.85/1.07          | (r1_tarski @ (k6_subset_1 @ X13 @ X15) @ (k6_subset_1 @ X14 @ X15)))),
% 0.85/1.07      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.85/1.07  thf('54', plain,
% 0.85/1.07      (![X0 : $i]:
% 0.85/1.07         (r1_tarski @ (k6_subset_1 @ sk_B_1 @ X0) @ (k6_subset_1 @ sk_A @ X0))),
% 0.85/1.07      inference('sup-', [status(thm)], ['49', '53'])).
% 0.85/1.07  thf('55', plain,
% 0.85/1.07      (((r1_tarski @ sk_B_1 @ 
% 0.85/1.07         (k6_subset_1 @ sk_A @ (k6_subset_1 @ sk_A @ sk_C_2))))
% 0.85/1.07         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 0.85/1.07               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.85/1.07      inference('sup+', [status(thm)], ['41', '54'])).
% 0.85/1.07  thf('56', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.85/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.07  thf(involutiveness_k3_subset_1, axiom,
% 0.85/1.07    (![A:$i,B:$i]:
% 0.85/1.07     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.85/1.07       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.85/1.07  thf('57', plain,
% 0.85/1.07      (![X37 : $i, X38 : $i]:
% 0.85/1.07         (((k3_subset_1 @ X38 @ (k3_subset_1 @ X38 @ X37)) = (X37))
% 0.85/1.07          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38)))),
% 0.85/1.07      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.85/1.07  thf('58', plain,
% 0.85/1.07      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_2)) = (sk_C_2))),
% 0.85/1.07      inference('sup-', [status(thm)], ['56', '57'])).
% 0.85/1.07  thf('59', plain,
% 0.85/1.07      (((k3_subset_1 @ sk_A @ sk_C_2) = (k6_subset_1 @ sk_A @ sk_C_2))),
% 0.85/1.07      inference('sup-', [status(thm)], ['2', '5'])).
% 0.85/1.07  thf('60', plain,
% 0.85/1.07      (((k3_subset_1 @ sk_A @ (k6_subset_1 @ sk_A @ sk_C_2)) = (sk_C_2))),
% 0.85/1.07      inference('demod', [status(thm)], ['58', '59'])).
% 0.85/1.07  thf(dt_k6_subset_1, axiom,
% 0.85/1.07    (![A:$i,B:$i]:
% 0.85/1.07     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.85/1.07  thf('61', plain,
% 0.85/1.07      (![X34 : $i, X35 : $i]:
% 0.85/1.07         (m1_subset_1 @ (k6_subset_1 @ X34 @ X35) @ (k1_zfmisc_1 @ X34))),
% 0.85/1.07      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.85/1.07  thf('62', plain,
% 0.85/1.07      (![X32 : $i, X33 : $i]:
% 0.85/1.07         (((k3_subset_1 @ X32 @ X33) = (k6_subset_1 @ X32 @ X33))
% 0.85/1.07          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 0.85/1.07      inference('demod', [status(thm)], ['3', '4'])).
% 0.85/1.07  thf('63', plain,
% 0.85/1.07      (![X0 : $i, X1 : $i]:
% 0.85/1.07         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 0.85/1.07           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 0.85/1.07      inference('sup-', [status(thm)], ['61', '62'])).
% 0.85/1.07  thf('64', plain,
% 0.85/1.07      (((k6_subset_1 @ sk_A @ (k6_subset_1 @ sk_A @ sk_C_2)) = (sk_C_2))),
% 0.85/1.07      inference('demod', [status(thm)], ['60', '63'])).
% 0.85/1.07  thf('65', plain,
% 0.85/1.07      (((r1_tarski @ sk_B_1 @ sk_C_2))
% 0.85/1.07         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 0.85/1.07               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.85/1.07      inference('demod', [status(thm)], ['55', '64'])).
% 0.85/1.07  thf('66', plain,
% 0.85/1.07      ((~ (r1_tarski @ sk_B_1 @ sk_C_2)) <= (~ ((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 0.85/1.07      inference('split', [status(esa)], ['0'])).
% 0.85/1.07  thf('67', plain,
% 0.85/1.07      (((r1_tarski @ sk_B_1 @ sk_C_2)) | 
% 0.85/1.07       ~
% 0.85/1.07       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 0.85/1.07         (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.85/1.07      inference('sup-', [status(thm)], ['65', '66'])).
% 0.85/1.07  thf('68', plain,
% 0.85/1.07      (~
% 0.85/1.07       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 0.85/1.07         (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.85/1.07      inference('sat_resolution*', [status(thm)], ['11', '67'])).
% 0.85/1.07  thf('69', plain,
% 0.85/1.07      (~ (r1_tarski @ (k6_subset_1 @ sk_A @ sk_C_2) @ 
% 0.85/1.07          (k6_subset_1 @ sk_A @ sk_B_1))),
% 0.85/1.07      inference('simpl_trail', [status(thm)], ['10', '68'])).
% 0.85/1.07  thf('70', plain,
% 0.85/1.07      (((r1_tarski @ sk_B_1 @ sk_C_2)) <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 0.85/1.07      inference('split', [status(esa)], ['13'])).
% 0.85/1.07  thf(t85_xboole_1, axiom,
% 0.85/1.07    (![A:$i,B:$i,C:$i]:
% 0.85/1.07     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.85/1.07  thf('71', plain,
% 0.85/1.07      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.85/1.07         (~ (r1_tarski @ X19 @ X20)
% 0.85/1.07          | (r1_xboole_0 @ X19 @ (k4_xboole_0 @ X21 @ X20)))),
% 0.85/1.07      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.85/1.07  thf('72', plain,
% 0.85/1.07      (![X39 : $i, X40 : $i]:
% 0.85/1.07         ((k6_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))),
% 0.85/1.07      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.85/1.07  thf('73', plain,
% 0.85/1.07      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.85/1.07         (~ (r1_tarski @ X19 @ X20)
% 0.85/1.07          | (r1_xboole_0 @ X19 @ (k6_subset_1 @ X21 @ X20)))),
% 0.85/1.07      inference('demod', [status(thm)], ['71', '72'])).
% 0.85/1.07  thf('74', plain,
% 0.85/1.07      ((![X0 : $i]: (r1_xboole_0 @ sk_B_1 @ (k6_subset_1 @ X0 @ sk_C_2)))
% 0.85/1.07         <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 0.85/1.07      inference('sup-', [status(thm)], ['70', '73'])).
% 0.85/1.07  thf('75', plain,
% 0.85/1.07      (![X0 : $i, X1 : $i]:
% 0.85/1.07         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.85/1.07      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.85/1.07  thf('76', plain,
% 0.85/1.07      ((![X0 : $i]: (r1_xboole_0 @ (k6_subset_1 @ X0 @ sk_C_2) @ sk_B_1))
% 0.85/1.07         <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 0.85/1.07      inference('sup-', [status(thm)], ['74', '75'])).
% 0.85/1.07  thf('77', plain,
% 0.85/1.07      (![X0 : $i, X1 : $i]:
% 0.85/1.07         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.85/1.07      inference('sup-', [status(thm)], ['24', '25'])).
% 0.85/1.07  thf('78', plain,
% 0.85/1.07      ((![X0 : $i]:
% 0.85/1.07          ((k3_xboole_0 @ (k6_subset_1 @ X0 @ sk_C_2) @ sk_B_1) = (k1_xboole_0)))
% 0.85/1.07         <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 0.85/1.07      inference('sup-', [status(thm)], ['76', '77'])).
% 0.85/1.07  thf('79', plain,
% 0.85/1.07      (![X7 : $i, X8 : $i]:
% 0.85/1.07         ((k6_subset_1 @ X7 @ X8)
% 0.85/1.07           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.85/1.07      inference('demod', [status(thm)], ['28', '29'])).
% 0.85/1.07  thf('80', plain,
% 0.85/1.07      ((![X0 : $i]:
% 0.85/1.07          ((k6_subset_1 @ (k6_subset_1 @ X0 @ sk_C_2) @ sk_B_1)
% 0.85/1.07            = (k5_xboole_0 @ (k6_subset_1 @ X0 @ sk_C_2) @ k1_xboole_0)))
% 0.85/1.07         <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 0.85/1.07      inference('sup+', [status(thm)], ['78', '79'])).
% 0.85/1.07  thf('81', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.85/1.07      inference('sup+', [status(thm)], ['38', '39'])).
% 0.85/1.07  thf('82', plain,
% 0.85/1.07      ((![X0 : $i]:
% 0.85/1.07          ((k6_subset_1 @ (k6_subset_1 @ X0 @ sk_C_2) @ sk_B_1)
% 0.85/1.07            = (k6_subset_1 @ X0 @ sk_C_2)))
% 0.85/1.07         <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 0.85/1.07      inference('demod', [status(thm)], ['80', '81'])).
% 0.85/1.07  thf('83', plain,
% 0.85/1.07      (((r1_tarski @ sk_B_1 @ sk_C_2)) | 
% 0.85/1.07       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 0.85/1.07         (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.85/1.07      inference('split', [status(esa)], ['13'])).
% 0.85/1.07  thf('84', plain, (((r1_tarski @ sk_B_1 @ sk_C_2))),
% 0.85/1.07      inference('sat_resolution*', [status(thm)], ['11', '67', '83'])).
% 0.85/1.07  thf('85', plain,
% 0.85/1.07      (![X0 : $i]:
% 0.85/1.07         ((k6_subset_1 @ (k6_subset_1 @ X0 @ sk_C_2) @ sk_B_1)
% 0.85/1.07           = (k6_subset_1 @ X0 @ sk_C_2))),
% 0.85/1.07      inference('simpl_trail', [status(thm)], ['82', '84'])).
% 0.85/1.07  thf(t36_xboole_1, axiom,
% 0.85/1.07    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.85/1.07  thf('86', plain,
% 0.85/1.07      (![X16 : $i, X17 : $i]: (r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X16)),
% 0.85/1.07      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.85/1.07  thf('87', plain,
% 0.85/1.07      (![X39 : $i, X40 : $i]:
% 0.85/1.07         ((k6_subset_1 @ X39 @ X40) = (k4_xboole_0 @ X39 @ X40))),
% 0.85/1.07      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.85/1.07  thf('88', plain,
% 0.85/1.07      (![X16 : $i, X17 : $i]: (r1_tarski @ (k6_subset_1 @ X16 @ X17) @ X16)),
% 0.85/1.07      inference('demod', [status(thm)], ['86', '87'])).
% 0.85/1.07  thf('89', plain,
% 0.85/1.07      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.85/1.07         (~ (r1_tarski @ X13 @ X14)
% 0.85/1.07          | (r1_tarski @ (k6_subset_1 @ X13 @ X15) @ (k6_subset_1 @ X14 @ X15)))),
% 0.85/1.07      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.85/1.07  thf('90', plain,
% 0.85/1.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.07         (r1_tarski @ (k6_subset_1 @ (k6_subset_1 @ X0 @ X1) @ X2) @ 
% 0.85/1.07          (k6_subset_1 @ X0 @ X2))),
% 0.85/1.07      inference('sup-', [status(thm)], ['88', '89'])).
% 0.85/1.07  thf('91', plain,
% 0.85/1.07      (![X0 : $i]:
% 0.85/1.07         (r1_tarski @ (k6_subset_1 @ X0 @ sk_C_2) @ (k6_subset_1 @ X0 @ sk_B_1))),
% 0.85/1.07      inference('sup+', [status(thm)], ['85', '90'])).
% 0.85/1.07  thf('92', plain, ($false), inference('demod', [status(thm)], ['69', '91'])).
% 0.85/1.07  
% 0.85/1.07  % SZS output end Refutation
% 0.85/1.07  
% 0.85/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
