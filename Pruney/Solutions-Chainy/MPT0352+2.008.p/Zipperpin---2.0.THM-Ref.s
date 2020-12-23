%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GQkOCxWvSx

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:08 EST 2020

% Result     : Theorem 1.00s
% Output     : Refutation 1.00s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 601 expanded)
%              Number of leaves         :   36 ( 193 expanded)
%              Depth                    :   18
%              Number of atoms          : 1258 (5240 expanded)
%              Number of equality atoms :   80 ( 263 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ X44 )
      | ( r2_hidden @ X43 @ X44 )
      | ( v1_xboole_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X48: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('6',plain,(
    r2_hidden @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X41 @ X40 )
      | ( r1_tarski @ X41 @ X39 )
      | ( X40
       != ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('8',plain,(
    ! [X39: $i,X41: $i] :
      ( ( r1_tarski @ X41 @ X39 )
      | ~ ( r2_hidden @ X41 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    r1_tarski @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_A )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k3_subset_1 @ X46 @ X47 )
        = ( k4_xboole_0 @ X46 @ X47 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ X44 )
      | ( r2_hidden @ X43 @ X44 )
      | ( v1_xboole_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X48: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('24',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X39: $i,X41: $i] :
      ( ( r1_tarski @ X41 @ X39 )
      | ~ ( r2_hidden @ X41 @ ( k1_zfmisc_1 @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('26',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k3_subset_1 @ X46 @ X47 )
        = ( k4_xboole_0 @ X46 @ X47 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('33',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['1','19','34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ~ ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('38',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('39',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X31 @ X32 ) @ X32 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('40',plain,(
    r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['41'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('43',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X28 @ X29 )
      | ~ ( r1_xboole_0 @ X29 @ X30 )
      | ( r1_xboole_0 @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ X0 )
        | ~ ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ X0 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ sk_B_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('47',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r1_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('52',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ X33 @ X34 )
      | ~ ( r1_xboole_0 @ X33 @ X35 )
      | ( r1_tarski @ X33 @ ( k4_xboole_0 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B_1 @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) )
        | ~ ( r1_tarski @ sk_B_1 @ X0 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B_1 @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) ) )
        | ~ ( r1_tarski @ sk_B_1 @ X0 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','55'])).

thf('57',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('58',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('59',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) )
    = ( k3_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('61',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_A )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('62',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) )
    = sk_C_2 ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['56','62'])).

thf('64',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_C_2 )
   <= ~ ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('65',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['36','65'])).

thf('67',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['35','66'])).

thf('68',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_A )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('69',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('70',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['70'])).

thf(t108_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ) )).

thf('72',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ( r1_tarski @ ( k3_xboole_0 @ X14 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t108_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['69','73'])).

thf('75',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('82',plain,(
    ! [X27: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X27 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X27: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X27 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('89',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k2_xboole_0 @ X36 @ X37 )
      = ( k5_xboole_0 @ X36 @ ( k4_xboole_0 @ X37 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('91',plain,(
    ! [X17: $i] :
      ( ( k2_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['87','92'])).

thf('94',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k3_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('97',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ X13 )
      = ( k5_xboole_0 @ X12 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','102'])).

thf('104',plain,
    ( ( k4_xboole_0 @ sk_C_2 @ sk_A )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['68','103'])).

thf('105',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k2_xboole_0 @ X36 @ X37 )
      = ( k5_xboole_0 @ X36 @ ( k4_xboole_0 @ X37 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('106',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('109',plain,
    ( ( k2_xboole_0 @ sk_C_2 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['70'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('111',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference('sup+',[status(thm)],['109','112'])).

thf('114',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('115',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('117',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ sk_A ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('119',plain,(
    ! [X31: $i,X32: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X31 @ X32 ) @ X32 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(split,[status(esa)],['41'])).

thf('123',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X28 @ X29 )
      | ~ ( r1_xboole_0 @ X29 @ X30 )
      | ( r1_xboole_0 @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('124',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ sk_B_1 @ X0 )
        | ~ ( r1_xboole_0 @ sk_C_2 @ X0 ) )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B_1 @ ( k4_xboole_0 @ X0 @ sk_C_2 ) )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['121','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('127',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_2 ) @ sk_B_1 )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ sk_B_1 )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['118','127'])).

thf('129',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ X33 @ X34 )
      | ~ ( r1_xboole_0 @ X33 @ X35 )
      | ( r1_tarski @ X33 @ ( k4_xboole_0 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('130',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k4_xboole_0 @ X0 @ sk_B_1 ) )
        | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ X0 ) )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('132',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k5_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('133',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ ( k4_xboole_0 @ X0 @ sk_B_1 ) )
        | ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ X0 ) )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,
    ( ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ ( k4_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['117','133'])).

thf('135',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('136',plain,
    ( ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_2 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['41'])).

thf('138',plain,(
    r1_tarski @ sk_B_1 @ sk_C_2 ),
    inference('sat_resolution*',[status(thm)],['36','65','137'])).

thf('139',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_2 ) @ ( k5_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['136','138'])).

thf('140',plain,(
    $false ),
    inference(demod,[status(thm)],['67','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GQkOCxWvSx
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:20:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 1.00/1.18  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.00/1.18  % Solved by: fo/fo7.sh
% 1.00/1.18  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.00/1.18  % done 2874 iterations in 0.732s
% 1.00/1.18  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.00/1.18  % SZS output start Refutation
% 1.00/1.18  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.00/1.18  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.00/1.18  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.00/1.18  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.00/1.18  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.00/1.18  thf(sk_A_type, type, sk_A: $i).
% 1.00/1.18  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.00/1.18  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.00/1.18  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.00/1.18  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.00/1.18  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.00/1.18  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.00/1.18  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.00/1.18  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.00/1.18  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.00/1.18  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.00/1.18  thf(t31_subset_1, conjecture,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.00/1.18       ( ![C:$i]:
% 1.00/1.18         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.00/1.18           ( ( r1_tarski @ B @ C ) <=>
% 1.00/1.18             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 1.00/1.18  thf(zf_stmt_0, negated_conjecture,
% 1.00/1.18    (~( ![A:$i,B:$i]:
% 1.00/1.18        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.00/1.18          ( ![C:$i]:
% 1.00/1.18            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.00/1.18              ( ( r1_tarski @ B @ C ) <=>
% 1.00/1.18                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 1.00/1.18    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 1.00/1.18  thf('0', plain,
% 1.00/1.18      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.00/1.18           (k3_subset_1 @ sk_A @ sk_B_1))
% 1.00/1.18        | ~ (r1_tarski @ sk_B_1 @ sk_C_2))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('1', plain,
% 1.00/1.18      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.00/1.18           (k3_subset_1 @ sk_A @ sk_B_1)))
% 1.00/1.18         <= (~
% 1.00/1.18             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.00/1.18               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 1.00/1.18      inference('split', [status(esa)], ['0'])).
% 1.00/1.18  thf('2', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf(d2_subset_1, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( ( v1_xboole_0 @ A ) =>
% 1.00/1.18         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.00/1.18       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.00/1.18         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.00/1.18  thf('3', plain,
% 1.00/1.18      (![X43 : $i, X44 : $i]:
% 1.00/1.18         (~ (m1_subset_1 @ X43 @ X44)
% 1.00/1.18          | (r2_hidden @ X43 @ X44)
% 1.00/1.18          | (v1_xboole_0 @ X44))),
% 1.00/1.18      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.00/1.18  thf('4', plain,
% 1.00/1.18      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.00/1.18        | (r2_hidden @ sk_C_2 @ (k1_zfmisc_1 @ sk_A)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['2', '3'])).
% 1.00/1.18  thf(fc1_subset_1, axiom,
% 1.00/1.18    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.00/1.18  thf('5', plain, (![X48 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X48))),
% 1.00/1.18      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.00/1.18  thf('6', plain, ((r2_hidden @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 1.00/1.18      inference('clc', [status(thm)], ['4', '5'])).
% 1.00/1.18  thf(d1_zfmisc_1, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.00/1.18       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.00/1.18  thf('7', plain,
% 1.00/1.18      (![X39 : $i, X40 : $i, X41 : $i]:
% 1.00/1.18         (~ (r2_hidden @ X41 @ X40)
% 1.00/1.18          | (r1_tarski @ X41 @ X39)
% 1.00/1.18          | ((X40) != (k1_zfmisc_1 @ X39)))),
% 1.00/1.18      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.00/1.18  thf('8', plain,
% 1.00/1.18      (![X39 : $i, X41 : $i]:
% 1.00/1.18         ((r1_tarski @ X41 @ X39) | ~ (r2_hidden @ X41 @ (k1_zfmisc_1 @ X39)))),
% 1.00/1.18      inference('simplify', [status(thm)], ['7'])).
% 1.00/1.18  thf('9', plain, ((r1_tarski @ sk_C_2 @ sk_A)),
% 1.00/1.18      inference('sup-', [status(thm)], ['6', '8'])).
% 1.00/1.18  thf(t28_xboole_1, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.00/1.18  thf('10', plain,
% 1.00/1.18      (![X18 : $i, X19 : $i]:
% 1.00/1.18         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 1.00/1.18      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.00/1.18  thf('11', plain, (((k3_xboole_0 @ sk_C_2 @ sk_A) = (sk_C_2))),
% 1.00/1.18      inference('sup-', [status(thm)], ['9', '10'])).
% 1.00/1.18  thf(commutativity_k3_xboole_0, axiom,
% 1.00/1.18    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.00/1.18  thf('12', plain,
% 1.00/1.18      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.00/1.18      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.00/1.18  thf(t100_xboole_1, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.00/1.18  thf('13', plain,
% 1.00/1.18      (![X12 : $i, X13 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ X12 @ X13)
% 1.00/1.18           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.00/1.18      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.00/1.18  thf('14', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ X0 @ X1)
% 1.00/1.18           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.00/1.18      inference('sup+', [status(thm)], ['12', '13'])).
% 1.00/1.18  thf('15', plain,
% 1.00/1.18      (((k4_xboole_0 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ sk_C_2))),
% 1.00/1.18      inference('sup+', [status(thm)], ['11', '14'])).
% 1.00/1.18  thf('16', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf(d5_subset_1, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.00/1.18       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.00/1.18  thf('17', plain,
% 1.00/1.18      (![X46 : $i, X47 : $i]:
% 1.00/1.18         (((k3_subset_1 @ X46 @ X47) = (k4_xboole_0 @ X46 @ X47))
% 1.00/1.18          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X46)))),
% 1.00/1.18      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.00/1.18  thf('18', plain,
% 1.00/1.18      (((k3_subset_1 @ sk_A @ sk_C_2) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 1.00/1.18      inference('sup-', [status(thm)], ['16', '17'])).
% 1.00/1.18  thf('19', plain,
% 1.00/1.18      (((k3_subset_1 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ sk_C_2))),
% 1.00/1.18      inference('sup+', [status(thm)], ['15', '18'])).
% 1.00/1.18  thf('20', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('21', plain,
% 1.00/1.18      (![X43 : $i, X44 : $i]:
% 1.00/1.18         (~ (m1_subset_1 @ X43 @ X44)
% 1.00/1.18          | (r2_hidden @ X43 @ X44)
% 1.00/1.18          | (v1_xboole_0 @ X44))),
% 1.00/1.18      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.00/1.18  thf('22', plain,
% 1.00/1.18      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.00/1.18        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['20', '21'])).
% 1.00/1.18  thf('23', plain, (![X48 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X48))),
% 1.00/1.18      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.00/1.18  thf('24', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.00/1.18      inference('clc', [status(thm)], ['22', '23'])).
% 1.00/1.18  thf('25', plain,
% 1.00/1.18      (![X39 : $i, X41 : $i]:
% 1.00/1.18         ((r1_tarski @ X41 @ X39) | ~ (r2_hidden @ X41 @ (k1_zfmisc_1 @ X39)))),
% 1.00/1.18      inference('simplify', [status(thm)], ['7'])).
% 1.00/1.18  thf('26', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 1.00/1.18      inference('sup-', [status(thm)], ['24', '25'])).
% 1.00/1.18  thf('27', plain,
% 1.00/1.18      (![X18 : $i, X19 : $i]:
% 1.00/1.18         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 1.00/1.18      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.00/1.18  thf('28', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 1.00/1.18      inference('sup-', [status(thm)], ['26', '27'])).
% 1.00/1.18  thf('29', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ X0 @ X1)
% 1.00/1.18           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.00/1.18      inference('sup+', [status(thm)], ['12', '13'])).
% 1.00/1.18  thf('30', plain,
% 1.00/1.18      (((k4_xboole_0 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ sk_B_1))),
% 1.00/1.18      inference('sup+', [status(thm)], ['28', '29'])).
% 1.00/1.18  thf('31', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('32', plain,
% 1.00/1.18      (![X46 : $i, X47 : $i]:
% 1.00/1.18         (((k3_subset_1 @ X46 @ X47) = (k4_xboole_0 @ X46 @ X47))
% 1.00/1.18          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X46)))),
% 1.00/1.18      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.00/1.18  thf('33', plain,
% 1.00/1.18      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 1.00/1.18      inference('sup-', [status(thm)], ['31', '32'])).
% 1.00/1.18  thf('34', plain,
% 1.00/1.18      (((k3_subset_1 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ sk_B_1))),
% 1.00/1.18      inference('sup+', [status(thm)], ['30', '33'])).
% 1.00/1.18  thf('35', plain,
% 1.00/1.18      ((~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ 
% 1.00/1.18           (k5_xboole_0 @ sk_A @ sk_B_1)))
% 1.00/1.18         <= (~
% 1.00/1.18             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.00/1.18               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 1.00/1.18      inference('demod', [status(thm)], ['1', '19', '34'])).
% 1.00/1.18  thf('36', plain,
% 1.00/1.18      (~
% 1.00/1.18       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.00/1.18         (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 1.00/1.18       ~ ((r1_tarski @ sk_B_1 @ sk_C_2))),
% 1.00/1.18      inference('split', [status(esa)], ['0'])).
% 1.00/1.18  thf('37', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 1.00/1.18      inference('sup-', [status(thm)], ['24', '25'])).
% 1.00/1.18  thf('38', plain,
% 1.00/1.18      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 1.00/1.18      inference('sup-', [status(thm)], ['31', '32'])).
% 1.00/1.18  thf(t79_xboole_1, axiom,
% 1.00/1.18    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.00/1.18  thf('39', plain,
% 1.00/1.18      (![X31 : $i, X32 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X31 @ X32) @ X32)),
% 1.00/1.18      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.00/1.18  thf('40', plain, ((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 1.00/1.18      inference('sup+', [status(thm)], ['38', '39'])).
% 1.00/1.18  thf('41', plain,
% 1.00/1.18      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.00/1.18         (k3_subset_1 @ sk_A @ sk_B_1))
% 1.00/1.18        | (r1_tarski @ sk_B_1 @ sk_C_2))),
% 1.00/1.18      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.00/1.18  thf('42', plain,
% 1.00/1.18      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.00/1.18         (k3_subset_1 @ sk_A @ sk_B_1)))
% 1.00/1.18         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.00/1.18               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 1.00/1.18      inference('split', [status(esa)], ['41'])).
% 1.00/1.18  thf(t63_xboole_1, axiom,
% 1.00/1.18    (![A:$i,B:$i,C:$i]:
% 1.00/1.18     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 1.00/1.18       ( r1_xboole_0 @ A @ C ) ))).
% 1.00/1.18  thf('43', plain,
% 1.00/1.18      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.00/1.18         (~ (r1_tarski @ X28 @ X29)
% 1.00/1.18          | ~ (r1_xboole_0 @ X29 @ X30)
% 1.00/1.18          | (r1_xboole_0 @ X28 @ X30))),
% 1.00/1.18      inference('cnf', [status(esa)], [t63_xboole_1])).
% 1.00/1.18  thf('44', plain,
% 1.00/1.18      ((![X0 : $i]:
% 1.00/1.18          ((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_2) @ X0)
% 1.00/1.18           | ~ (r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B_1) @ X0)))
% 1.00/1.18         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.00/1.18               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['42', '43'])).
% 1.00/1.18  thf('45', plain,
% 1.00/1.18      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_2) @ sk_B_1))
% 1.00/1.18         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.00/1.18               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['40', '44'])).
% 1.00/1.18  thf('46', plain,
% 1.00/1.18      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.00/1.18      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.00/1.18  thf(t4_xboole_0, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.00/1.18            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.00/1.18       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.00/1.18            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.00/1.18  thf('47', plain,
% 1.00/1.18      (![X4 : $i, X5 : $i]:
% 1.00/1.18         ((r1_xboole_0 @ X4 @ X5)
% 1.00/1.18          | (r2_hidden @ (sk_C @ X5 @ X4) @ (k3_xboole_0 @ X4 @ X5)))),
% 1.00/1.18      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.00/1.18  thf('48', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.00/1.18          | (r1_xboole_0 @ X0 @ X1))),
% 1.00/1.18      inference('sup+', [status(thm)], ['46', '47'])).
% 1.00/1.18  thf('49', plain,
% 1.00/1.18      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.00/1.18         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 1.00/1.18          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.00/1.18      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.00/1.18  thf('50', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['48', '49'])).
% 1.00/1.18  thf('51', plain,
% 1.00/1.18      (((r1_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C_2)))
% 1.00/1.18         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.00/1.18               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['45', '50'])).
% 1.00/1.18  thf(t86_xboole_1, axiom,
% 1.00/1.18    (![A:$i,B:$i,C:$i]:
% 1.00/1.18     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 1.00/1.18       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 1.00/1.18  thf('52', plain,
% 1.00/1.18      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.00/1.18         (~ (r1_tarski @ X33 @ X34)
% 1.00/1.18          | ~ (r1_xboole_0 @ X33 @ X35)
% 1.00/1.18          | (r1_tarski @ X33 @ (k4_xboole_0 @ X34 @ X35)))),
% 1.00/1.18      inference('cnf', [status(esa)], [t86_xboole_1])).
% 1.00/1.18  thf('53', plain,
% 1.00/1.18      ((![X0 : $i]:
% 1.00/1.18          ((r1_tarski @ sk_B_1 @ 
% 1.00/1.18            (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_2)))
% 1.00/1.18           | ~ (r1_tarski @ sk_B_1 @ X0)))
% 1.00/1.18         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.00/1.18               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['51', '52'])).
% 1.00/1.18  thf('54', plain,
% 1.00/1.18      (((k3_subset_1 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ sk_C_2))),
% 1.00/1.18      inference('sup+', [status(thm)], ['15', '18'])).
% 1.00/1.18  thf('55', plain,
% 1.00/1.18      ((![X0 : $i]:
% 1.00/1.18          ((r1_tarski @ sk_B_1 @ 
% 1.00/1.18            (k4_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_C_2)))
% 1.00/1.18           | ~ (r1_tarski @ sk_B_1 @ X0)))
% 1.00/1.18         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.00/1.18               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 1.00/1.18      inference('demod', [status(thm)], ['53', '54'])).
% 1.00/1.18  thf('56', plain,
% 1.00/1.18      (((r1_tarski @ sk_B_1 @ 
% 1.00/1.18         (k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_2))))
% 1.00/1.18         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.00/1.18               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 1.00/1.18      inference('sup-', [status(thm)], ['37', '55'])).
% 1.00/1.18  thf('57', plain,
% 1.00/1.18      (((k4_xboole_0 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ sk_C_2))),
% 1.00/1.18      inference('sup+', [status(thm)], ['11', '14'])).
% 1.00/1.18  thf(t48_xboole_1, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.00/1.18  thf('58', plain,
% 1.00/1.18      (![X25 : $i, X26 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 1.00/1.18           = (k3_xboole_0 @ X25 @ X26))),
% 1.00/1.18      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.00/1.18  thf('59', plain,
% 1.00/1.18      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_2))
% 1.00/1.18         = (k3_xboole_0 @ sk_A @ sk_C_2))),
% 1.00/1.18      inference('sup+', [status(thm)], ['57', '58'])).
% 1.00/1.18  thf('60', plain,
% 1.00/1.18      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.00/1.18      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.00/1.18  thf('61', plain, (((k3_xboole_0 @ sk_C_2 @ sk_A) = (sk_C_2))),
% 1.00/1.18      inference('sup-', [status(thm)], ['9', '10'])).
% 1.00/1.18  thf('62', plain,
% 1.00/1.18      (((k4_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_A @ sk_C_2)) = (sk_C_2))),
% 1.00/1.18      inference('demod', [status(thm)], ['59', '60', '61'])).
% 1.00/1.18  thf('63', plain,
% 1.00/1.18      (((r1_tarski @ sk_B_1 @ sk_C_2))
% 1.00/1.18         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.00/1.18               (k3_subset_1 @ sk_A @ sk_B_1))))),
% 1.00/1.18      inference('demod', [status(thm)], ['56', '62'])).
% 1.00/1.18  thf('64', plain,
% 1.00/1.18      ((~ (r1_tarski @ sk_B_1 @ sk_C_2)) <= (~ ((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 1.00/1.18      inference('split', [status(esa)], ['0'])).
% 1.00/1.18  thf('65', plain,
% 1.00/1.18      (((r1_tarski @ sk_B_1 @ sk_C_2)) | 
% 1.00/1.18       ~
% 1.00/1.18       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.00/1.18         (k3_subset_1 @ sk_A @ sk_B_1)))),
% 1.00/1.18      inference('sup-', [status(thm)], ['63', '64'])).
% 1.00/1.18  thf('66', plain,
% 1.00/1.18      (~
% 1.00/1.18       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.00/1.18         (k3_subset_1 @ sk_A @ sk_B_1)))),
% 1.00/1.18      inference('sat_resolution*', [status(thm)], ['36', '65'])).
% 1.00/1.18  thf('67', plain,
% 1.00/1.18      (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ 
% 1.00/1.18          (k5_xboole_0 @ sk_A @ sk_B_1))),
% 1.00/1.18      inference('simpl_trail', [status(thm)], ['35', '66'])).
% 1.00/1.18  thf('68', plain, (((k3_xboole_0 @ sk_C_2 @ sk_A) = (sk_C_2))),
% 1.00/1.18      inference('sup-', [status(thm)], ['9', '10'])).
% 1.00/1.18  thf('69', plain,
% 1.00/1.18      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.00/1.18      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.00/1.18  thf(d10_xboole_0, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.00/1.18  thf('70', plain,
% 1.00/1.18      (![X9 : $i, X10 : $i]: ((r1_tarski @ X9 @ X10) | ((X9) != (X10)))),
% 1.00/1.18      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.00/1.18  thf('71', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 1.00/1.18      inference('simplify', [status(thm)], ['70'])).
% 1.00/1.18  thf(t108_xboole_1, axiom,
% 1.00/1.18    (![A:$i,B:$i,C:$i]:
% 1.00/1.18     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k3_xboole_0 @ A @ C ) @ B ) ))).
% 1.00/1.18  thf('72', plain,
% 1.00/1.18      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.00/1.18         (~ (r1_tarski @ X14 @ X15)
% 1.00/1.18          | (r1_tarski @ (k3_xboole_0 @ X14 @ X16) @ X15))),
% 1.00/1.18      inference('cnf', [status(esa)], [t108_xboole_1])).
% 1.00/1.18  thf('73', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 1.00/1.18      inference('sup-', [status(thm)], ['71', '72'])).
% 1.00/1.18  thf('74', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.00/1.18      inference('sup+', [status(thm)], ['69', '73'])).
% 1.00/1.18  thf('75', plain,
% 1.00/1.18      (![X18 : $i, X19 : $i]:
% 1.00/1.18         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 1.00/1.18      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.00/1.18  thf('76', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 1.00/1.18           = (k3_xboole_0 @ X1 @ X0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['74', '75'])).
% 1.00/1.18  thf('77', plain,
% 1.00/1.18      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.00/1.18      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.00/1.18  thf('78', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 1.00/1.18           = (k3_xboole_0 @ X1 @ X0))),
% 1.00/1.18      inference('demod', [status(thm)], ['76', '77'])).
% 1.00/1.18  thf('79', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ X0 @ X1)
% 1.00/1.18           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.00/1.18      inference('sup+', [status(thm)], ['12', '13'])).
% 1.00/1.18  thf('80', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 1.00/1.18           = (k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.00/1.18      inference('sup+', [status(thm)], ['78', '79'])).
% 1.00/1.18  thf('81', plain,
% 1.00/1.18      (![X25 : $i, X26 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 1.00/1.18           = (k3_xboole_0 @ X25 @ X26))),
% 1.00/1.18      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.00/1.18  thf(t4_boole, axiom,
% 1.00/1.18    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.00/1.18  thf('82', plain,
% 1.00/1.18      (![X27 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X27) = (k1_xboole_0))),
% 1.00/1.18      inference('cnf', [status(esa)], [t4_boole])).
% 1.00/1.18  thf('83', plain,
% 1.00/1.18      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.00/1.18      inference('sup+', [status(thm)], ['81', '82'])).
% 1.00/1.18  thf('84', plain,
% 1.00/1.18      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.00/1.18      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.00/1.18  thf('85', plain,
% 1.00/1.18      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.00/1.18      inference('sup+', [status(thm)], ['83', '84'])).
% 1.00/1.18  thf('86', plain,
% 1.00/1.18      (![X12 : $i, X13 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ X12 @ X13)
% 1.00/1.18           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.00/1.18      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.00/1.18  thf('87', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.00/1.18      inference('sup+', [status(thm)], ['85', '86'])).
% 1.00/1.18  thf('88', plain,
% 1.00/1.18      (![X27 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X27) = (k1_xboole_0))),
% 1.00/1.18      inference('cnf', [status(esa)], [t4_boole])).
% 1.00/1.18  thf(t98_xboole_1, axiom,
% 1.00/1.18    (![A:$i,B:$i]:
% 1.00/1.18     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 1.00/1.18  thf('89', plain,
% 1.00/1.18      (![X36 : $i, X37 : $i]:
% 1.00/1.18         ((k2_xboole_0 @ X36 @ X37)
% 1.00/1.18           = (k5_xboole_0 @ X36 @ (k4_xboole_0 @ X37 @ X36)))),
% 1.00/1.18      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.00/1.18  thf('90', plain,
% 1.00/1.18      (![X0 : $i]:
% 1.00/1.18         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.00/1.18      inference('sup+', [status(thm)], ['88', '89'])).
% 1.00/1.18  thf(t1_boole, axiom,
% 1.00/1.18    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.00/1.18  thf('91', plain, (![X17 : $i]: ((k2_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 1.00/1.18      inference('cnf', [status(esa)], [t1_boole])).
% 1.00/1.18  thf('92', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.00/1.18      inference('sup+', [status(thm)], ['90', '91'])).
% 1.00/1.18  thf('93', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.00/1.18      inference('demod', [status(thm)], ['87', '92'])).
% 1.00/1.18  thf('94', plain,
% 1.00/1.18      (![X25 : $i, X26 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ X25 @ (k4_xboole_0 @ X25 @ X26))
% 1.00/1.18           = (k3_xboole_0 @ X25 @ X26))),
% 1.00/1.18      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.00/1.18  thf('95', plain,
% 1.00/1.18      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.00/1.18      inference('sup+', [status(thm)], ['93', '94'])).
% 1.00/1.18  thf('96', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 1.00/1.18      inference('simplify', [status(thm)], ['70'])).
% 1.00/1.18  thf('97', plain,
% 1.00/1.18      (![X18 : $i, X19 : $i]:
% 1.00/1.18         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 1.00/1.18      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.00/1.18  thf('98', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.00/1.18      inference('sup-', [status(thm)], ['96', '97'])).
% 1.00/1.18  thf('99', plain,
% 1.00/1.18      (![X12 : $i, X13 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ X12 @ X13)
% 1.00/1.18           = (k5_xboole_0 @ X12 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.00/1.18      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.00/1.18  thf('100', plain,
% 1.00/1.18      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.00/1.18      inference('sup+', [status(thm)], ['98', '99'])).
% 1.00/1.18  thf('101', plain,
% 1.00/1.18      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.00/1.18      inference('sup+', [status(thm)], ['83', '84'])).
% 1.00/1.18  thf('102', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.00/1.18      inference('demod', [status(thm)], ['95', '100', '101'])).
% 1.00/1.18  thf('103', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 1.00/1.18      inference('demod', [status(thm)], ['80', '102'])).
% 1.00/1.18  thf('104', plain, (((k4_xboole_0 @ sk_C_2 @ sk_A) = (k1_xboole_0))),
% 1.00/1.18      inference('sup+', [status(thm)], ['68', '103'])).
% 1.00/1.18  thf('105', plain,
% 1.00/1.18      (![X36 : $i, X37 : $i]:
% 1.00/1.18         ((k2_xboole_0 @ X36 @ X37)
% 1.00/1.18           = (k5_xboole_0 @ X36 @ (k4_xboole_0 @ X37 @ X36)))),
% 1.00/1.18      inference('cnf', [status(esa)], [t98_xboole_1])).
% 1.00/1.18  thf('106', plain,
% 1.00/1.18      (((k2_xboole_0 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 1.00/1.18      inference('sup+', [status(thm)], ['104', '105'])).
% 1.00/1.18  thf(commutativity_k2_xboole_0, axiom,
% 1.00/1.18    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.00/1.18  thf('107', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.00/1.18      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.00/1.18  thf('108', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.00/1.18      inference('sup+', [status(thm)], ['90', '91'])).
% 1.00/1.18  thf('109', plain, (((k2_xboole_0 @ sk_C_2 @ sk_A) = (sk_A))),
% 1.00/1.18      inference('demod', [status(thm)], ['106', '107', '108'])).
% 1.00/1.18  thf('110', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 1.00/1.18      inference('simplify', [status(thm)], ['70'])).
% 1.00/1.18  thf(t43_xboole_1, axiom,
% 1.00/1.18    (![A:$i,B:$i,C:$i]:
% 1.00/1.18     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.00/1.18       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.00/1.18  thf('111', plain,
% 1.00/1.18      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.00/1.18         ((r1_tarski @ (k4_xboole_0 @ X22 @ X23) @ X24)
% 1.00/1.18          | ~ (r1_tarski @ X22 @ (k2_xboole_0 @ X23 @ X24)))),
% 1.00/1.18      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.00/1.18  thf('112', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 1.00/1.18      inference('sup-', [status(thm)], ['110', '111'])).
% 1.00/1.18  thf('113', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_2) @ sk_A)),
% 1.00/1.18      inference('sup+', [status(thm)], ['109', '112'])).
% 1.00/1.18  thf('114', plain,
% 1.00/1.18      (((k3_subset_1 @ sk_A @ sk_C_2) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 1.00/1.18      inference('sup-', [status(thm)], ['16', '17'])).
% 1.00/1.18  thf('115', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ sk_A)),
% 1.00/1.18      inference('demod', [status(thm)], ['113', '114'])).
% 1.00/1.18  thf('116', plain,
% 1.00/1.18      (((k3_subset_1 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ sk_C_2))),
% 1.00/1.18      inference('sup+', [status(thm)], ['15', '18'])).
% 1.00/1.18  thf('117', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ sk_A)),
% 1.00/1.18      inference('demod', [status(thm)], ['115', '116'])).
% 1.00/1.18  thf('118', plain,
% 1.00/1.18      (((k3_subset_1 @ sk_A @ sk_C_2) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 1.00/1.18      inference('sup-', [status(thm)], ['16', '17'])).
% 1.00/1.18  thf('119', plain,
% 1.00/1.18      (![X31 : $i, X32 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X31 @ X32) @ X32)),
% 1.00/1.18      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.00/1.18  thf('120', plain,
% 1.00/1.18      (![X0 : $i, X1 : $i]:
% 1.00/1.18         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.00/1.19      inference('sup-', [status(thm)], ['48', '49'])).
% 1.00/1.19  thf('121', plain,
% 1.00/1.19      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 1.00/1.19      inference('sup-', [status(thm)], ['119', '120'])).
% 1.00/1.19  thf('122', plain,
% 1.00/1.19      (((r1_tarski @ sk_B_1 @ sk_C_2)) <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 1.00/1.19      inference('split', [status(esa)], ['41'])).
% 1.00/1.19  thf('123', plain,
% 1.00/1.19      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.00/1.19         (~ (r1_tarski @ X28 @ X29)
% 1.00/1.19          | ~ (r1_xboole_0 @ X29 @ X30)
% 1.00/1.19          | (r1_xboole_0 @ X28 @ X30))),
% 1.00/1.19      inference('cnf', [status(esa)], [t63_xboole_1])).
% 1.00/1.19  thf('124', plain,
% 1.00/1.19      ((![X0 : $i]:
% 1.00/1.19          ((r1_xboole_0 @ sk_B_1 @ X0) | ~ (r1_xboole_0 @ sk_C_2 @ X0)))
% 1.00/1.19         <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 1.00/1.19      inference('sup-', [status(thm)], ['122', '123'])).
% 1.00/1.19  thf('125', plain,
% 1.00/1.19      ((![X0 : $i]: (r1_xboole_0 @ sk_B_1 @ (k4_xboole_0 @ X0 @ sk_C_2)))
% 1.00/1.19         <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 1.00/1.19      inference('sup-', [status(thm)], ['121', '124'])).
% 1.00/1.19  thf('126', plain,
% 1.00/1.19      (![X0 : $i, X1 : $i]:
% 1.00/1.19         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.00/1.19      inference('sup-', [status(thm)], ['48', '49'])).
% 1.00/1.19  thf('127', plain,
% 1.00/1.19      ((![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_2) @ sk_B_1))
% 1.00/1.19         <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 1.00/1.19      inference('sup-', [status(thm)], ['125', '126'])).
% 1.00/1.19  thf('128', plain,
% 1.00/1.19      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_2) @ sk_B_1))
% 1.00/1.19         <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 1.00/1.19      inference('sup+', [status(thm)], ['118', '127'])).
% 1.00/1.19  thf('129', plain,
% 1.00/1.19      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.00/1.19         (~ (r1_tarski @ X33 @ X34)
% 1.00/1.19          | ~ (r1_xboole_0 @ X33 @ X35)
% 1.00/1.19          | (r1_tarski @ X33 @ (k4_xboole_0 @ X34 @ X35)))),
% 1.00/1.19      inference('cnf', [status(esa)], [t86_xboole_1])).
% 1.00/1.19  thf('130', plain,
% 1.00/1.19      ((![X0 : $i]:
% 1.00/1.19          ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.00/1.19            (k4_xboole_0 @ X0 @ sk_B_1))
% 1.00/1.19           | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ X0)))
% 1.00/1.19         <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 1.00/1.19      inference('sup-', [status(thm)], ['128', '129'])).
% 1.00/1.19  thf('131', plain,
% 1.00/1.19      (((k3_subset_1 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ sk_C_2))),
% 1.00/1.19      inference('sup+', [status(thm)], ['15', '18'])).
% 1.00/1.19  thf('132', plain,
% 1.00/1.19      (((k3_subset_1 @ sk_A @ sk_C_2) = (k5_xboole_0 @ sk_A @ sk_C_2))),
% 1.00/1.19      inference('sup+', [status(thm)], ['15', '18'])).
% 1.00/1.19  thf('133', plain,
% 1.00/1.19      ((![X0 : $i]:
% 1.00/1.19          ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ 
% 1.00/1.19            (k4_xboole_0 @ X0 @ sk_B_1))
% 1.00/1.19           | ~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ X0)))
% 1.00/1.19         <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 1.00/1.19      inference('demod', [status(thm)], ['130', '131', '132'])).
% 1.00/1.19  thf('134', plain,
% 1.00/1.19      (((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ 
% 1.00/1.19         (k4_xboole_0 @ sk_A @ sk_B_1))) <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 1.00/1.19      inference('sup-', [status(thm)], ['117', '133'])).
% 1.00/1.19  thf('135', plain,
% 1.00/1.19      (((k4_xboole_0 @ sk_A @ sk_B_1) = (k5_xboole_0 @ sk_A @ sk_B_1))),
% 1.00/1.19      inference('sup+', [status(thm)], ['28', '29'])).
% 1.00/1.19  thf('136', plain,
% 1.00/1.19      (((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ 
% 1.00/1.19         (k5_xboole_0 @ sk_A @ sk_B_1))) <= (((r1_tarski @ sk_B_1 @ sk_C_2)))),
% 1.00/1.19      inference('demod', [status(thm)], ['134', '135'])).
% 1.00/1.19  thf('137', plain,
% 1.00/1.19      (((r1_tarski @ sk_B_1 @ sk_C_2)) | 
% 1.00/1.19       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_2) @ 
% 1.00/1.19         (k3_subset_1 @ sk_A @ sk_B_1)))),
% 1.00/1.19      inference('split', [status(esa)], ['41'])).
% 1.00/1.19  thf('138', plain, (((r1_tarski @ sk_B_1 @ sk_C_2))),
% 1.00/1.19      inference('sat_resolution*', [status(thm)], ['36', '65', '137'])).
% 1.00/1.19  thf('139', plain,
% 1.00/1.19      ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_2) @ 
% 1.00/1.19        (k5_xboole_0 @ sk_A @ sk_B_1))),
% 1.00/1.19      inference('simpl_trail', [status(thm)], ['136', '138'])).
% 1.00/1.19  thf('140', plain, ($false), inference('demod', [status(thm)], ['67', '139'])).
% 1.00/1.19  
% 1.00/1.19  % SZS output end Refutation
% 1.00/1.19  
% 1.00/1.19  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
