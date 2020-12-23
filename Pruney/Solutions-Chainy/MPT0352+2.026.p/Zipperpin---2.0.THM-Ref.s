%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WVF4LvGxWt

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:11 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 534 expanded)
%              Number of leaves         :   31 ( 169 expanded)
%              Depth                    :   18
%              Number of atoms          :  929 (4576 expanded)
%              Number of equality atoms :   36 ( 200 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
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
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ X50 )
      | ( r2_hidden @ X49 @ X50 )
      | ( v1_xboole_0 @ X50 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X54: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('6',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X40 @ X39 )
      | ( r1_tarski @ X40 @ X38 )
      | ( X39
       != ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('8',plain,(
    ! [X38: $i,X40: $i] :
      ( ( r1_tarski @ X40 @ X38 )
      | ~ ( r2_hidden @ X40 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k3_subset_1 @ X52 @ X53 )
        = ( k4_xboole_0 @ X52 @ X53 ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X52: $i,X53: $i] :
      ( ( ( k3_subset_1 @ X52 @ X53 )
        = ( k4_xboole_0 @ X52 @ X53 ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('22',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ X50 )
      | ( r2_hidden @ X49 @ X50 )
      | ( v1_xboole_0 @ X50 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X54: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('27',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X38: $i,X40: $i] :
      ( ( r1_tarski @ X40 @ X38 )
      | ~ ( r2_hidden @ X40 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('29',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('33',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['22','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['1','19','34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('39',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('40',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X27 @ X28 ) @ X28 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('43',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ X34 @ X35 )
      | ~ ( r1_xboole_0 @ X34 @ X36 )
      | ( r1_tarski @ X34 @ ( k4_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('46',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('47',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,
    ( sk_B
    = ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['37','49'])).

thf('51',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['51'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('53',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X31 @ X32 )
      | ( r1_xboole_0 @ X31 @ ( k4_xboole_0 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('54',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('56',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['22','33'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( r1_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['50','57'])).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('60',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('62',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('63',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('67',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('70',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r1_tarski @ X24 @ X25 )
      | ~ ( r1_tarski @ X24 @ ( k2_xboole_0 @ X25 @ X26 ) )
      | ~ ( r1_xboole_0 @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('71',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','71'])).

thf('73',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('74',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['36','74'])).

thf('76',plain,(
    ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['35','75'])).

thf('77',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('78',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('79',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('81',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['51'])).

thf('82',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ X31 @ X32 )
      | ( r1_xboole_0 @ X31 @ ( k4_xboole_0 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('83',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('85',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_B )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ X34 @ X35 )
      | ~ ( r1_xboole_0 @ X34 @ X36 )
      | ( r1_tarski @ X34 @ ( k4_xboole_0 @ X35 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('87',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ ( k4_xboole_0 @ X1 @ sk_B ) )
        | ~ ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ X1 ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ X0 )
        | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['80','87'])).

thf('89',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ X0 )
        | ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['51'])).

thf('92',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['36','74','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ X0 )
      | ( r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['90','92'])).

thf('94',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['79','93'])).

thf('95',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('96',plain,(
    r1_tarski @ ( k5_xboole_0 @ sk_A @ sk_C_1 ) @ ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    $false ),
    inference(demod,[status(thm)],['76','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WVF4LvGxWt
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:34:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.04/2.25  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.04/2.25  % Solved by: fo/fo7.sh
% 2.04/2.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.04/2.25  % done 4810 iterations in 1.796s
% 2.04/2.25  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.04/2.25  % SZS output start Refutation
% 2.04/2.25  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.04/2.25  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.04/2.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.04/2.25  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.04/2.25  thf(sk_B_type, type, sk_B: $i).
% 2.04/2.25  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.04/2.25  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.04/2.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.04/2.25  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.04/2.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.04/2.25  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.04/2.25  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.04/2.25  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.04/2.25  thf(sk_A_type, type, sk_A: $i).
% 2.04/2.25  thf(t31_subset_1, conjecture,
% 2.04/2.25    (![A:$i,B:$i]:
% 2.04/2.25     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.04/2.25       ( ![C:$i]:
% 2.04/2.25         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.04/2.25           ( ( r1_tarski @ B @ C ) <=>
% 2.04/2.25             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 2.04/2.25  thf(zf_stmt_0, negated_conjecture,
% 2.04/2.25    (~( ![A:$i,B:$i]:
% 2.04/2.25        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.04/2.25          ( ![C:$i]:
% 2.04/2.25            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.04/2.25              ( ( r1_tarski @ B @ C ) <=>
% 2.04/2.25                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 2.04/2.25    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 2.04/2.25  thf('0', plain,
% 2.04/2.25      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.04/2.25           (k3_subset_1 @ sk_A @ sk_B))
% 2.04/2.25        | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('1', plain,
% 2.04/2.25      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.04/2.25           (k3_subset_1 @ sk_A @ sk_B)))
% 2.04/2.25         <= (~
% 2.04/2.25             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.04/2.25               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.04/2.25      inference('split', [status(esa)], ['0'])).
% 2.04/2.25  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf(d2_subset_1, axiom,
% 2.04/2.25    (![A:$i,B:$i]:
% 2.04/2.25     ( ( ( v1_xboole_0 @ A ) =>
% 2.04/2.25         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 2.04/2.25       ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.04/2.25         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 2.04/2.25  thf('3', plain,
% 2.04/2.25      (![X49 : $i, X50 : $i]:
% 2.04/2.25         (~ (m1_subset_1 @ X49 @ X50)
% 2.04/2.25          | (r2_hidden @ X49 @ X50)
% 2.04/2.25          | (v1_xboole_0 @ X50))),
% 2.04/2.25      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.04/2.25  thf('4', plain,
% 2.04/2.25      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 2.04/2.25        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['2', '3'])).
% 2.04/2.25  thf(fc1_subset_1, axiom,
% 2.04/2.25    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.04/2.25  thf('5', plain, (![X54 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X54))),
% 2.04/2.25      inference('cnf', [status(esa)], [fc1_subset_1])).
% 2.04/2.25  thf('6', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 2.04/2.25      inference('clc', [status(thm)], ['4', '5'])).
% 2.04/2.25  thf(d1_zfmisc_1, axiom,
% 2.04/2.25    (![A:$i,B:$i]:
% 2.04/2.25     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 2.04/2.25       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 2.04/2.25  thf('7', plain,
% 2.04/2.25      (![X38 : $i, X39 : $i, X40 : $i]:
% 2.04/2.25         (~ (r2_hidden @ X40 @ X39)
% 2.04/2.25          | (r1_tarski @ X40 @ X38)
% 2.04/2.25          | ((X39) != (k1_zfmisc_1 @ X38)))),
% 2.04/2.25      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 2.04/2.25  thf('8', plain,
% 2.04/2.25      (![X38 : $i, X40 : $i]:
% 2.04/2.25         ((r1_tarski @ X40 @ X38) | ~ (r2_hidden @ X40 @ (k1_zfmisc_1 @ X38)))),
% 2.04/2.25      inference('simplify', [status(thm)], ['7'])).
% 2.04/2.25  thf('9', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 2.04/2.25      inference('sup-', [status(thm)], ['6', '8'])).
% 2.04/2.25  thf(t28_xboole_1, axiom,
% 2.04/2.25    (![A:$i,B:$i]:
% 2.04/2.25     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.04/2.25  thf('10', plain,
% 2.04/2.25      (![X17 : $i, X18 : $i]:
% 2.04/2.25         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 2.04/2.25      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.04/2.25  thf('11', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 2.04/2.25      inference('sup-', [status(thm)], ['9', '10'])).
% 2.04/2.25  thf(commutativity_k3_xboole_0, axiom,
% 2.04/2.25    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.04/2.25  thf('12', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.04/2.25      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.04/2.25  thf(t100_xboole_1, axiom,
% 2.04/2.25    (![A:$i,B:$i]:
% 2.04/2.25     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.04/2.25  thf('13', plain,
% 2.04/2.25      (![X7 : $i, X8 : $i]:
% 2.04/2.25         ((k4_xboole_0 @ X7 @ X8)
% 2.04/2.25           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 2.04/2.25      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.04/2.25  thf('14', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         ((k4_xboole_0 @ X0 @ X1)
% 2.04/2.25           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.04/2.25      inference('sup+', [status(thm)], ['12', '13'])).
% 2.04/2.25  thf('15', plain,
% 2.04/2.25      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 2.04/2.25      inference('sup+', [status(thm)], ['11', '14'])).
% 2.04/2.25  thf('16', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf(d5_subset_1, axiom,
% 2.04/2.25    (![A:$i,B:$i]:
% 2.04/2.25     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.04/2.25       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 2.04/2.25  thf('17', plain,
% 2.04/2.25      (![X52 : $i, X53 : $i]:
% 2.04/2.25         (((k3_subset_1 @ X52 @ X53) = (k4_xboole_0 @ X52 @ X53))
% 2.04/2.25          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ X52)))),
% 2.04/2.25      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.04/2.25  thf('18', plain,
% 2.04/2.25      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 2.04/2.25      inference('sup-', [status(thm)], ['16', '17'])).
% 2.04/2.25  thf('19', plain,
% 2.04/2.25      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 2.04/2.25      inference('sup+', [status(thm)], ['15', '18'])).
% 2.04/2.25  thf('20', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('21', plain,
% 2.04/2.25      (![X52 : $i, X53 : $i]:
% 2.04/2.25         (((k3_subset_1 @ X52 @ X53) = (k4_xboole_0 @ X52 @ X53))
% 2.04/2.25          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ X52)))),
% 2.04/2.25      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.04/2.25  thf('22', plain,
% 2.04/2.25      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 2.04/2.25      inference('sup-', [status(thm)], ['20', '21'])).
% 2.04/2.25  thf('23', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('24', plain,
% 2.04/2.25      (![X49 : $i, X50 : $i]:
% 2.04/2.25         (~ (m1_subset_1 @ X49 @ X50)
% 2.04/2.25          | (r2_hidden @ X49 @ X50)
% 2.04/2.25          | (v1_xboole_0 @ X50))),
% 2.04/2.25      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.04/2.25  thf('25', plain,
% 2.04/2.25      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 2.04/2.25        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['23', '24'])).
% 2.04/2.25  thf('26', plain, (![X54 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X54))),
% 2.04/2.25      inference('cnf', [status(esa)], [fc1_subset_1])).
% 2.04/2.25  thf('27', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 2.04/2.25      inference('clc', [status(thm)], ['25', '26'])).
% 2.04/2.25  thf('28', plain,
% 2.04/2.25      (![X38 : $i, X40 : $i]:
% 2.04/2.25         ((r1_tarski @ X40 @ X38) | ~ (r2_hidden @ X40 @ (k1_zfmisc_1 @ X38)))),
% 2.04/2.25      inference('simplify', [status(thm)], ['7'])).
% 2.04/2.25  thf('29', plain, ((r1_tarski @ sk_B @ sk_A)),
% 2.04/2.25      inference('sup-', [status(thm)], ['27', '28'])).
% 2.04/2.25  thf('30', plain,
% 2.04/2.25      (![X17 : $i, X18 : $i]:
% 2.04/2.25         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 2.04/2.25      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.04/2.25  thf('31', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 2.04/2.25      inference('sup-', [status(thm)], ['29', '30'])).
% 2.04/2.25  thf('32', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         ((k4_xboole_0 @ X0 @ X1)
% 2.04/2.25           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.04/2.25      inference('sup+', [status(thm)], ['12', '13'])).
% 2.04/2.25  thf('33', plain,
% 2.04/2.25      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 2.04/2.25      inference('sup+', [status(thm)], ['31', '32'])).
% 2.04/2.25  thf('34', plain,
% 2.04/2.25      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 2.04/2.25      inference('sup+', [status(thm)], ['22', '33'])).
% 2.04/2.25  thf('35', plain,
% 2.04/2.25      ((~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 2.04/2.25           (k5_xboole_0 @ sk_A @ sk_B)))
% 2.04/2.25         <= (~
% 2.04/2.25             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.04/2.25               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.04/2.25      inference('demod', [status(thm)], ['1', '19', '34'])).
% 2.04/2.25  thf('36', plain,
% 2.04/2.25      (~
% 2.04/2.25       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.04/2.25         (k3_subset_1 @ sk_A @ sk_B))) | 
% 2.04/2.25       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 2.04/2.25      inference('split', [status(esa)], ['0'])).
% 2.04/2.25  thf('37', plain,
% 2.04/2.25      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 2.04/2.25      inference('sup+', [status(thm)], ['31', '32'])).
% 2.04/2.25  thf(d10_xboole_0, axiom,
% 2.04/2.25    (![A:$i,B:$i]:
% 2.04/2.25     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.04/2.25  thf('38', plain,
% 2.04/2.25      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 2.04/2.25      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.04/2.25  thf('39', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 2.04/2.25      inference('simplify', [status(thm)], ['38'])).
% 2.04/2.25  thf(t79_xboole_1, axiom,
% 2.04/2.25    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 2.04/2.25  thf('40', plain,
% 2.04/2.25      (![X27 : $i, X28 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X27 @ X28) @ X28)),
% 2.04/2.25      inference('cnf', [status(esa)], [t79_xboole_1])).
% 2.04/2.25  thf(symmetry_r1_xboole_0, axiom,
% 2.04/2.25    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.04/2.25  thf('41', plain,
% 2.04/2.25      (![X2 : $i, X3 : $i]:
% 2.04/2.25         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.04/2.25      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.04/2.25  thf('42', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 2.04/2.25      inference('sup-', [status(thm)], ['40', '41'])).
% 2.04/2.25  thf(t86_xboole_1, axiom,
% 2.04/2.25    (![A:$i,B:$i,C:$i]:
% 2.04/2.25     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 2.04/2.25       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 2.04/2.25  thf('43', plain,
% 2.04/2.25      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.04/2.25         (~ (r1_tarski @ X34 @ X35)
% 2.04/2.25          | ~ (r1_xboole_0 @ X34 @ X36)
% 2.04/2.25          | (r1_tarski @ X34 @ (k4_xboole_0 @ X35 @ X36)))),
% 2.04/2.25      inference('cnf', [status(esa)], [t86_xboole_1])).
% 2.04/2.25  thf('44', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.04/2.25         ((r1_tarski @ X0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 2.04/2.25          | ~ (r1_tarski @ X0 @ X2))),
% 2.04/2.25      inference('sup-', [status(thm)], ['42', '43'])).
% 2.04/2.25  thf('45', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['39', '44'])).
% 2.04/2.25  thf(t36_xboole_1, axiom,
% 2.04/2.25    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.04/2.25  thf('46', plain,
% 2.04/2.25      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 2.04/2.25      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.04/2.25  thf('47', plain,
% 2.04/2.25      (![X4 : $i, X6 : $i]:
% 2.04/2.25         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 2.04/2.25      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.04/2.25  thf('48', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.04/2.25          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['46', '47'])).
% 2.04/2.25  thf('49', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['45', '48'])).
% 2.04/2.25  thf('50', plain,
% 2.04/2.25      (((sk_B) = (k4_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 2.04/2.25      inference('sup+', [status(thm)], ['37', '49'])).
% 2.04/2.25  thf('51', plain,
% 2.04/2.25      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.04/2.25         (k3_subset_1 @ sk_A @ sk_B))
% 2.04/2.25        | (r1_tarski @ sk_B @ sk_C_1))),
% 2.04/2.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.25  thf('52', plain,
% 2.04/2.25      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.04/2.25         (k3_subset_1 @ sk_A @ sk_B)))
% 2.04/2.25         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.04/2.25               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.04/2.25      inference('split', [status(esa)], ['51'])).
% 2.04/2.25  thf(t85_xboole_1, axiom,
% 2.04/2.25    (![A:$i,B:$i,C:$i]:
% 2.04/2.25     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 2.04/2.25  thf('53', plain,
% 2.04/2.25      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.04/2.25         (~ (r1_tarski @ X31 @ X32)
% 2.04/2.25          | (r1_xboole_0 @ X31 @ (k4_xboole_0 @ X33 @ X32)))),
% 2.04/2.25      inference('cnf', [status(esa)], [t85_xboole_1])).
% 2.04/2.25  thf('54', plain,
% 2.04/2.25      ((![X0 : $i]:
% 2.04/2.25          (r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.04/2.25           (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_B))))
% 2.04/2.25         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.04/2.25               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.04/2.25      inference('sup-', [status(thm)], ['52', '53'])).
% 2.04/2.25  thf('55', plain,
% 2.04/2.25      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 2.04/2.25      inference('sup+', [status(thm)], ['15', '18'])).
% 2.04/2.25  thf('56', plain,
% 2.04/2.25      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 2.04/2.25      inference('sup+', [status(thm)], ['22', '33'])).
% 2.04/2.25  thf('57', plain,
% 2.04/2.25      ((![X0 : $i]:
% 2.04/2.25          (r1_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 2.04/2.25           (k4_xboole_0 @ X0 @ (k5_xboole_0 @ sk_A @ sk_B))))
% 2.04/2.25         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.04/2.25               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.04/2.25      inference('demod', [status(thm)], ['54', '55', '56'])).
% 2.04/2.25  thf('58', plain,
% 2.04/2.25      (((r1_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_C_1) @ sk_B))
% 2.04/2.25         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.04/2.25               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.04/2.25      inference('sup+', [status(thm)], ['50', '57'])).
% 2.04/2.25  thf('59', plain,
% 2.04/2.25      (![X2 : $i, X3 : $i]:
% 2.04/2.25         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.04/2.25      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.04/2.25  thf('60', plain,
% 2.04/2.25      (((r1_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_1)))
% 2.04/2.25         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.04/2.25               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.04/2.25      inference('sup-', [status(thm)], ['58', '59'])).
% 2.04/2.25  thf('61', plain,
% 2.04/2.25      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 2.04/2.25      inference('sup+', [status(thm)], ['11', '14'])).
% 2.04/2.25  thf('62', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 2.04/2.25      inference('simplify', [status(thm)], ['38'])).
% 2.04/2.25  thf(t44_xboole_1, axiom,
% 2.04/2.25    (![A:$i,B:$i,C:$i]:
% 2.04/2.25     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 2.04/2.25       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 2.04/2.25  thf('63', plain,
% 2.04/2.25      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.04/2.25         ((r1_tarski @ X21 @ (k2_xboole_0 @ X22 @ X23))
% 2.04/2.25          | ~ (r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X23))),
% 2.04/2.25      inference('cnf', [status(esa)], [t44_xboole_1])).
% 2.04/2.25  thf('64', plain,
% 2.04/2.25      (![X0 : $i, X1 : $i]:
% 2.04/2.25         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.04/2.25      inference('sup-', [status(thm)], ['62', '63'])).
% 2.04/2.25  thf('65', plain,
% 2.04/2.25      ((r1_tarski @ sk_A @ 
% 2.04/2.25        (k2_xboole_0 @ sk_C_1 @ (k5_xboole_0 @ sk_A @ sk_C_1)))),
% 2.04/2.25      inference('sup+', [status(thm)], ['61', '64'])).
% 2.04/2.25  thf('66', plain, ((r1_tarski @ sk_B @ sk_A)),
% 2.04/2.25      inference('sup-', [status(thm)], ['27', '28'])).
% 2.04/2.25  thf(t1_xboole_1, axiom,
% 2.04/2.25    (![A:$i,B:$i,C:$i]:
% 2.04/2.25     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 2.04/2.25       ( r1_tarski @ A @ C ) ))).
% 2.04/2.25  thf('67', plain,
% 2.04/2.25      (![X14 : $i, X15 : $i, X16 : $i]:
% 2.04/2.25         (~ (r1_tarski @ X14 @ X15)
% 2.04/2.25          | ~ (r1_tarski @ X15 @ X16)
% 2.04/2.25          | (r1_tarski @ X14 @ X16))),
% 2.04/2.25      inference('cnf', [status(esa)], [t1_xboole_1])).
% 2.04/2.25  thf('68', plain,
% 2.04/2.25      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 2.04/2.25      inference('sup-', [status(thm)], ['66', '67'])).
% 2.04/2.25  thf('69', plain,
% 2.04/2.26      ((r1_tarski @ sk_B @ 
% 2.04/2.26        (k2_xboole_0 @ sk_C_1 @ (k5_xboole_0 @ sk_A @ sk_C_1)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['65', '68'])).
% 2.04/2.26  thf(t73_xboole_1, axiom,
% 2.04/2.26    (![A:$i,B:$i,C:$i]:
% 2.04/2.26     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 2.04/2.26       ( r1_tarski @ A @ B ) ))).
% 2.04/2.26  thf('70', plain,
% 2.04/2.26      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.04/2.26         ((r1_tarski @ X24 @ X25)
% 2.04/2.26          | ~ (r1_tarski @ X24 @ (k2_xboole_0 @ X25 @ X26))
% 2.04/2.26          | ~ (r1_xboole_0 @ X24 @ X26))),
% 2.04/2.26      inference('cnf', [status(esa)], [t73_xboole_1])).
% 2.04/2.26  thf('71', plain,
% 2.04/2.26      ((~ (r1_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_C_1))
% 2.04/2.26        | (r1_tarski @ sk_B @ sk_C_1))),
% 2.04/2.26      inference('sup-', [status(thm)], ['69', '70'])).
% 2.04/2.26  thf('72', plain,
% 2.04/2.26      (((r1_tarski @ sk_B @ sk_C_1))
% 2.04/2.26         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.04/2.26               (k3_subset_1 @ sk_A @ sk_B))))),
% 2.04/2.26      inference('sup-', [status(thm)], ['60', '71'])).
% 2.04/2.26  thf('73', plain,
% 2.04/2.26      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 2.04/2.26      inference('split', [status(esa)], ['0'])).
% 2.04/2.26  thf('74', plain,
% 2.04/2.26      (((r1_tarski @ sk_B @ sk_C_1)) | 
% 2.04/2.26       ~
% 2.04/2.26       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.04/2.26         (k3_subset_1 @ sk_A @ sk_B)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['72', '73'])).
% 2.04/2.26  thf('75', plain,
% 2.04/2.26      (~
% 2.04/2.26       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.04/2.26         (k3_subset_1 @ sk_A @ sk_B)))),
% 2.04/2.26      inference('sat_resolution*', [status(thm)], ['36', '74'])).
% 2.04/2.26  thf('76', plain,
% 2.04/2.26      (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 2.04/2.26          (k5_xboole_0 @ sk_A @ sk_B))),
% 2.04/2.26      inference('simpl_trail', [status(thm)], ['35', '75'])).
% 2.04/2.26  thf('77', plain,
% 2.04/2.26      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 2.04/2.26      inference('sup+', [status(thm)], ['11', '14'])).
% 2.04/2.26  thf('78', plain,
% 2.04/2.26      (![X19 : $i, X20 : $i]: (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X19)),
% 2.04/2.26      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.04/2.26  thf('79', plain, ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ sk_A)),
% 2.04/2.26      inference('sup+', [status(thm)], ['77', '78'])).
% 2.04/2.26  thf('80', plain,
% 2.04/2.26      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 2.04/2.26      inference('sup+', [status(thm)], ['11', '14'])).
% 2.04/2.26  thf('81', plain,
% 2.04/2.26      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 2.04/2.26      inference('split', [status(esa)], ['51'])).
% 2.04/2.26  thf('82', plain,
% 2.04/2.26      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.04/2.26         (~ (r1_tarski @ X31 @ X32)
% 2.04/2.26          | (r1_xboole_0 @ X31 @ (k4_xboole_0 @ X33 @ X32)))),
% 2.04/2.26      inference('cnf', [status(esa)], [t85_xboole_1])).
% 2.04/2.26  thf('83', plain,
% 2.04/2.26      ((![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1)))
% 2.04/2.26         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['81', '82'])).
% 2.04/2.26  thf('84', plain,
% 2.04/2.26      (![X2 : $i, X3 : $i]:
% 2.04/2.26         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 2.04/2.26      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.04/2.26  thf('85', plain,
% 2.04/2.26      ((![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_B))
% 2.04/2.26         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['83', '84'])).
% 2.04/2.26  thf('86', plain,
% 2.04/2.26      (![X34 : $i, X35 : $i, X36 : $i]:
% 2.04/2.26         (~ (r1_tarski @ X34 @ X35)
% 2.04/2.26          | ~ (r1_xboole_0 @ X34 @ X36)
% 2.04/2.26          | (r1_tarski @ X34 @ (k4_xboole_0 @ X35 @ X36)))),
% 2.04/2.26      inference('cnf', [status(esa)], [t86_xboole_1])).
% 2.04/2.26  thf('87', plain,
% 2.04/2.26      ((![X0 : $i, X1 : $i]:
% 2.04/2.26          ((r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_1) @ (k4_xboole_0 @ X1 @ sk_B))
% 2.04/2.26           | ~ (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_1) @ X1)))
% 2.04/2.26         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['85', '86'])).
% 2.04/2.26  thf('88', plain,
% 2.04/2.26      ((![X0 : $i]:
% 2.04/2.26          (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ X0)
% 2.04/2.26           | (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_C_1) @ 
% 2.04/2.26              (k4_xboole_0 @ X0 @ sk_B))))
% 2.04/2.26         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 2.04/2.26      inference('sup-', [status(thm)], ['80', '87'])).
% 2.04/2.26  thf('89', plain,
% 2.04/2.26      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 2.04/2.26      inference('sup+', [status(thm)], ['11', '14'])).
% 2.04/2.26  thf('90', plain,
% 2.04/2.26      ((![X0 : $i]:
% 2.04/2.26          (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ X0)
% 2.04/2.26           | (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 2.04/2.26              (k4_xboole_0 @ X0 @ sk_B))))
% 2.04/2.26         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 2.04/2.26      inference('demod', [status(thm)], ['88', '89'])).
% 2.04/2.26  thf('91', plain,
% 2.04/2.26      (((r1_tarski @ sk_B @ sk_C_1)) | 
% 2.04/2.26       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 2.04/2.26         (k3_subset_1 @ sk_A @ sk_B)))),
% 2.04/2.26      inference('split', [status(esa)], ['51'])).
% 2.04/2.26  thf('92', plain, (((r1_tarski @ sk_B @ sk_C_1))),
% 2.04/2.26      inference('sat_resolution*', [status(thm)], ['36', '74', '91'])).
% 2.04/2.26  thf('93', plain,
% 2.04/2.26      (![X0 : $i]:
% 2.04/2.26         (~ (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ X0)
% 2.04/2.26          | (r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ 
% 2.04/2.26             (k4_xboole_0 @ X0 @ sk_B)))),
% 2.04/2.26      inference('simpl_trail', [status(thm)], ['90', '92'])).
% 2.04/2.26  thf('94', plain,
% 2.04/2.26      ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ (k4_xboole_0 @ sk_A @ sk_B))),
% 2.04/2.26      inference('sup-', [status(thm)], ['79', '93'])).
% 2.04/2.26  thf('95', plain,
% 2.04/2.26      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 2.04/2.26      inference('sup+', [status(thm)], ['31', '32'])).
% 2.04/2.26  thf('96', plain,
% 2.04/2.26      ((r1_tarski @ (k5_xboole_0 @ sk_A @ sk_C_1) @ (k5_xboole_0 @ sk_A @ sk_B))),
% 2.04/2.26      inference('demod', [status(thm)], ['94', '95'])).
% 2.04/2.26  thf('97', plain, ($false), inference('demod', [status(thm)], ['76', '96'])).
% 2.04/2.26  
% 2.04/2.26  % SZS output end Refutation
% 2.04/2.26  
% 2.04/2.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
