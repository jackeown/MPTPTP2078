%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.klBXpQaPTI

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:46 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 222 expanded)
%              Number of leaves         :   26 (  77 expanded)
%              Depth                    :   17
%              Number of atoms          :  703 (1726 expanded)
%              Number of equality atoms :   57 ( 122 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t40_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( ( r1_tarski @ B @ C )
          & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
       => ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
       => ( ( ( r1_tarski @ B @ C )
            & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
         => ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_subset_1])).

thf('0',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k4_xboole_0 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('3',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ~ ( r1_tarski @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_2 ) )
      | ( r1_xboole_0 @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_xboole_0 @ sk_B @ sk_C_2 ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_2 )
    = sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ sk_B @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ( r1_xboole_0 @ X18 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_2 ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['8','13'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('19',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ( r2_hidden @ X21 @ X23 )
      | ( X23
       != ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('20',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('22',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ( m1_subset_1 @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k4_xboole_0 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ X0 )
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_xboole_0 @ X28 )
      | ( m1_subset_1 @ X28 @ X27 )
      | ~ ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('27',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k4_xboole_0 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_subset_1 @ X0 @ X1 )
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_subset_1 @ X0 @ X0 )
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ X1 )
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ( ( k3_subset_1 @ sk_B @ sk_B )
      = sk_B )
    | ~ ( v1_xboole_0 @ sk_B )
    | ( ( k3_subset_1 @ sk_B @ sk_B )
      = ( k4_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['14','29'])).

thf('31',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_2 )
    = ( k4_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('33',plain,(
    r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = sk_B ),
    inference('sup+',[status(thm)],['8','13'])).

thf('39',plain,
    ( ( ( k3_subset_1 @ sk_B @ sk_B )
      = sk_B )
    | ( ( k3_subset_1 @ sk_B @ sk_B )
      = sk_B ) ),
    inference(demod,[status(thm)],['30','37','38'])).

thf('40',plain,
    ( ( k3_subset_1 @ sk_B @ sk_B )
    = sk_B ),
    inference(simplify,[status(thm)],['39'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('41',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('42',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('43',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ( m1_subset_1 @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k4_xboole_0 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_subset_1 @ X0 @ X1 )
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 )
      | ( ( k3_subset_1 @ X0 @ X1 )
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup+',[status(thm)],['41','52'])).

thf('54',plain,(
    ! [X9: $i] :
      ( r1_tarski @ k1_xboole_0 @ X9 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('55',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('56',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X14 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['53','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('64',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X32 @ ( k3_subset_1 @ X32 @ X31 ) )
        = X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( k3_subset_1 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_xboole_0 @ X28 )
      | ( m1_subset_1 @ X28 @ X27 )
      | ~ ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('69',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X32 @ ( k3_subset_1 @ X32 @ X31 ) )
        = X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X1 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_subset_1 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X1 ) )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( k3_subset_1 @ X0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k3_subset_1 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['62','71'])).

thf('73',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['54','59'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k3_subset_1 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k3_subset_1 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['40','75'])).

thf('77',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.klBXpQaPTI
% 0.15/0.38  % Computer   : n016.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 14:56:04 EST 2020
% 0.15/0.39  % CPUTime    : 
% 0.15/0.39  % Running portfolio for 600 s
% 0.15/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.39  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 1.60/1.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.60/1.81  % Solved by: fo/fo7.sh
% 1.60/1.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.60/1.81  % done 2848 iterations in 1.318s
% 1.60/1.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.60/1.81  % SZS output start Refutation
% 1.60/1.81  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.60/1.81  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.60/1.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.60/1.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.60/1.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.60/1.81  thf(sk_B_type, type, sk_B: $i).
% 1.60/1.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.60/1.81  thf(sk_A_type, type, sk_A: $i).
% 1.60/1.81  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.60/1.81  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.60/1.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.60/1.81  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.60/1.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.60/1.81  thf(t40_subset_1, conjecture,
% 1.60/1.81    (![A:$i,B:$i,C:$i]:
% 1.60/1.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.60/1.81       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 1.60/1.81         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.60/1.81  thf(zf_stmt_0, negated_conjecture,
% 1.60/1.81    (~( ![A:$i,B:$i,C:$i]:
% 1.60/1.81        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.60/1.81          ( ( ( r1_tarski @ B @ C ) & 
% 1.60/1.81              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 1.60/1.81            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 1.60/1.81    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 1.60/1.81  thf('0', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_2))),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('1', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf(d5_subset_1, axiom,
% 1.60/1.81    (![A:$i,B:$i]:
% 1.60/1.81     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.60/1.81       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.60/1.81  thf('2', plain,
% 1.60/1.81      (![X29 : $i, X30 : $i]:
% 1.60/1.81         (((k3_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))
% 1.60/1.81          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 1.60/1.81      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.60/1.81  thf('3', plain,
% 1.60/1.81      (((k3_subset_1 @ sk_A @ sk_C_2) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 1.60/1.81      inference('sup-', [status(thm)], ['1', '2'])).
% 1.60/1.81  thf(t106_xboole_1, axiom,
% 1.60/1.81    (![A:$i,B:$i,C:$i]:
% 1.60/1.81     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 1.60/1.81       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 1.60/1.81  thf('4', plain,
% 1.60/1.81      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.60/1.81         ((r1_xboole_0 @ X6 @ X8)
% 1.60/1.81          | ~ (r1_tarski @ X6 @ (k4_xboole_0 @ X7 @ X8)))),
% 1.60/1.81      inference('cnf', [status(esa)], [t106_xboole_1])).
% 1.60/1.81  thf('5', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C_2))
% 1.60/1.81          | (r1_xboole_0 @ X0 @ sk_C_2))),
% 1.60/1.81      inference('sup-', [status(thm)], ['3', '4'])).
% 1.60/1.81  thf('6', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 1.60/1.81      inference('sup-', [status(thm)], ['0', '5'])).
% 1.60/1.81  thf(t83_xboole_1, axiom,
% 1.60/1.81    (![A:$i,B:$i]:
% 1.60/1.81     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.60/1.81  thf('7', plain,
% 1.60/1.81      (![X15 : $i, X16 : $i]:
% 1.60/1.81         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 1.60/1.81      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.60/1.81  thf('8', plain, (((k4_xboole_0 @ sk_B @ sk_C_2) = (sk_B))),
% 1.60/1.81      inference('sup-', [status(thm)], ['6', '7'])).
% 1.60/1.81  thf('9', plain, ((r1_tarski @ sk_B @ sk_C_2)),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf(t85_xboole_1, axiom,
% 1.60/1.81    (![A:$i,B:$i,C:$i]:
% 1.60/1.81     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 1.60/1.81  thf('10', plain,
% 1.60/1.81      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.60/1.81         (~ (r1_tarski @ X18 @ X19)
% 1.60/1.81          | (r1_xboole_0 @ X18 @ (k4_xboole_0 @ X20 @ X19)))),
% 1.60/1.81      inference('cnf', [status(esa)], [t85_xboole_1])).
% 1.60/1.81  thf('11', plain,
% 1.60/1.81      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_2))),
% 1.60/1.81      inference('sup-', [status(thm)], ['9', '10'])).
% 1.60/1.81  thf('12', plain,
% 1.60/1.81      (![X15 : $i, X16 : $i]:
% 1.60/1.81         (((k4_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_xboole_0 @ X15 @ X16))),
% 1.60/1.81      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.60/1.81  thf('13', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         ((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_2)) = (sk_B))),
% 1.60/1.81      inference('sup-', [status(thm)], ['11', '12'])).
% 1.60/1.81  thf('14', plain, (((k4_xboole_0 @ sk_B @ sk_B) = (sk_B))),
% 1.60/1.81      inference('sup+', [status(thm)], ['8', '13'])).
% 1.60/1.81  thf(d3_tarski, axiom,
% 1.60/1.81    (![A:$i,B:$i]:
% 1.60/1.81     ( ( r1_tarski @ A @ B ) <=>
% 1.60/1.81       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.60/1.81  thf('15', plain,
% 1.60/1.81      (![X1 : $i, X3 : $i]:
% 1.60/1.81         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.60/1.81      inference('cnf', [status(esa)], [d3_tarski])).
% 1.60/1.81  thf('16', plain,
% 1.60/1.81      (![X1 : $i, X3 : $i]:
% 1.60/1.81         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.60/1.81      inference('cnf', [status(esa)], [d3_tarski])).
% 1.60/1.81  thf('17', plain,
% 1.60/1.81      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 1.60/1.81      inference('sup-', [status(thm)], ['15', '16'])).
% 1.60/1.81  thf('18', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.60/1.81      inference('simplify', [status(thm)], ['17'])).
% 1.60/1.81  thf(d1_zfmisc_1, axiom,
% 1.60/1.81    (![A:$i,B:$i]:
% 1.60/1.81     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.60/1.81       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.60/1.81  thf('19', plain,
% 1.60/1.81      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.60/1.81         (~ (r1_tarski @ X21 @ X22)
% 1.60/1.81          | (r2_hidden @ X21 @ X23)
% 1.60/1.81          | ((X23) != (k1_zfmisc_1 @ X22)))),
% 1.60/1.81      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.60/1.81  thf('20', plain,
% 1.60/1.81      (![X21 : $i, X22 : $i]:
% 1.60/1.81         ((r2_hidden @ X21 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X21 @ X22))),
% 1.60/1.81      inference('simplify', [status(thm)], ['19'])).
% 1.60/1.81  thf('21', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.60/1.81      inference('sup-', [status(thm)], ['18', '20'])).
% 1.60/1.81  thf(d2_subset_1, axiom,
% 1.60/1.81    (![A:$i,B:$i]:
% 1.60/1.81     ( ( ( v1_xboole_0 @ A ) =>
% 1.60/1.81         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.60/1.81       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.60/1.81         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.60/1.81  thf('22', plain,
% 1.60/1.81      (![X26 : $i, X27 : $i]:
% 1.60/1.81         (~ (r2_hidden @ X26 @ X27)
% 1.60/1.81          | (m1_subset_1 @ X26 @ X27)
% 1.60/1.81          | (v1_xboole_0 @ X27))),
% 1.60/1.81      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.60/1.81  thf('23', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.60/1.81          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 1.60/1.81      inference('sup-', [status(thm)], ['21', '22'])).
% 1.60/1.81  thf('24', plain,
% 1.60/1.81      (![X29 : $i, X30 : $i]:
% 1.60/1.81         (((k3_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))
% 1.60/1.81          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 1.60/1.81      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.60/1.81  thf('25', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.60/1.81          | ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0)))),
% 1.60/1.81      inference('sup-', [status(thm)], ['23', '24'])).
% 1.60/1.81  thf('26', plain,
% 1.60/1.81      (![X27 : $i, X28 : $i]:
% 1.60/1.81         (~ (v1_xboole_0 @ X28)
% 1.60/1.81          | (m1_subset_1 @ X28 @ X27)
% 1.60/1.81          | ~ (v1_xboole_0 @ X27))),
% 1.60/1.81      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.60/1.81  thf('27', plain,
% 1.60/1.81      (![X29 : $i, X30 : $i]:
% 1.60/1.81         (((k3_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))
% 1.60/1.81          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 1.60/1.81      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.60/1.81  thf('28', plain,
% 1.60/1.81      (![X0 : $i, X1 : $i]:
% 1.60/1.81         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.60/1.81          | ~ (v1_xboole_0 @ X1)
% 1.60/1.81          | ((k3_subset_1 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1)))),
% 1.60/1.81      inference('sup-', [status(thm)], ['26', '27'])).
% 1.60/1.81  thf('29', plain,
% 1.60/1.81      (![X0 : $i, X1 : $i]:
% 1.60/1.81         (((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))
% 1.60/1.81          | ((k3_subset_1 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))
% 1.60/1.81          | ~ (v1_xboole_0 @ X1))),
% 1.60/1.81      inference('sup-', [status(thm)], ['25', '28'])).
% 1.60/1.81  thf('30', plain,
% 1.60/1.81      ((((k3_subset_1 @ sk_B @ sk_B) = (sk_B))
% 1.60/1.81        | ~ (v1_xboole_0 @ sk_B)
% 1.60/1.81        | ((k3_subset_1 @ sk_B @ sk_B) = (k4_xboole_0 @ sk_B @ sk_B)))),
% 1.60/1.81      inference('sup+', [status(thm)], ['14', '29'])).
% 1.60/1.81  thf('31', plain,
% 1.60/1.81      (((k3_subset_1 @ sk_A @ sk_C_2) = (k4_xboole_0 @ sk_A @ sk_C_2))),
% 1.60/1.81      inference('sup-', [status(thm)], ['1', '2'])).
% 1.60/1.81  thf('32', plain,
% 1.60/1.81      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_2))),
% 1.60/1.81      inference('sup-', [status(thm)], ['9', '10'])).
% 1.60/1.81  thf('33', plain, ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_2))),
% 1.60/1.81      inference('sup+', [status(thm)], ['31', '32'])).
% 1.60/1.81  thf(t69_xboole_1, axiom,
% 1.60/1.81    (![A:$i,B:$i]:
% 1.60/1.81     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.60/1.81       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 1.60/1.81  thf('34', plain,
% 1.60/1.81      (![X11 : $i, X12 : $i]:
% 1.60/1.81         (~ (r1_xboole_0 @ X11 @ X12)
% 1.60/1.81          | ~ (r1_tarski @ X11 @ X12)
% 1.60/1.81          | (v1_xboole_0 @ X11))),
% 1.60/1.81      inference('cnf', [status(esa)], [t69_xboole_1])).
% 1.60/1.81  thf('35', plain,
% 1.60/1.81      (((v1_xboole_0 @ sk_B)
% 1.60/1.81        | ~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_2)))),
% 1.60/1.81      inference('sup-', [status(thm)], ['33', '34'])).
% 1.60/1.81  thf('36', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_2))),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('37', plain, ((v1_xboole_0 @ sk_B)),
% 1.60/1.81      inference('demod', [status(thm)], ['35', '36'])).
% 1.60/1.81  thf('38', plain, (((k4_xboole_0 @ sk_B @ sk_B) = (sk_B))),
% 1.60/1.81      inference('sup+', [status(thm)], ['8', '13'])).
% 1.60/1.81  thf('39', plain,
% 1.60/1.81      ((((k3_subset_1 @ sk_B @ sk_B) = (sk_B))
% 1.60/1.81        | ((k3_subset_1 @ sk_B @ sk_B) = (sk_B)))),
% 1.60/1.81      inference('demod', [status(thm)], ['30', '37', '38'])).
% 1.60/1.81  thf('40', plain, (((k3_subset_1 @ sk_B @ sk_B) = (sk_B))),
% 1.60/1.81      inference('simplify', [status(thm)], ['39'])).
% 1.60/1.81  thf(t3_boole, axiom,
% 1.60/1.81    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.60/1.81  thf('41', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.60/1.81      inference('cnf', [status(esa)], [t3_boole])).
% 1.60/1.81  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.60/1.81  thf('42', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 1.60/1.81      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.60/1.81  thf('43', plain,
% 1.60/1.81      (![X21 : $i, X22 : $i]:
% 1.60/1.81         ((r2_hidden @ X21 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X21 @ X22))),
% 1.60/1.81      inference('simplify', [status(thm)], ['19'])).
% 1.60/1.81  thf('44', plain,
% 1.60/1.81      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.60/1.81      inference('sup-', [status(thm)], ['42', '43'])).
% 1.60/1.81  thf('45', plain,
% 1.60/1.81      (![X26 : $i, X27 : $i]:
% 1.60/1.81         (~ (r2_hidden @ X26 @ X27)
% 1.60/1.81          | (m1_subset_1 @ X26 @ X27)
% 1.60/1.81          | (v1_xboole_0 @ X27))),
% 1.60/1.81      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.60/1.81  thf('46', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.60/1.81          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 1.60/1.81      inference('sup-', [status(thm)], ['44', '45'])).
% 1.60/1.81  thf('47', plain,
% 1.60/1.81      (![X29 : $i, X30 : $i]:
% 1.60/1.81         (((k3_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))
% 1.60/1.81          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 1.60/1.81      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.60/1.81  thf('48', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.60/1.81          | ((k3_subset_1 @ X0 @ k1_xboole_0)
% 1.60/1.81              = (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.60/1.81      inference('sup-', [status(thm)], ['46', '47'])).
% 1.60/1.81  thf('49', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.60/1.81      inference('cnf', [status(esa)], [t3_boole])).
% 1.60/1.81  thf('50', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.60/1.81          | ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0)))),
% 1.60/1.81      inference('demod', [status(thm)], ['48', '49'])).
% 1.60/1.81  thf('51', plain,
% 1.60/1.81      (![X0 : $i, X1 : $i]:
% 1.60/1.81         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.60/1.81          | ~ (v1_xboole_0 @ X1)
% 1.60/1.81          | ((k3_subset_1 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1)))),
% 1.60/1.81      inference('sup-', [status(thm)], ['26', '27'])).
% 1.60/1.81  thf('52', plain,
% 1.60/1.81      (![X0 : $i, X1 : $i]:
% 1.60/1.81         (((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))
% 1.60/1.81          | ((k3_subset_1 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))
% 1.60/1.81          | ~ (v1_xboole_0 @ X1))),
% 1.60/1.81      inference('sup-', [status(thm)], ['50', '51'])).
% 1.60/1.81  thf('53', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         (((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))
% 1.60/1.81          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.60/1.81          | ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0)))),
% 1.60/1.81      inference('sup+', [status(thm)], ['41', '52'])).
% 1.60/1.81  thf('54', plain, (![X9 : $i]: (r1_tarski @ k1_xboole_0 @ X9)),
% 1.60/1.81      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.60/1.81  thf('55', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 1.60/1.81      inference('cnf', [status(esa)], [t3_boole])).
% 1.60/1.81  thf(t79_xboole_1, axiom,
% 1.60/1.81    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.60/1.81  thf('56', plain,
% 1.60/1.81      (![X13 : $i, X14 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X14)),
% 1.60/1.81      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.60/1.81  thf('57', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.60/1.81      inference('sup+', [status(thm)], ['55', '56'])).
% 1.60/1.81  thf('58', plain,
% 1.60/1.81      (![X11 : $i, X12 : $i]:
% 1.60/1.81         (~ (r1_xboole_0 @ X11 @ X12)
% 1.60/1.81          | ~ (r1_tarski @ X11 @ X12)
% 1.60/1.81          | (v1_xboole_0 @ X11))),
% 1.60/1.81      inference('cnf', [status(esa)], [t69_xboole_1])).
% 1.60/1.81  thf('59', plain,
% 1.60/1.81      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 1.60/1.81      inference('sup-', [status(thm)], ['57', '58'])).
% 1.60/1.81  thf('60', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.60/1.81      inference('sup-', [status(thm)], ['54', '59'])).
% 1.60/1.81  thf('61', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         (((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))
% 1.60/1.81          | ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0)))),
% 1.60/1.81      inference('demod', [status(thm)], ['53', '60'])).
% 1.60/1.81  thf('62', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 1.60/1.81      inference('simplify', [status(thm)], ['61'])).
% 1.60/1.81  thf('63', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.60/1.81          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 1.60/1.81      inference('sup-', [status(thm)], ['44', '45'])).
% 1.60/1.81  thf(involutiveness_k3_subset_1, axiom,
% 1.60/1.81    (![A:$i,B:$i]:
% 1.60/1.81     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.60/1.81       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.60/1.81  thf('64', plain,
% 1.60/1.81      (![X31 : $i, X32 : $i]:
% 1.60/1.81         (((k3_subset_1 @ X32 @ (k3_subset_1 @ X32 @ X31)) = (X31))
% 1.60/1.81          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32)))),
% 1.60/1.81      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.60/1.81  thf('65', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.60/1.81          | ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 1.60/1.81              = (k1_xboole_0)))),
% 1.60/1.81      inference('sup-', [status(thm)], ['63', '64'])).
% 1.60/1.81  thf('66', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 1.60/1.81      inference('simplify', [status(thm)], ['61'])).
% 1.60/1.81  thf('67', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.60/1.81          | ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0)))),
% 1.60/1.81      inference('demod', [status(thm)], ['65', '66'])).
% 1.60/1.81  thf('68', plain,
% 1.60/1.81      (![X27 : $i, X28 : $i]:
% 1.60/1.81         (~ (v1_xboole_0 @ X28)
% 1.60/1.81          | (m1_subset_1 @ X28 @ X27)
% 1.60/1.81          | ~ (v1_xboole_0 @ X27))),
% 1.60/1.81      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.60/1.81  thf('69', plain,
% 1.60/1.81      (![X31 : $i, X32 : $i]:
% 1.60/1.81         (((k3_subset_1 @ X32 @ (k3_subset_1 @ X32 @ X31)) = (X31))
% 1.60/1.81          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32)))),
% 1.60/1.81      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.60/1.81  thf('70', plain,
% 1.60/1.81      (![X0 : $i, X1 : $i]:
% 1.60/1.81         (~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.60/1.81          | ~ (v1_xboole_0 @ X1)
% 1.60/1.81          | ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X1)) = (X1)))),
% 1.60/1.81      inference('sup-', [status(thm)], ['68', '69'])).
% 1.60/1.81  thf('71', plain,
% 1.60/1.81      (![X0 : $i, X1 : $i]:
% 1.60/1.81         (((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))
% 1.60/1.81          | ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X1)) = (X1))
% 1.60/1.81          | ~ (v1_xboole_0 @ X1))),
% 1.60/1.81      inference('sup-', [status(thm)], ['67', '70'])).
% 1.60/1.81  thf('72', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         (((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))
% 1.60/1.81          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.60/1.81          | ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0)))),
% 1.60/1.81      inference('sup+', [status(thm)], ['62', '71'])).
% 1.60/1.81  thf('73', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.60/1.81      inference('sup-', [status(thm)], ['54', '59'])).
% 1.60/1.81  thf('74', plain,
% 1.60/1.81      (![X0 : $i]:
% 1.60/1.81         (((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))
% 1.60/1.81          | ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0)))),
% 1.60/1.81      inference('demod', [status(thm)], ['72', '73'])).
% 1.60/1.81  thf('75', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.60/1.81      inference('simplify', [status(thm)], ['74'])).
% 1.60/1.81  thf('76', plain, (((k1_xboole_0) = (sk_B))),
% 1.60/1.81      inference('demod', [status(thm)], ['40', '75'])).
% 1.60/1.81  thf('77', plain, (((sk_B) != (k1_xboole_0))),
% 1.60/1.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.81  thf('78', plain, ($false),
% 1.60/1.81      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 1.60/1.81  
% 1.60/1.81  % SZS output end Refutation
% 1.60/1.81  
% 1.64/1.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
