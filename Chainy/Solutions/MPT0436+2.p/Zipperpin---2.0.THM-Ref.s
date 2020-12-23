%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0436+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Dl5aySU1Wz

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:55 EST 2020

% Result     : Theorem 21.38s
% Output     : Refutation 21.38s
% Verified   : 
% Statistics : Number of formulae       :   44 (  47 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :  185 ( 208 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_A_4_type,type,(
    sk_A_4: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_36_type,type,(
    sk_D_36: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_13_type,type,(
    sk_B_13: $i )).

thf(t19_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ ( A @ ( k2_relat_1 @ B ) ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ ( C @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ~ ( ( r2_hidden @ ( A @ ( k2_relat_1 @ B ) ) )
            & ! [C: $i] :
                ~ ( r2_hidden @ ( C @ ( k1_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_relat_1])).

thf('0',plain,(
    r2_hidden @ ( sk_A_4 @ ( k2_relat_1 @ sk_B_13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ ( D @ C ) @ A ) ) ) ) )).

thf('1',plain,(
    ! [X2050: $i,X2051: $i,X2052: $i] :
      ( ~ ( r2_hidden @ ( X2052 @ X2051 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_36 @ ( X2052 @ X2050 ) @ X2052 ) @ X2050 ) )
      | ( X2051
       != ( k2_relat_1 @ X2050 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('2',plain,(
    ! [X2050: $i,X2052: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_36 @ ( X2052 @ X2050 ) @ X2052 ) @ X2050 ) )
      | ~ ( r2_hidden @ ( X2052 @ ( k2_relat_1 @ X2050 ) ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_36 @ ( sk_A_4 @ sk_B_13 ) @ sk_A_4 ) @ sk_B_13 ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ ( C @ D ) @ A ) ) ) ) )).

thf('4',plain,(
    ! [X2041: $i,X2042: $i,X2043: $i,X2044: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( X2041 @ X2042 ) @ X2043 ) )
      | ( r2_hidden @ ( X2041 @ X2044 ) )
      | ( X2044
       != ( k1_relat_1 @ X2043 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('5',plain,(
    ! [X2041: $i,X2042: $i,X2043: $i] :
      ( ( r2_hidden @ ( X2041 @ ( k1_relat_1 @ X2043 ) ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( X2041 @ X2042 ) @ X2043 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    r2_hidden @ ( sk_D_36 @ ( sk_A_4 @ sk_B_13 ) @ ( k1_relat_1 @ sk_B_13 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('7',plain,(
    ! [X12: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ( r2_hidden @ ( sk_B @ X12 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('8',plain,(
    ! [X2069: $i] :
      ~ ( r2_hidden @ ( X2069 @ ( k1_relat_1 @ sk_B_13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_xboole_0 @ ( k1_relat_1 @ sk_B_13 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X46: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('11',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('12',plain,(
    ! [X46: $i] :
      ( ( X46 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_relat_1 @ sk_B_13 )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    r2_hidden @ ( sk_D_36 @ ( sk_A_4 @ sk_B_13 ) @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['6','13'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ ( A @ k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X317: $i] :
      ( r1_xboole_0 @ ( X317 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('16',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('17',plain,(
    ! [X317: $i] :
      ( r1_xboole_0 @ ( X317 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A @ B ) )
        & ( r2_hidden @ ( A @ B ) ) ) )).

thf('18',plain,(
    ! [X1028: $i,X1029: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X1028 @ X1029 ) )
      | ~ ( r2_hidden @ ( X1028 @ X1029 ) ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( X0 @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    $false ),
    inference('sup-',[status(thm)],['14','19'])).

%------------------------------------------------------------------------------
