%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pBj1yPlUaX

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:53 EST 2020

% Result     : Theorem 9.56s
% Output     : Refutation 9.56s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 973 expanded)
%              Number of leaves         :   42 ( 315 expanded)
%              Depth                    :   29
%              Number of atoms          : 1278 (7303 expanded)
%              Number of equality atoms :   81 ( 551 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t31_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
             => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X45: $i] :
      ( ( ( k3_relat_1 @ X45 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    ! [X45: $i] :
      ( ( ( k3_relat_1 @ X45 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('9',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','10'])).

thf('12',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t15_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ X47 ) @ ( k1_relat_1 @ X46 ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ X47 @ X46 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t15_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k6_subset_1 @ X35 @ X36 )
      = ( k4_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('17',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k6_subset_1 @ X35 @ X36 )
      = ( k4_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('18',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ X47 ) @ ( k1_relat_1 @ X46 ) ) @ ( k1_relat_1 @ ( k4_xboole_0 @ X47 @ X46 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X1 ) @ ( k2_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['14','20'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('22',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k2_tarski @ X26 @ X25 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X31 @ X32 ) )
      = ( k2_xboole_0 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k2_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['21','26','27','28'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ sk_B_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('33',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('34',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ~ ( r1_tarski @ X24 @ X23 )
      | ( r1_tarski @ ( k2_xboole_0 @ X22 @ X24 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('38',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X7 @ ( k2_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('44',plain,(
    ! [X40: $i,X43: $i] :
      ( ( X43
        = ( k1_relat_1 @ X40 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X43 @ X40 ) @ ( sk_D @ X43 @ X40 ) ) @ X40 )
      | ( r2_hidden @ ( sk_C @ X43 @ X40 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('45',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X30 ) @ X29 )
        = X29 )
      | ~ ( r2_hidden @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( ( k2_xboole_0 @ X0 @ ( k1_tarski @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( k4_tarski @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( sk_D @ X0 @ k1_xboole_0 ) ) )
        = k1_xboole_0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('51',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('52',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ~ ( r1_tarski @ X24 @ X23 )
      | ( r1_tarski @ ( k2_xboole_0 @ X22 @ X24 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('57',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X33 ) @ X34 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['49','58'])).

thf('60',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X30 ) @ X29 )
        = X29 )
      | ~ ( r2_hidden @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_C @ X0 @ k1_xboole_0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( ( k2_xboole_0 @ X0 @ ( k1_tarski @ ( sk_C @ X0 @ k1_xboole_0 ) ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k1_tarski @ ( sk_C @ k1_xboole_0 @ k1_xboole_0 ) )
      = k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['42','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('66',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['31','66','67'])).

thf('69',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('73',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ sk_B_1 ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X45: $i] :
      ( ( ( k3_relat_1 @ X45 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('77',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X7 @ ( k2_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) @ X3 )
      | ( r1_tarski @ X1 @ X3 ) ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ X0 ) @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','81'])).

thf('83',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['73','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t28_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('87',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ X51 ) @ ( k2_relat_1 @ X50 ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ X51 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t28_relat_1])).

thf('88',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k6_subset_1 @ X35 @ X36 )
      = ( k4_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('89',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k6_subset_1 @ X35 @ X36 )
      = ( k4_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('90',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( v1_relat_1 @ X50 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X51 ) @ ( k2_relat_1 @ X50 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X51 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ ( k2_relat_1 @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['86','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('95',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('98',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ sk_B_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('100',plain,(
    ! [X37: $i] :
      ( ( v1_relat_1 @ X37 )
      | ~ ( v1_xboole_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('101',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('102',plain,(
    ! [X45: $i] :
      ( ( ( k3_relat_1 @ X45 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('103',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('105',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['100','105'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('107',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('108',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( k3_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ sk_B_1 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['99','108'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('110',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('111',plain,(
    ! [X37: $i] :
      ( ( v1_relat_1 @ X37 )
      | ~ ( v1_xboole_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('112',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf(t19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) )).

thf('113',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X48 ) @ ( k1_relat_1 @ X48 ) )
      | ~ ( r2_hidden @ X49 @ ( k2_relat_1 @ X48 ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t19_relat_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['111','116'])).

thf('118',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['110','119'])).

thf('121',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X30 ) @ X29 )
        = X29 )
      | ~ ( r2_hidden @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('122',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_C_1 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ X13 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('125',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('127',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['125','128'])).

thf('130',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( ( k1_tarski @ ( sk_C_1 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['122','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('132',plain,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['109','132','133'])).

thf('135',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['85','134'])).

thf('136',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('137',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ~ ( r1_tarski @ X24 @ X23 )
      | ( r1_tarski @ ( k2_xboole_0 @ X22 @ X24 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B_1 ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['135','138'])).

thf('140',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','139'])).

thf('141',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    $false ),
    inference(demod,[status(thm)],['0','142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pBj1yPlUaX
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:13:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 9.56/9.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.56/9.79  % Solved by: fo/fo7.sh
% 9.56/9.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.56/9.79  % done 11048 iterations in 9.332s
% 9.56/9.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.56/9.79  % SZS output start Refutation
% 9.56/9.79  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 9.56/9.79  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 9.56/9.79  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 9.56/9.79  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 9.56/9.79  thf(sk_B_type, type, sk_B: $i > $i).
% 9.56/9.79  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 9.56/9.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.56/9.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.56/9.79  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 9.56/9.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.56/9.79  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 9.56/9.79  thf(sk_B_1_type, type, sk_B_1: $i).
% 9.56/9.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 9.56/9.79  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 9.56/9.79  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 9.56/9.79  thf(sk_A_type, type, sk_A: $i).
% 9.56/9.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 9.56/9.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.56/9.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 9.56/9.79  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 9.56/9.79  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 9.56/9.79  thf(t31_relat_1, conjecture,
% 9.56/9.79    (![A:$i]:
% 9.56/9.79     ( ( v1_relat_1 @ A ) =>
% 9.56/9.79       ( ![B:$i]:
% 9.56/9.79         ( ( v1_relat_1 @ B ) =>
% 9.56/9.79           ( ( r1_tarski @ A @ B ) =>
% 9.56/9.79             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 9.56/9.79  thf(zf_stmt_0, negated_conjecture,
% 9.56/9.79    (~( ![A:$i]:
% 9.56/9.79        ( ( v1_relat_1 @ A ) =>
% 9.56/9.79          ( ![B:$i]:
% 9.56/9.79            ( ( v1_relat_1 @ B ) =>
% 9.56/9.79              ( ( r1_tarski @ A @ B ) =>
% 9.56/9.79                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 9.56/9.79    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 9.56/9.79  thf('0', plain,
% 9.56/9.79      (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 9.56/9.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.56/9.79  thf(d6_relat_1, axiom,
% 9.56/9.79    (![A:$i]:
% 9.56/9.79     ( ( v1_relat_1 @ A ) =>
% 9.56/9.79       ( ( k3_relat_1 @ A ) =
% 9.56/9.79         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 9.56/9.79  thf('1', plain,
% 9.56/9.79      (![X45 : $i]:
% 9.56/9.79         (((k3_relat_1 @ X45)
% 9.56/9.79            = (k2_xboole_0 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45)))
% 9.56/9.79          | ~ (v1_relat_1 @ X45))),
% 9.56/9.79      inference('cnf', [status(esa)], [d6_relat_1])).
% 9.56/9.79  thf('2', plain,
% 9.56/9.79      (![X45 : $i]:
% 9.56/9.79         (((k3_relat_1 @ X45)
% 9.56/9.79            = (k2_xboole_0 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45)))
% 9.56/9.79          | ~ (v1_relat_1 @ X45))),
% 9.56/9.79      inference('cnf', [status(esa)], [d6_relat_1])).
% 9.56/9.79  thf(d10_xboole_0, axiom,
% 9.56/9.79    (![A:$i,B:$i]:
% 9.56/9.79     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 9.56/9.79  thf('3', plain,
% 9.56/9.79      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 9.56/9.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.56/9.79  thf('4', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 9.56/9.79      inference('simplify', [status(thm)], ['3'])).
% 9.56/9.79  thf(l32_xboole_1, axiom,
% 9.56/9.79    (![A:$i,B:$i]:
% 9.56/9.79     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 9.56/9.79  thf('5', plain,
% 9.56/9.79      (![X4 : $i, X6 : $i]:
% 9.56/9.79         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 9.56/9.79      inference('cnf', [status(esa)], [l32_xboole_1])).
% 9.56/9.79  thf('6', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 9.56/9.79      inference('sup-', [status(thm)], ['4', '5'])).
% 9.56/9.79  thf(t44_xboole_1, axiom,
% 9.56/9.79    (![A:$i,B:$i,C:$i]:
% 9.56/9.79     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 9.56/9.79       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 9.56/9.79  thf('7', plain,
% 9.56/9.79      (![X19 : $i, X20 : $i, X21 : $i]:
% 9.56/9.79         ((r1_tarski @ X19 @ (k2_xboole_0 @ X20 @ X21))
% 9.56/9.79          | ~ (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X21))),
% 9.56/9.79      inference('cnf', [status(esa)], [t44_xboole_1])).
% 9.56/9.79  thf('8', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i]:
% 9.56/9.79         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 9.56/9.79          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 9.56/9.79      inference('sup-', [status(thm)], ['6', '7'])).
% 9.56/9.79  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 9.56/9.79  thf('9', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 9.56/9.79      inference('cnf', [status(esa)], [t2_xboole_1])).
% 9.56/9.79  thf('10', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 9.56/9.79      inference('demod', [status(thm)], ['8', '9'])).
% 9.56/9.79  thf('11', plain,
% 9.56/9.79      (![X0 : $i]:
% 9.56/9.79         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 9.56/9.79          | ~ (v1_relat_1 @ X0))),
% 9.56/9.79      inference('sup+', [status(thm)], ['2', '10'])).
% 9.56/9.79  thf('12', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 9.56/9.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.56/9.79  thf('13', plain,
% 9.56/9.79      (![X4 : $i, X6 : $i]:
% 9.56/9.79         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 9.56/9.79      inference('cnf', [status(esa)], [l32_xboole_1])).
% 9.56/9.79  thf('14', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 9.56/9.79      inference('sup-', [status(thm)], ['12', '13'])).
% 9.56/9.79  thf(t15_relat_1, axiom,
% 9.56/9.79    (![A:$i]:
% 9.56/9.79     ( ( v1_relat_1 @ A ) =>
% 9.56/9.79       ( ![B:$i]:
% 9.56/9.79         ( ( v1_relat_1 @ B ) =>
% 9.56/9.79           ( r1_tarski @
% 9.56/9.79             ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ 
% 9.56/9.79             ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 9.56/9.79  thf('15', plain,
% 9.56/9.79      (![X46 : $i, X47 : $i]:
% 9.56/9.79         (~ (v1_relat_1 @ X46)
% 9.56/9.79          | (r1_tarski @ 
% 9.56/9.79             (k6_subset_1 @ (k1_relat_1 @ X47) @ (k1_relat_1 @ X46)) @ 
% 9.56/9.79             (k1_relat_1 @ (k6_subset_1 @ X47 @ X46)))
% 9.56/9.79          | ~ (v1_relat_1 @ X47))),
% 9.56/9.79      inference('cnf', [status(esa)], [t15_relat_1])).
% 9.56/9.79  thf(redefinition_k6_subset_1, axiom,
% 9.56/9.79    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 9.56/9.79  thf('16', plain,
% 9.56/9.79      (![X35 : $i, X36 : $i]:
% 9.56/9.79         ((k6_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))),
% 9.56/9.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 9.56/9.79  thf('17', plain,
% 9.56/9.79      (![X35 : $i, X36 : $i]:
% 9.56/9.79         ((k6_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))),
% 9.56/9.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 9.56/9.79  thf('18', plain,
% 9.56/9.79      (![X46 : $i, X47 : $i]:
% 9.56/9.79         (~ (v1_relat_1 @ X46)
% 9.56/9.79          | (r1_tarski @ 
% 9.56/9.79             (k4_xboole_0 @ (k1_relat_1 @ X47) @ (k1_relat_1 @ X46)) @ 
% 9.56/9.79             (k1_relat_1 @ (k4_xboole_0 @ X47 @ X46)))
% 9.56/9.79          | ~ (v1_relat_1 @ X47))),
% 9.56/9.79      inference('demod', [status(thm)], ['15', '16', '17'])).
% 9.56/9.79  thf('19', plain,
% 9.56/9.79      (![X19 : $i, X20 : $i, X21 : $i]:
% 9.56/9.79         ((r1_tarski @ X19 @ (k2_xboole_0 @ X20 @ X21))
% 9.56/9.79          | ~ (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X21))),
% 9.56/9.79      inference('cnf', [status(esa)], [t44_xboole_1])).
% 9.56/9.79  thf('20', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i]:
% 9.56/9.79         (~ (v1_relat_1 @ X1)
% 9.56/9.79          | ~ (v1_relat_1 @ X0)
% 9.56/9.79          | (r1_tarski @ (k1_relat_1 @ X1) @ 
% 9.56/9.79             (k2_xboole_0 @ (k1_relat_1 @ X0) @ 
% 9.56/9.79              (k1_relat_1 @ (k4_xboole_0 @ X1 @ X0)))))),
% 9.56/9.79      inference('sup-', [status(thm)], ['18', '19'])).
% 9.56/9.79  thf('21', plain,
% 9.56/9.79      (((r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 9.56/9.79         (k2_xboole_0 @ (k1_relat_1 @ sk_B_1) @ (k1_relat_1 @ k1_xboole_0)))
% 9.56/9.79        | ~ (v1_relat_1 @ sk_B_1)
% 9.56/9.79        | ~ (v1_relat_1 @ sk_A))),
% 9.56/9.79      inference('sup+', [status(thm)], ['14', '20'])).
% 9.56/9.79  thf(commutativity_k2_tarski, axiom,
% 9.56/9.79    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 9.56/9.79  thf('22', plain,
% 9.56/9.79      (![X25 : $i, X26 : $i]:
% 9.56/9.79         ((k2_tarski @ X26 @ X25) = (k2_tarski @ X25 @ X26))),
% 9.56/9.79      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 9.56/9.79  thf(l51_zfmisc_1, axiom,
% 9.56/9.79    (![A:$i,B:$i]:
% 9.56/9.79     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 9.56/9.79  thf('23', plain,
% 9.56/9.79      (![X31 : $i, X32 : $i]:
% 9.56/9.79         ((k3_tarski @ (k2_tarski @ X31 @ X32)) = (k2_xboole_0 @ X31 @ X32))),
% 9.56/9.79      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 9.56/9.79  thf('24', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i]:
% 9.56/9.79         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 9.56/9.79      inference('sup+', [status(thm)], ['22', '23'])).
% 9.56/9.79  thf('25', plain,
% 9.56/9.79      (![X31 : $i, X32 : $i]:
% 9.56/9.79         ((k3_tarski @ (k2_tarski @ X31 @ X32)) = (k2_xboole_0 @ X31 @ X32))),
% 9.56/9.79      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 9.56/9.79  thf('26', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.56/9.79      inference('sup+', [status(thm)], ['24', '25'])).
% 9.56/9.79  thf('27', plain, ((v1_relat_1 @ sk_B_1)),
% 9.56/9.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.56/9.79  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 9.56/9.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.56/9.79  thf('29', plain,
% 9.56/9.79      ((r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 9.56/9.79        (k2_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ (k1_relat_1 @ sk_B_1)))),
% 9.56/9.79      inference('demod', [status(thm)], ['21', '26', '27', '28'])).
% 9.56/9.79  thf(t1_xboole_1, axiom,
% 9.56/9.79    (![A:$i,B:$i,C:$i]:
% 9.56/9.79     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 9.56/9.79       ( r1_tarski @ A @ C ) ))).
% 9.56/9.79  thf('30', plain,
% 9.56/9.79      (![X10 : $i, X11 : $i, X12 : $i]:
% 9.56/9.79         (~ (r1_tarski @ X10 @ X11)
% 9.56/9.79          | ~ (r1_tarski @ X11 @ X12)
% 9.56/9.79          | (r1_tarski @ X10 @ X12))),
% 9.56/9.79      inference('cnf', [status(esa)], [t1_xboole_1])).
% 9.56/9.79  thf('31', plain,
% 9.56/9.79      (![X0 : $i]:
% 9.56/9.79         ((r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 9.56/9.79          | ~ (r1_tarski @ 
% 9.56/9.79               (k2_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 9.56/9.79                (k1_relat_1 @ sk_B_1)) @ 
% 9.56/9.79               X0))),
% 9.56/9.79      inference('sup-', [status(thm)], ['29', '30'])).
% 9.56/9.79  thf('32', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 9.56/9.79      inference('simplify', [status(thm)], ['3'])).
% 9.56/9.79  thf('33', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 9.56/9.79      inference('cnf', [status(esa)], [t2_xboole_1])).
% 9.56/9.79  thf(t8_xboole_1, axiom,
% 9.56/9.79    (![A:$i,B:$i,C:$i]:
% 9.56/9.79     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 9.56/9.79       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 9.56/9.79  thf('34', plain,
% 9.56/9.79      (![X22 : $i, X23 : $i, X24 : $i]:
% 9.56/9.79         (~ (r1_tarski @ X22 @ X23)
% 9.56/9.79          | ~ (r1_tarski @ X24 @ X23)
% 9.56/9.79          | (r1_tarski @ (k2_xboole_0 @ X22 @ X24) @ X23))),
% 9.56/9.79      inference('cnf', [status(esa)], [t8_xboole_1])).
% 9.56/9.79  thf('35', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i]:
% 9.56/9.79         ((r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X1) @ X0)
% 9.56/9.79          | ~ (r1_tarski @ X1 @ X0))),
% 9.56/9.79      inference('sup-', [status(thm)], ['33', '34'])).
% 9.56/9.79  thf('36', plain,
% 9.56/9.79      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0)),
% 9.56/9.79      inference('sup-', [status(thm)], ['32', '35'])).
% 9.56/9.79  thf('37', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 9.56/9.79      inference('simplify', [status(thm)], ['3'])).
% 9.56/9.79  thf(t10_xboole_1, axiom,
% 9.56/9.79    (![A:$i,B:$i,C:$i]:
% 9.56/9.79     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 9.56/9.79  thf('38', plain,
% 9.56/9.79      (![X7 : $i, X8 : $i, X9 : $i]:
% 9.56/9.79         (~ (r1_tarski @ X7 @ X8) | (r1_tarski @ X7 @ (k2_xboole_0 @ X9 @ X8)))),
% 9.56/9.79      inference('cnf', [status(esa)], [t10_xboole_1])).
% 9.56/9.79  thf('39', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 9.56/9.79      inference('sup-', [status(thm)], ['37', '38'])).
% 9.56/9.79  thf('40', plain,
% 9.56/9.79      (![X1 : $i, X3 : $i]:
% 9.56/9.79         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 9.56/9.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.56/9.79  thf('41', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i]:
% 9.56/9.79         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 9.56/9.79          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 9.56/9.79      inference('sup-', [status(thm)], ['39', '40'])).
% 9.56/9.79  thf('42', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 9.56/9.79      inference('sup-', [status(thm)], ['36', '41'])).
% 9.56/9.79  thf('43', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 9.56/9.79      inference('sup-', [status(thm)], ['36', '41'])).
% 9.56/9.79  thf(d4_relat_1, axiom,
% 9.56/9.79    (![A:$i,B:$i]:
% 9.56/9.79     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 9.56/9.79       ( ![C:$i]:
% 9.56/9.79         ( ( r2_hidden @ C @ B ) <=>
% 9.56/9.79           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 9.56/9.79  thf('44', plain,
% 9.56/9.79      (![X40 : $i, X43 : $i]:
% 9.56/9.79         (((X43) = (k1_relat_1 @ X40))
% 9.56/9.79          | (r2_hidden @ 
% 9.56/9.79             (k4_tarski @ (sk_C @ X43 @ X40) @ (sk_D @ X43 @ X40)) @ X40)
% 9.56/9.79          | (r2_hidden @ (sk_C @ X43 @ X40) @ X43))),
% 9.56/9.79      inference('cnf', [status(esa)], [d4_relat_1])).
% 9.56/9.79  thf(l22_zfmisc_1, axiom,
% 9.56/9.79    (![A:$i,B:$i]:
% 9.56/9.79     ( ( r2_hidden @ A @ B ) =>
% 9.56/9.79       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 9.56/9.79  thf('45', plain,
% 9.56/9.79      (![X29 : $i, X30 : $i]:
% 9.56/9.79         (((k2_xboole_0 @ (k1_tarski @ X30) @ X29) = (X29))
% 9.56/9.79          | ~ (r2_hidden @ X30 @ X29))),
% 9.56/9.79      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 9.56/9.79  thf('46', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i]:
% 9.56/9.79         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 9.56/9.79          | ((X1) = (k1_relat_1 @ X0))
% 9.56/9.79          | ((k2_xboole_0 @ 
% 9.56/9.79              (k1_tarski @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X1 @ X0))) @ 
% 9.56/9.79              X0) = (X0)))),
% 9.56/9.79      inference('sup-', [status(thm)], ['44', '45'])).
% 9.56/9.79  thf('47', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.56/9.79      inference('sup+', [status(thm)], ['24', '25'])).
% 9.56/9.79  thf('48', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i]:
% 9.56/9.79         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 9.56/9.79          | ((X1) = (k1_relat_1 @ X0))
% 9.56/9.79          | ((k2_xboole_0 @ X0 @ 
% 9.56/9.79              (k1_tarski @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X1 @ X0))))
% 9.56/9.79              = (X0)))),
% 9.56/9.79      inference('demod', [status(thm)], ['46', '47'])).
% 9.56/9.79  thf('49', plain,
% 9.56/9.79      (![X0 : $i]:
% 9.56/9.79         (((k1_tarski @ 
% 9.56/9.79            (k4_tarski @ (sk_C @ X0 @ k1_xboole_0) @ (sk_D @ X0 @ k1_xboole_0)))
% 9.56/9.79            = (k1_xboole_0))
% 9.56/9.79          | ((X0) = (k1_relat_1 @ k1_xboole_0))
% 9.56/9.79          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0))),
% 9.56/9.79      inference('sup+', [status(thm)], ['43', '48'])).
% 9.56/9.79  thf('50', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 9.56/9.79      inference('simplify', [status(thm)], ['3'])).
% 9.56/9.79  thf('51', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 9.56/9.79      inference('simplify', [status(thm)], ['3'])).
% 9.56/9.79  thf('52', plain,
% 9.56/9.79      (![X22 : $i, X23 : $i, X24 : $i]:
% 9.56/9.79         (~ (r1_tarski @ X22 @ X23)
% 9.56/9.79          | ~ (r1_tarski @ X24 @ X23)
% 9.56/9.79          | (r1_tarski @ (k2_xboole_0 @ X22 @ X24) @ X23))),
% 9.56/9.79      inference('cnf', [status(esa)], [t8_xboole_1])).
% 9.56/9.79  thf('53', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i]:
% 9.56/9.79         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 9.56/9.79      inference('sup-', [status(thm)], ['51', '52'])).
% 9.56/9.79  thf('54', plain, (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ X0 @ X0) @ X0)),
% 9.56/9.79      inference('sup-', [status(thm)], ['50', '53'])).
% 9.56/9.79  thf('55', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i]:
% 9.56/9.79         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 9.56/9.79          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 9.56/9.79      inference('sup-', [status(thm)], ['39', '40'])).
% 9.56/9.79  thf('56', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 9.56/9.79      inference('sup-', [status(thm)], ['54', '55'])).
% 9.56/9.79  thf(t49_zfmisc_1, axiom,
% 9.56/9.79    (![A:$i,B:$i]:
% 9.56/9.79     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 9.56/9.79  thf('57', plain,
% 9.56/9.79      (![X33 : $i, X34 : $i]:
% 9.56/9.79         ((k2_xboole_0 @ (k1_tarski @ X33) @ X34) != (k1_xboole_0))),
% 9.56/9.79      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 9.56/9.79  thf('58', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 9.56/9.79      inference('sup-', [status(thm)], ['56', '57'])).
% 9.56/9.79  thf('59', plain,
% 9.56/9.79      (![X0 : $i]:
% 9.56/9.79         (((X0) = (k1_relat_1 @ k1_xboole_0))
% 9.56/9.79          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0))),
% 9.56/9.79      inference('simplify_reflect-', [status(thm)], ['49', '58'])).
% 9.56/9.79  thf('60', plain,
% 9.56/9.79      (![X29 : $i, X30 : $i]:
% 9.56/9.79         (((k2_xboole_0 @ (k1_tarski @ X30) @ X29) = (X29))
% 9.56/9.79          | ~ (r2_hidden @ X30 @ X29))),
% 9.56/9.79      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 9.56/9.79  thf('61', plain,
% 9.56/9.79      (![X0 : $i]:
% 9.56/9.79         (((X0) = (k1_relat_1 @ k1_xboole_0))
% 9.56/9.79          | ((k2_xboole_0 @ (k1_tarski @ (sk_C @ X0 @ k1_xboole_0)) @ X0)
% 9.56/9.79              = (X0)))),
% 9.56/9.79      inference('sup-', [status(thm)], ['59', '60'])).
% 9.56/9.79  thf('62', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.56/9.79      inference('sup+', [status(thm)], ['24', '25'])).
% 9.56/9.79  thf('63', plain,
% 9.56/9.79      (![X0 : $i]:
% 9.56/9.79         (((X0) = (k1_relat_1 @ k1_xboole_0))
% 9.56/9.79          | ((k2_xboole_0 @ X0 @ (k1_tarski @ (sk_C @ X0 @ k1_xboole_0)))
% 9.56/9.79              = (X0)))),
% 9.56/9.79      inference('demod', [status(thm)], ['61', '62'])).
% 9.56/9.79  thf('64', plain,
% 9.56/9.79      ((((k1_tarski @ (sk_C @ k1_xboole_0 @ k1_xboole_0)) = (k1_xboole_0))
% 9.56/9.79        | ((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0)))),
% 9.56/9.79      inference('sup+', [status(thm)], ['42', '63'])).
% 9.56/9.79  thf('65', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 9.56/9.79      inference('sup-', [status(thm)], ['56', '57'])).
% 9.56/9.79  thf('66', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 9.56/9.79      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 9.56/9.79  thf('67', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 9.56/9.79      inference('sup-', [status(thm)], ['36', '41'])).
% 9.56/9.79  thf('68', plain,
% 9.56/9.79      (![X0 : $i]:
% 9.56/9.79         ((r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 9.56/9.79          | ~ (r1_tarski @ (k1_relat_1 @ sk_B_1) @ X0))),
% 9.56/9.79      inference('demod', [status(thm)], ['31', '66', '67'])).
% 9.56/9.79  thf('69', plain,
% 9.56/9.79      ((~ (v1_relat_1 @ sk_B_1)
% 9.56/9.79        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1)))),
% 9.56/9.79      inference('sup-', [status(thm)], ['11', '68'])).
% 9.56/9.79  thf('70', plain, ((v1_relat_1 @ sk_B_1)),
% 9.56/9.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.56/9.79  thf('71', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 9.56/9.79      inference('demod', [status(thm)], ['69', '70'])).
% 9.56/9.79  thf('72', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i]:
% 9.56/9.79         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 9.56/9.79      inference('sup-', [status(thm)], ['51', '52'])).
% 9.56/9.79  thf('73', plain,
% 9.56/9.79      ((r1_tarski @ 
% 9.56/9.79        (k2_xboole_0 @ (k3_relat_1 @ sk_B_1) @ (k1_relat_1 @ sk_A)) @ 
% 9.56/9.79        (k3_relat_1 @ sk_B_1))),
% 9.56/9.79      inference('sup-', [status(thm)], ['71', '72'])).
% 9.56/9.79  thf('74', plain,
% 9.56/9.79      (![X45 : $i]:
% 9.56/9.79         (((k3_relat_1 @ X45)
% 9.56/9.79            = (k2_xboole_0 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45)))
% 9.56/9.79          | ~ (v1_relat_1 @ X45))),
% 9.56/9.79      inference('cnf', [status(esa)], [d6_relat_1])).
% 9.56/9.79  thf('75', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.56/9.79      inference('sup+', [status(thm)], ['24', '25'])).
% 9.56/9.79  thf('76', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 9.56/9.79      inference('sup-', [status(thm)], ['37', '38'])).
% 9.56/9.79  thf('77', plain,
% 9.56/9.79      (![X7 : $i, X8 : $i, X9 : $i]:
% 9.56/9.79         (~ (r1_tarski @ X7 @ X8) | (r1_tarski @ X7 @ (k2_xboole_0 @ X9 @ X8)))),
% 9.56/9.79      inference('cnf', [status(esa)], [t10_xboole_1])).
% 9.56/9.79  thf('78', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.56/9.79         (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 9.56/9.79      inference('sup-', [status(thm)], ['76', '77'])).
% 9.56/9.79  thf('79', plain,
% 9.56/9.79      (![X10 : $i, X11 : $i, X12 : $i]:
% 9.56/9.79         (~ (r1_tarski @ X10 @ X11)
% 9.56/9.79          | ~ (r1_tarski @ X11 @ X12)
% 9.56/9.79          | (r1_tarski @ X10 @ X12))),
% 9.56/9.79      inference('cnf', [status(esa)], [t1_xboole_1])).
% 9.56/9.79  thf('80', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.56/9.79         ((r1_tarski @ X0 @ X3)
% 9.56/9.79          | ~ (r1_tarski @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3))),
% 9.56/9.79      inference('sup-', [status(thm)], ['78', '79'])).
% 9.56/9.79  thf('81', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 9.56/9.79         (~ (r1_tarski @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0) @ X3)
% 9.56/9.79          | (r1_tarski @ X1 @ X3))),
% 9.56/9.79      inference('sup-', [status(thm)], ['75', '80'])).
% 9.56/9.79  thf('82', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.56/9.79         (~ (r1_tarski @ (k2_xboole_0 @ (k3_relat_1 @ X0) @ X2) @ X1)
% 9.56/9.79          | ~ (v1_relat_1 @ X0)
% 9.56/9.79          | (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 9.56/9.79      inference('sup-', [status(thm)], ['74', '81'])).
% 9.56/9.79  thf('83', plain,
% 9.56/9.79      (((r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1))
% 9.56/9.79        | ~ (v1_relat_1 @ sk_B_1))),
% 9.56/9.79      inference('sup-', [status(thm)], ['73', '82'])).
% 9.56/9.79  thf('84', plain, ((v1_relat_1 @ sk_B_1)),
% 9.56/9.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.56/9.79  thf('85', plain,
% 9.56/9.79      ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ (k3_relat_1 @ sk_B_1))),
% 9.56/9.79      inference('demod', [status(thm)], ['83', '84'])).
% 9.56/9.79  thf('86', plain, (((k4_xboole_0 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 9.56/9.79      inference('sup-', [status(thm)], ['12', '13'])).
% 9.56/9.79  thf(t28_relat_1, axiom,
% 9.56/9.79    (![A:$i]:
% 9.56/9.79     ( ( v1_relat_1 @ A ) =>
% 9.56/9.79       ( ![B:$i]:
% 9.56/9.79         ( ( v1_relat_1 @ B ) =>
% 9.56/9.79           ( r1_tarski @
% 9.56/9.79             ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ 
% 9.56/9.79             ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 9.56/9.79  thf('87', plain,
% 9.56/9.79      (![X50 : $i, X51 : $i]:
% 9.56/9.79         (~ (v1_relat_1 @ X50)
% 9.56/9.79          | (r1_tarski @ 
% 9.56/9.79             (k6_subset_1 @ (k2_relat_1 @ X51) @ (k2_relat_1 @ X50)) @ 
% 9.56/9.79             (k2_relat_1 @ (k6_subset_1 @ X51 @ X50)))
% 9.56/9.79          | ~ (v1_relat_1 @ X51))),
% 9.56/9.79      inference('cnf', [status(esa)], [t28_relat_1])).
% 9.56/9.79  thf('88', plain,
% 9.56/9.79      (![X35 : $i, X36 : $i]:
% 9.56/9.79         ((k6_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))),
% 9.56/9.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 9.56/9.79  thf('89', plain,
% 9.56/9.79      (![X35 : $i, X36 : $i]:
% 9.56/9.79         ((k6_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))),
% 9.56/9.79      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 9.56/9.79  thf('90', plain,
% 9.56/9.79      (![X50 : $i, X51 : $i]:
% 9.56/9.79         (~ (v1_relat_1 @ X50)
% 9.56/9.79          | (r1_tarski @ 
% 9.56/9.79             (k4_xboole_0 @ (k2_relat_1 @ X51) @ (k2_relat_1 @ X50)) @ 
% 9.56/9.79             (k2_relat_1 @ (k4_xboole_0 @ X51 @ X50)))
% 9.56/9.79          | ~ (v1_relat_1 @ X51))),
% 9.56/9.79      inference('demod', [status(thm)], ['87', '88', '89'])).
% 9.56/9.79  thf('91', plain,
% 9.56/9.79      (![X19 : $i, X20 : $i, X21 : $i]:
% 9.56/9.79         ((r1_tarski @ X19 @ (k2_xboole_0 @ X20 @ X21))
% 9.56/9.79          | ~ (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X21))),
% 9.56/9.79      inference('cnf', [status(esa)], [t44_xboole_1])).
% 9.56/9.79  thf('92', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i]:
% 9.56/9.79         (~ (v1_relat_1 @ X1)
% 9.56/9.79          | ~ (v1_relat_1 @ X0)
% 9.56/9.79          | (r1_tarski @ (k2_relat_1 @ X1) @ 
% 9.56/9.79             (k2_xboole_0 @ (k2_relat_1 @ X0) @ 
% 9.56/9.79              (k2_relat_1 @ (k4_xboole_0 @ X1 @ X0)))))),
% 9.56/9.79      inference('sup-', [status(thm)], ['90', '91'])).
% 9.56/9.79  thf('93', plain,
% 9.56/9.79      (((r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 9.56/9.79         (k2_xboole_0 @ (k2_relat_1 @ sk_B_1) @ (k2_relat_1 @ k1_xboole_0)))
% 9.56/9.79        | ~ (v1_relat_1 @ sk_B_1)
% 9.56/9.79        | ~ (v1_relat_1 @ sk_A))),
% 9.56/9.79      inference('sup+', [status(thm)], ['86', '92'])).
% 9.56/9.79  thf('94', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 9.56/9.79      inference('sup+', [status(thm)], ['24', '25'])).
% 9.56/9.79  thf('95', plain, ((v1_relat_1 @ sk_B_1)),
% 9.56/9.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.56/9.79  thf('96', plain, ((v1_relat_1 @ sk_A)),
% 9.56/9.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.56/9.79  thf('97', plain,
% 9.56/9.79      ((r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 9.56/9.79        (k2_xboole_0 @ (k2_relat_1 @ k1_xboole_0) @ (k2_relat_1 @ sk_B_1)))),
% 9.56/9.79      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 9.56/9.79  thf('98', plain,
% 9.56/9.79      (![X10 : $i, X11 : $i, X12 : $i]:
% 9.56/9.79         (~ (r1_tarski @ X10 @ X11)
% 9.56/9.79          | ~ (r1_tarski @ X11 @ X12)
% 9.56/9.79          | (r1_tarski @ X10 @ X12))),
% 9.56/9.79      inference('cnf', [status(esa)], [t1_xboole_1])).
% 9.56/9.79  thf('99', plain,
% 9.56/9.79      (![X0 : $i]:
% 9.56/9.79         ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 9.56/9.79          | ~ (r1_tarski @ 
% 9.56/9.79               (k2_xboole_0 @ (k2_relat_1 @ k1_xboole_0) @ 
% 9.56/9.79                (k2_relat_1 @ sk_B_1)) @ 
% 9.56/9.79               X0))),
% 9.56/9.79      inference('sup-', [status(thm)], ['97', '98'])).
% 9.56/9.79  thf(cc1_relat_1, axiom,
% 9.56/9.79    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 9.56/9.79  thf('100', plain,
% 9.56/9.79      (![X37 : $i]: ((v1_relat_1 @ X37) | ~ (v1_xboole_0 @ X37))),
% 9.56/9.79      inference('cnf', [status(esa)], [cc1_relat_1])).
% 9.56/9.79  thf('101', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 9.56/9.79      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 9.56/9.79  thf('102', plain,
% 9.56/9.79      (![X45 : $i]:
% 9.56/9.79         (((k3_relat_1 @ X45)
% 9.56/9.79            = (k2_xboole_0 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45)))
% 9.56/9.79          | ~ (v1_relat_1 @ X45))),
% 9.56/9.79      inference('cnf', [status(esa)], [d6_relat_1])).
% 9.56/9.79  thf('103', plain,
% 9.56/9.79      ((((k3_relat_1 @ k1_xboole_0)
% 9.56/9.79          = (k2_xboole_0 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0)))
% 9.56/9.79        | ~ (v1_relat_1 @ k1_xboole_0))),
% 9.56/9.79      inference('sup+', [status(thm)], ['101', '102'])).
% 9.56/9.79  thf('104', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 9.56/9.79      inference('sup-', [status(thm)], ['36', '41'])).
% 9.56/9.79  thf('105', plain,
% 9.56/9.79      ((((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 9.56/9.79        | ~ (v1_relat_1 @ k1_xboole_0))),
% 9.56/9.79      inference('demod', [status(thm)], ['103', '104'])).
% 9.56/9.79  thf('106', plain,
% 9.56/9.79      ((~ (v1_xboole_0 @ k1_xboole_0)
% 9.56/9.79        | ((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)))),
% 9.56/9.79      inference('sup-', [status(thm)], ['100', '105'])).
% 9.56/9.79  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 9.56/9.79  thf('107', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 9.56/9.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 9.56/9.79  thf('108', plain,
% 9.56/9.79      (((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 9.56/9.79      inference('demod', [status(thm)], ['106', '107'])).
% 9.56/9.79  thf('109', plain,
% 9.56/9.79      (![X0 : $i]:
% 9.56/9.79         ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 9.56/9.79          | ~ (r1_tarski @ 
% 9.56/9.79               (k2_xboole_0 @ (k3_relat_1 @ k1_xboole_0) @ 
% 9.56/9.79                (k2_relat_1 @ sk_B_1)) @ 
% 9.56/9.79               X0))),
% 9.56/9.79      inference('demod', [status(thm)], ['99', '108'])).
% 9.56/9.79  thf(t7_xboole_0, axiom,
% 9.56/9.79    (![A:$i]:
% 9.56/9.79     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 9.56/9.79          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 9.56/9.79  thf('110', plain,
% 9.56/9.79      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 9.56/9.79      inference('cnf', [status(esa)], [t7_xboole_0])).
% 9.56/9.79  thf('111', plain,
% 9.56/9.79      (![X37 : $i]: ((v1_relat_1 @ X37) | ~ (v1_xboole_0 @ X37))),
% 9.56/9.79      inference('cnf', [status(esa)], [cc1_relat_1])).
% 9.56/9.79  thf('112', plain,
% 9.56/9.79      (((k3_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 9.56/9.79      inference('demod', [status(thm)], ['106', '107'])).
% 9.56/9.79  thf(t19_relat_1, axiom,
% 9.56/9.79    (![A:$i,B:$i]:
% 9.56/9.79     ( ( v1_relat_1 @ B ) =>
% 9.56/9.79       ( ~( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) & 
% 9.56/9.79            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 9.56/9.79  thf('113', plain,
% 9.56/9.79      (![X48 : $i, X49 : $i]:
% 9.56/9.79         ((r2_hidden @ (sk_C_1 @ X48) @ (k1_relat_1 @ X48))
% 9.56/9.79          | ~ (r2_hidden @ X49 @ (k2_relat_1 @ X48))
% 9.56/9.79          | ~ (v1_relat_1 @ X48))),
% 9.56/9.79      inference('cnf', [status(esa)], [t19_relat_1])).
% 9.56/9.79  thf('114', plain,
% 9.56/9.79      (![X0 : $i]:
% 9.56/9.79         (~ (r2_hidden @ X0 @ (k3_relat_1 @ k1_xboole_0))
% 9.56/9.79          | ~ (v1_relat_1 @ k1_xboole_0)
% 9.56/9.79          | (r2_hidden @ (sk_C_1 @ k1_xboole_0) @ (k1_relat_1 @ k1_xboole_0)))),
% 9.56/9.79      inference('sup-', [status(thm)], ['112', '113'])).
% 9.56/9.79  thf('115', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 9.56/9.79      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 9.56/9.79  thf('116', plain,
% 9.56/9.79      (![X0 : $i]:
% 9.56/9.79         (~ (r2_hidden @ X0 @ (k3_relat_1 @ k1_xboole_0))
% 9.56/9.79          | ~ (v1_relat_1 @ k1_xboole_0)
% 9.56/9.79          | (r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0))),
% 9.56/9.79      inference('demod', [status(thm)], ['114', '115'])).
% 9.56/9.79  thf('117', plain,
% 9.56/9.79      (![X0 : $i]:
% 9.56/9.79         (~ (v1_xboole_0 @ k1_xboole_0)
% 9.56/9.79          | (r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0)
% 9.56/9.79          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ k1_xboole_0)))),
% 9.56/9.79      inference('sup-', [status(thm)], ['111', '116'])).
% 9.56/9.79  thf('118', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 9.56/9.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 9.56/9.79  thf('119', plain,
% 9.56/9.79      (![X0 : $i]:
% 9.56/9.79         ((r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0)
% 9.56/9.79          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ k1_xboole_0)))),
% 9.56/9.79      inference('demod', [status(thm)], ['117', '118'])).
% 9.56/9.79  thf('120', plain,
% 9.56/9.79      ((((k3_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 9.56/9.79        | (r2_hidden @ (sk_C_1 @ k1_xboole_0) @ k1_xboole_0))),
% 9.56/9.79      inference('sup-', [status(thm)], ['110', '119'])).
% 9.56/9.79  thf('121', plain,
% 9.56/9.79      (![X29 : $i, X30 : $i]:
% 9.56/9.79         (((k2_xboole_0 @ (k1_tarski @ X30) @ X29) = (X29))
% 9.56/9.79          | ~ (r2_hidden @ X30 @ X29))),
% 9.56/9.79      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 9.56/9.79  thf('122', plain,
% 9.56/9.79      ((((k3_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 9.56/9.79        | ((k2_xboole_0 @ (k1_tarski @ (sk_C_1 @ k1_xboole_0)) @ k1_xboole_0)
% 9.56/9.79            = (k1_xboole_0)))),
% 9.56/9.79      inference('sup-', [status(thm)], ['120', '121'])).
% 9.56/9.79  thf('123', plain, (![X13 : $i]: (r1_tarski @ k1_xboole_0 @ X13)),
% 9.56/9.79      inference('cnf', [status(esa)], [t2_xboole_1])).
% 9.56/9.79  thf('124', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i]:
% 9.56/9.79         ((r1_tarski @ (k2_xboole_0 @ X0 @ X1) @ X0) | ~ (r1_tarski @ X1 @ X0))),
% 9.56/9.79      inference('sup-', [status(thm)], ['51', '52'])).
% 9.56/9.79  thf('125', plain,
% 9.56/9.79      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ X0)),
% 9.56/9.79      inference('sup-', [status(thm)], ['123', '124'])).
% 9.56/9.79  thf('126', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 9.56/9.79      inference('demod', [status(thm)], ['8', '9'])).
% 9.56/9.79  thf('127', plain,
% 9.56/9.79      (![X1 : $i, X3 : $i]:
% 9.56/9.79         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 9.56/9.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.56/9.79  thf('128', plain,
% 9.56/9.79      (![X0 : $i, X1 : $i]:
% 9.56/9.79         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 9.56/9.79          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 9.56/9.79      inference('sup-', [status(thm)], ['126', '127'])).
% 9.56/9.79  thf('129', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 9.56/9.79      inference('sup-', [status(thm)], ['125', '128'])).
% 9.56/9.79  thf('130', plain,
% 9.56/9.79      ((((k3_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 9.56/9.79        | ((k1_tarski @ (sk_C_1 @ k1_xboole_0)) = (k1_xboole_0)))),
% 9.56/9.79      inference('demod', [status(thm)], ['122', '129'])).
% 9.56/9.79  thf('131', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 9.56/9.79      inference('sup-', [status(thm)], ['56', '57'])).
% 9.56/9.79  thf('132', plain, (((k3_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 9.56/9.79      inference('simplify_reflect-', [status(thm)], ['130', '131'])).
% 9.56/9.79  thf('133', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 9.56/9.79      inference('sup-', [status(thm)], ['36', '41'])).
% 9.56/9.79  thf('134', plain,
% 9.56/9.79      (![X0 : $i]:
% 9.56/9.79         ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 9.56/9.79          | ~ (r1_tarski @ (k2_relat_1 @ sk_B_1) @ X0))),
% 9.56/9.79      inference('demod', [status(thm)], ['109', '132', '133'])).
% 9.56/9.79  thf('135', plain,
% 9.56/9.79      ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 9.56/9.79      inference('sup-', [status(thm)], ['85', '134'])).
% 9.56/9.79  thf('136', plain,
% 9.56/9.79      ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 9.56/9.79      inference('demod', [status(thm)], ['69', '70'])).
% 9.56/9.79  thf('137', plain,
% 9.56/9.79      (![X22 : $i, X23 : $i, X24 : $i]:
% 9.56/9.79         (~ (r1_tarski @ X22 @ X23)
% 9.56/9.79          | ~ (r1_tarski @ X24 @ X23)
% 9.56/9.79          | (r1_tarski @ (k2_xboole_0 @ X22 @ X24) @ X23))),
% 9.56/9.79      inference('cnf', [status(esa)], [t8_xboole_1])).
% 9.56/9.79  thf('138', plain,
% 9.56/9.79      (![X0 : $i]:
% 9.56/9.79         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 9.56/9.79           (k3_relat_1 @ sk_B_1))
% 9.56/9.79          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B_1)))),
% 9.56/9.79      inference('sup-', [status(thm)], ['136', '137'])).
% 9.56/9.79  thf('139', plain,
% 9.56/9.79      ((r1_tarski @ 
% 9.56/9.79        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 9.56/9.79        (k3_relat_1 @ sk_B_1))),
% 9.56/9.79      inference('sup-', [status(thm)], ['135', '138'])).
% 9.56/9.79  thf('140', plain,
% 9.56/9.79      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))
% 9.56/9.79        | ~ (v1_relat_1 @ sk_A))),
% 9.56/9.79      inference('sup+', [status(thm)], ['1', '139'])).
% 9.56/9.79  thf('141', plain, ((v1_relat_1 @ sk_A)),
% 9.56/9.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.56/9.79  thf('142', plain,
% 9.56/9.79      ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B_1))),
% 9.56/9.79      inference('demod', [status(thm)], ['140', '141'])).
% 9.56/9.79  thf('143', plain, ($false), inference('demod', [status(thm)], ['0', '142'])).
% 9.56/9.79  
% 9.56/9.79  % SZS output end Refutation
% 9.56/9.79  
% 9.63/9.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
