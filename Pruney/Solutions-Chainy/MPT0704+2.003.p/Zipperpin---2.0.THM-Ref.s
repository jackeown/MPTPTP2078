%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R962XeIOlj

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 168 expanded)
%              Number of leaves         :   18 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  677 (1847 expanded)
%              Number of equality atoms :   28 (  53 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t159_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i] :
          ? [C: $i] :
            ( r1_tarski @ ( k10_relat_1 @ A @ ( k1_tarski @ B ) ) @ ( k1_tarski @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v2_funct_1 @ A )
        <=> ! [B: $i] :
            ? [C: $i] :
              ( r1_tarski @ ( k10_relat_1 @ A @ ( k1_tarski @ B ) ) @ ( k1_tarski @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t159_funct_1])).

thf('0',plain,(
    ! [X9: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X9 ) ) @ ( k1_tarski @ ( sk_C_1 @ X9 ) ) )
      | ( v2_funct_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v2_funct_1 @ sk_A )
   <= ( v2_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t142_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
      <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
         != k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k10_relat_1 @ X3 @ ( k1_tarski @ X4 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X4 @ ( k2_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t142_funct_1])).

thf('3',plain,(
    ! [X8: $i] :
      ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X8 ) )
      | ~ ( v2_funct_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ! [X8: $i] :
        ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X8 ) )
   <= ! [X8: $i] :
        ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X8 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
        | ~ ( v1_relat_1 @ sk_A )
        | ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) ) )
   <= ! [X8: $i] :
        ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X8 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ ( k1_tarski @ X2 ) )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('7',plain,(
    ! [X2: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X2 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ sk_B_1 @ ( k2_relat_1 @ sk_A ) )
   <= ! [X8: $i] :
        ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X8 ) ) ),
    inference(demod,[status(thm)],['5','7','8'])).

thf(t144_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k2_relat_1 @ A ) )
              & ! [C: $i] :
                  ( ( k10_relat_1 @ A @ ( k1_tarski @ B ) )
                 != ( k1_tarski @ C ) ) )
      <=> ( v2_funct_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_relat_1 @ X5 ) )
      | ( ( k10_relat_1 @ X5 @ ( k1_tarski @ X6 ) )
        = ( k1_tarski @ ( sk_C @ X6 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t144_funct_1])).

thf('11',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ! [X8: $i] :
        ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X8 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
        = ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) )
      | ~ ( v2_funct_1 @ sk_A ) )
   <= ! [X8: $i] :
        ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X8 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( ! [X8: $i] :
          ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X8 ) )
      & ( v2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,
    ( ! [X8: $i] :
        ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X8 ) )
   <= ! [X8: $i] :
        ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X8 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
   <= ( ! [X8: $i] :
          ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X8 ) )
      & ( v2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( ! [X8: $i] :
          ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X8 ) )
      & ( v2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('19',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ ( k1_tarski @ X2 ) )
      | ( X1
       != ( k1_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('20',plain,(
    ! [X2: $i] :
      ( r1_tarski @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X2 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( r1_tarski @ ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
   <= ( ! [X8: $i] :
          ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X8 ) )
      & ( v2_funct_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('22',plain,
    ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = ( k1_tarski @ ( sk_C @ sk_B_1 @ sk_A ) ) )
   <= ( ! [X8: $i] :
          ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X8 ) )
      & ( v2_funct_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('23',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
   <= ( ! [X8: $i] :
          ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X8 ) )
      & ( v2_funct_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v2_funct_1 @ sk_A )
    | ~ ! [X8: $i] :
          ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X8 ) ) ),
    inference(demod,[status(thm)],['17','23'])).

thf('25',plain,
    ( ! [X9: $i] :
        ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X9 ) ) @ ( k1_tarski @ ( sk_C_1 @ X9 ) ) )
   <= ! [X9: $i] :
        ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X9 ) ) @ ( k1_tarski @ ( sk_C_1 @ X9 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ! [X8: $i] :
        ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X8 ) )
   <= ! [X8: $i] :
        ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X8 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('27',plain,
    ( ~ ! [X9: $i] :
          ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X9 ) ) @ ( k1_tarski @ ( sk_C_1 @ X9 ) ) )
    | ~ ! [X8: $i] :
          ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X8 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( v2_funct_1 @ sk_A )
    | ! [X8: $i] :
        ~ ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) @ ( k1_tarski @ X8 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('29',plain,
    ( ! [X9: $i] :
        ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X9 ) ) @ ( k1_tarski @ ( sk_C_1 @ X9 ) ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( ! [X9: $i] :
        ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X9 ) ) @ ( k1_tarski @ ( sk_C_1 @ X9 ) ) )
   <= ! [X9: $i] :
        ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X9 ) ) @ ( k1_tarski @ ( sk_C_1 @ X9 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X0 ) )
          = k1_xboole_0 )
        | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ X0 ) )
          = ( k1_tarski @ ( sk_C_1 @ X0 ) ) ) )
   <= ! [X9: $i] :
        ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X9 ) ) @ ( k1_tarski @ ( sk_C_1 @ X9 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X5: $i,X7: $i] :
      ( ( ( k10_relat_1 @ X5 @ ( k1_tarski @ ( sk_B @ X5 ) ) )
       != ( k1_tarski @ X7 ) )
      | ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t144_funct_1])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( ( k1_tarski @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
         != ( k1_tarski @ X0 ) )
        | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ ( sk_B @ sk_A ) ) )
          = k1_xboole_0 )
        | ~ ( v1_relat_1 @ sk_A )
        | ~ ( v1_funct_1 @ sk_A )
        | ( v2_funct_1 @ sk_A ) )
   <= ! [X9: $i] :
        ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X9 ) ) @ ( k1_tarski @ ( sk_C_1 @ X9 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( ( k1_tarski @ ( sk_C_1 @ ( sk_B @ sk_A ) ) )
         != ( k1_tarski @ X0 ) )
        | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ ( sk_B @ sk_A ) ) )
          = k1_xboole_0 )
        | ( v2_funct_1 @ sk_A ) )
   <= ! [X9: $i] :
        ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X9 ) ) @ ( k1_tarski @ ( sk_C_1 @ X9 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( ( v2_funct_1 @ sk_A )
      | ( ( k10_relat_1 @ sk_A @ ( k1_tarski @ ( sk_B @ sk_A ) ) )
        = k1_xboole_0 ) )
   <= ! [X9: $i] :
        ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X9 ) ) @ ( k1_tarski @ ( sk_C_1 @ X9 ) ) ) ),
    inference(eq_res,[status(thm)],['37'])).

thf('39',plain,(
    ! [X5: $i] :
      ( ( r2_hidden @ ( sk_B @ X5 ) @ ( k2_relat_1 @ X5 ) )
      | ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t144_funct_1])).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k2_relat_1 @ X3 ) )
      | ( ( k10_relat_1 @ X3 @ ( k1_tarski @ X4 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t142_funct_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
       != k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_funct_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_A )
      | ( v2_funct_1 @ sk_A ) )
   <= ! [X9: $i] :
        ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X9 ) ) @ ( k1_tarski @ ( sk_C_1 @ X9 ) ) ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_funct_1 @ sk_A )
      | ( v2_funct_1 @ sk_A ) )
   <= ! [X9: $i] :
        ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X9 ) ) @ ( k1_tarski @ ( sk_C_1 @ X9 ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( v2_funct_1 @ sk_A )
   <= ! [X9: $i] :
        ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X9 ) ) @ ( k1_tarski @ ( sk_C_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( v2_funct_1 @ sk_A )
   <= ~ ( v2_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('49',plain,
    ( ~ ! [X9: $i] :
          ( r1_tarski @ ( k10_relat_1 @ sk_A @ ( k1_tarski @ X9 ) ) @ ( k1_tarski @ ( sk_C_1 @ X9 ) ) )
    | ( v2_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['24','27','28','29','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R962XeIOlj
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:16:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 44 iterations in 0.025s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.22/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.49  thf(t159_funct_1, conjecture,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.49       ( ( v2_funct_1 @ A ) <=>
% 0.22/0.49         ( ![B:$i]:
% 0.22/0.49           ( ?[C:$i]:
% 0.22/0.49             ( r1_tarski @
% 0.22/0.49               ( k10_relat_1 @ A @ ( k1_tarski @ B ) ) @ ( k1_tarski @ C ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]:
% 0.22/0.49        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.49          ( ( v2_funct_1 @ A ) <=>
% 0.22/0.49            ( ![B:$i]:
% 0.22/0.49              ( ?[C:$i]:
% 0.22/0.49                ( r1_tarski @
% 0.22/0.49                  ( k10_relat_1 @ A @ ( k1_tarski @ B ) ) @ ( k1_tarski @ C ) ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t159_funct_1])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (![X9 : $i]:
% 0.22/0.49         ((r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ X9)) @ 
% 0.22/0.49           (k1_tarski @ (sk_C_1 @ X9)))
% 0.22/0.49          | (v2_funct_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('1', plain, (((v2_funct_1 @ sk_A)) <= (((v2_funct_1 @ sk_A)))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf(t142_funct_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ B ) =>
% 0.22/0.49       ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.22/0.49         ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i]:
% 0.22/0.49         (((k10_relat_1 @ X3 @ (k1_tarski @ X4)) = (k1_xboole_0))
% 0.22/0.49          | (r2_hidden @ X4 @ (k2_relat_1 @ X3))
% 0.22/0.49          | ~ (v1_relat_1 @ X3))),
% 0.22/0.49      inference('cnf', [status(esa)], [t142_funct_1])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X8 : $i]:
% 0.22/0.49         (~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.22/0.49             (k1_tarski @ X8))
% 0.22/0.49          | ~ (v2_funct_1 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      ((![X8 : $i]:
% 0.22/0.49          ~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.22/0.49             (k1_tarski @ X8)))
% 0.22/0.49         <= ((![X8 : $i]:
% 0.22/0.49                ~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.22/0.49                   (k1_tarski @ X8))))),
% 0.22/0.49      inference('split', [status(esa)], ['3'])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      ((![X0 : $i]:
% 0.22/0.49          (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.22/0.49           | ~ (v1_relat_1 @ sk_A)
% 0.22/0.49           | (r2_hidden @ sk_B_1 @ (k2_relat_1 @ sk_A))))
% 0.22/0.49         <= ((![X8 : $i]:
% 0.22/0.49                ~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.22/0.49                   (k1_tarski @ X8))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '4'])).
% 0.22/0.49  thf(l3_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.22/0.49       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X1 : $i, X2 : $i]:
% 0.22/0.49         ((r1_tarski @ X1 @ (k1_tarski @ X2)) | ((X1) != (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.22/0.49  thf('7', plain, (![X2 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X2))),
% 0.22/0.49      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.49  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (((r2_hidden @ sk_B_1 @ (k2_relat_1 @ sk_A)))
% 0.22/0.49         <= ((![X8 : $i]:
% 0.22/0.49                ~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.22/0.49                   (k1_tarski @ X8))))),
% 0.22/0.49      inference('demod', [status(thm)], ['5', '7', '8'])).
% 0.22/0.49  thf(t144_funct_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.49       ( ( ![B:$i]:
% 0.22/0.49           ( ~( ( r2_hidden @ B @ ( k2_relat_1 @ A ) ) & 
% 0.22/0.49                ( ![C:$i]:
% 0.22/0.49                  ( ( k10_relat_1 @ A @ ( k1_tarski @ B ) ) !=
% 0.22/0.49                    ( k1_tarski @ C ) ) ) ) ) ) <=>
% 0.22/0.49         ( v2_funct_1 @ A ) ) ))).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i]:
% 0.22/0.49         (~ (v2_funct_1 @ X5)
% 0.22/0.49          | ~ (r2_hidden @ X6 @ (k2_relat_1 @ X5))
% 0.22/0.49          | ((k10_relat_1 @ X5 @ (k1_tarski @ X6))
% 0.22/0.49              = (k1_tarski @ (sk_C @ X6 @ X5)))
% 0.22/0.49          | ~ (v1_funct_1 @ X5)
% 0.22/0.49          | ~ (v1_relat_1 @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [t144_funct_1])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (((~ (v1_relat_1 @ sk_A)
% 0.22/0.49         | ~ (v1_funct_1 @ sk_A)
% 0.22/0.49         | ((k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.22/0.49             = (k1_tarski @ (sk_C @ sk_B_1 @ sk_A)))
% 0.22/0.49         | ~ (v2_funct_1 @ sk_A)))
% 0.22/0.49         <= ((![X8 : $i]:
% 0.22/0.49                ~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.22/0.49                   (k1_tarski @ X8))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('12', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('13', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (((((k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.22/0.49           = (k1_tarski @ (sk_C @ sk_B_1 @ sk_A)))
% 0.22/0.49         | ~ (v2_funct_1 @ sk_A)))
% 0.22/0.49         <= ((![X8 : $i]:
% 0.22/0.49                ~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.22/0.49                   (k1_tarski @ X8))))),
% 0.22/0.49      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      ((((k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.22/0.49          = (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))))
% 0.22/0.49         <= ((![X8 : $i]:
% 0.22/0.49                ~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.22/0.49                   (k1_tarski @ X8))) & 
% 0.22/0.49             ((v2_funct_1 @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '14'])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      ((![X8 : $i]:
% 0.22/0.49          ~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.22/0.49             (k1_tarski @ X8)))
% 0.22/0.49         <= ((![X8 : $i]:
% 0.22/0.49                ~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.22/0.49                   (k1_tarski @ X8))))),
% 0.22/0.49      inference('split', [status(esa)], ['3'])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      ((~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.22/0.49           (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1))))
% 0.22/0.49         <= ((![X8 : $i]:
% 0.22/0.49                ~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.22/0.49                   (k1_tarski @ X8))) & 
% 0.22/0.49             ((v2_funct_1 @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      ((((k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.22/0.49          = (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))))
% 0.22/0.49         <= ((![X8 : $i]:
% 0.22/0.49                ~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.22/0.49                   (k1_tarski @ X8))) & 
% 0.22/0.49             ((v2_funct_1 @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '14'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X1 : $i, X2 : $i]:
% 0.22/0.49         ((r1_tarski @ X1 @ (k1_tarski @ X2)) | ((X1) != (k1_tarski @ X2)))),
% 0.22/0.49      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (![X2 : $i]: (r1_tarski @ (k1_tarski @ X2) @ (k1_tarski @ X2))),
% 0.22/0.49      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (((r1_tarski @ (k1_tarski @ (sk_C @ sk_B_1 @ sk_A)) @ 
% 0.22/0.49         (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1))))
% 0.22/0.49         <= ((![X8 : $i]:
% 0.22/0.49                ~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.22/0.49                   (k1_tarski @ X8))) & 
% 0.22/0.49             ((v2_funct_1 @ sk_A)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['18', '20'])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      ((((k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1))
% 0.22/0.49          = (k1_tarski @ (sk_C @ sk_B_1 @ sk_A))))
% 0.22/0.49         <= ((![X8 : $i]:
% 0.22/0.49                ~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.22/0.49                   (k1_tarski @ X8))) & 
% 0.22/0.49             ((v2_funct_1 @ sk_A)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '14'])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (((r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.22/0.49         (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1))))
% 0.22/0.49         <= ((![X8 : $i]:
% 0.22/0.49                ~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.22/0.49                   (k1_tarski @ X8))) & 
% 0.22/0.49             ((v2_funct_1 @ sk_A)))),
% 0.22/0.49      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (~ ((v2_funct_1 @ sk_A)) | 
% 0.22/0.49       ~
% 0.22/0.49       (![X8 : $i]:
% 0.22/0.49          ~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.22/0.49             (k1_tarski @ X8)))),
% 0.22/0.49      inference('demod', [status(thm)], ['17', '23'])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      ((![X9 : $i]:
% 0.22/0.49          (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ X9)) @ 
% 0.22/0.49           (k1_tarski @ (sk_C_1 @ X9))))
% 0.22/0.49         <= ((![X9 : $i]:
% 0.22/0.49                (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ X9)) @ 
% 0.22/0.49                 (k1_tarski @ (sk_C_1 @ X9)))))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      ((![X8 : $i]:
% 0.22/0.49          ~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.22/0.49             (k1_tarski @ X8)))
% 0.22/0.49         <= ((![X8 : $i]:
% 0.22/0.49                ~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.22/0.49                   (k1_tarski @ X8))))),
% 0.22/0.49      inference('split', [status(esa)], ['3'])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (~
% 0.22/0.49       (![X9 : $i]:
% 0.22/0.49          (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ X9)) @ 
% 0.22/0.49           (k1_tarski @ (sk_C_1 @ X9)))) | 
% 0.22/0.49       ~
% 0.22/0.49       (![X8 : $i]:
% 0.22/0.49          ~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.22/0.49             (k1_tarski @ X8)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (~ ((v2_funct_1 @ sk_A)) | 
% 0.22/0.49       (![X8 : $i]:
% 0.22/0.49          ~ (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ sk_B_1)) @ 
% 0.22/0.49             (k1_tarski @ X8)))),
% 0.22/0.49      inference('split', [status(esa)], ['3'])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      ((![X9 : $i]:
% 0.22/0.49          (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ X9)) @ 
% 0.22/0.49           (k1_tarski @ (sk_C_1 @ X9)))) | 
% 0.22/0.49       ((v2_funct_1 @ sk_A))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      ((![X9 : $i]:
% 0.22/0.49          (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ X9)) @ 
% 0.22/0.49           (k1_tarski @ (sk_C_1 @ X9))))
% 0.22/0.49         <= ((![X9 : $i]:
% 0.22/0.49                (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ X9)) @ 
% 0.22/0.49                 (k1_tarski @ (sk_C_1 @ X9)))))),
% 0.22/0.49      inference('split', [status(esa)], ['0'])).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((X1) = (k1_tarski @ X0))
% 0.22/0.49          | ((X1) = (k1_xboole_0))
% 0.22/0.49          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      ((![X0 : $i]:
% 0.22/0.49          (((k10_relat_1 @ sk_A @ (k1_tarski @ X0)) = (k1_xboole_0))
% 0.22/0.49           | ((k10_relat_1 @ sk_A @ (k1_tarski @ X0))
% 0.22/0.49               = (k1_tarski @ (sk_C_1 @ X0)))))
% 0.22/0.49         <= ((![X9 : $i]:
% 0.22/0.49                (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ X9)) @ 
% 0.22/0.49                 (k1_tarski @ (sk_C_1 @ X9)))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      (![X5 : $i, X7 : $i]:
% 0.22/0.49         (((k10_relat_1 @ X5 @ (k1_tarski @ (sk_B @ X5))) != (k1_tarski @ X7))
% 0.22/0.49          | (v2_funct_1 @ X5)
% 0.22/0.49          | ~ (v1_funct_1 @ X5)
% 0.22/0.49          | ~ (v1_relat_1 @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [t144_funct_1])).
% 0.22/0.49  thf('34', plain,
% 0.22/0.49      ((![X0 : $i]:
% 0.22/0.49          (((k1_tarski @ (sk_C_1 @ (sk_B @ sk_A))) != (k1_tarski @ X0))
% 0.22/0.49           | ((k10_relat_1 @ sk_A @ (k1_tarski @ (sk_B @ sk_A)))
% 0.22/0.49               = (k1_xboole_0))
% 0.22/0.49           | ~ (v1_relat_1 @ sk_A)
% 0.22/0.49           | ~ (v1_funct_1 @ sk_A)
% 0.22/0.49           | (v2_funct_1 @ sk_A)))
% 0.22/0.49         <= ((![X9 : $i]:
% 0.22/0.49                (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ X9)) @ 
% 0.22/0.49                 (k1_tarski @ (sk_C_1 @ X9)))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.49  thf('35', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('36', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('37', plain,
% 0.22/0.49      ((![X0 : $i]:
% 0.22/0.49          (((k1_tarski @ (sk_C_1 @ (sk_B @ sk_A))) != (k1_tarski @ X0))
% 0.22/0.49           | ((k10_relat_1 @ sk_A @ (k1_tarski @ (sk_B @ sk_A)))
% 0.22/0.49               = (k1_xboole_0))
% 0.22/0.49           | (v2_funct_1 @ sk_A)))
% 0.22/0.49         <= ((![X9 : $i]:
% 0.22/0.49                (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ X9)) @ 
% 0.22/0.49                 (k1_tarski @ (sk_C_1 @ X9)))))),
% 0.22/0.49      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.22/0.49  thf('38', plain,
% 0.22/0.49      ((((v2_funct_1 @ sk_A)
% 0.22/0.49         | ((k10_relat_1 @ sk_A @ (k1_tarski @ (sk_B @ sk_A))) = (k1_xboole_0))))
% 0.22/0.49         <= ((![X9 : $i]:
% 0.22/0.49                (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ X9)) @ 
% 0.22/0.49                 (k1_tarski @ (sk_C_1 @ X9)))))),
% 0.22/0.49      inference('eq_res', [status(thm)], ['37'])).
% 0.22/0.49  thf('39', plain,
% 0.22/0.49      (![X5 : $i]:
% 0.22/0.49         ((r2_hidden @ (sk_B @ X5) @ (k2_relat_1 @ X5))
% 0.22/0.49          | (v2_funct_1 @ X5)
% 0.22/0.49          | ~ (v1_funct_1 @ X5)
% 0.22/0.49          | ~ (v1_relat_1 @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [t144_funct_1])).
% 0.22/0.49  thf('40', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X4 @ (k2_relat_1 @ X3))
% 0.22/0.49          | ((k10_relat_1 @ X3 @ (k1_tarski @ X4)) != (k1_xboole_0))
% 0.22/0.49          | ~ (v1_relat_1 @ X3))),
% 0.22/0.49      inference('cnf', [status(esa)], [t142_funct_1])).
% 0.22/0.49  thf('41', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X0)
% 0.22/0.49          | ~ (v1_funct_1 @ X0)
% 0.22/0.49          | (v2_funct_1 @ X0)
% 0.22/0.49          | ~ (v1_relat_1 @ X0)
% 0.22/0.49          | ((k10_relat_1 @ X0 @ (k1_tarski @ (sk_B @ X0))) != (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.49  thf('42', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k10_relat_1 @ X0 @ (k1_tarski @ (sk_B @ X0))) != (k1_xboole_0))
% 0.22/0.49          | (v2_funct_1 @ X0)
% 0.22/0.49          | ~ (v1_funct_1 @ X0)
% 0.22/0.49          | ~ (v1_relat_1 @ X0))),
% 0.22/0.49      inference('simplify', [status(thm)], ['41'])).
% 0.22/0.49  thf('43', plain,
% 0.22/0.49      (((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.49         | (v2_funct_1 @ sk_A)
% 0.22/0.49         | ~ (v1_relat_1 @ sk_A)
% 0.22/0.49         | ~ (v1_funct_1 @ sk_A)
% 0.22/0.49         | (v2_funct_1 @ sk_A)))
% 0.22/0.49         <= ((![X9 : $i]:
% 0.22/0.49                (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ X9)) @ 
% 0.22/0.49                 (k1_tarski @ (sk_C_1 @ X9)))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['38', '42'])).
% 0.22/0.49  thf('44', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('45', plain, ((v1_funct_1 @ sk_A)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('46', plain,
% 0.22/0.49      (((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.49         | (v2_funct_1 @ sk_A)
% 0.22/0.49         | (v2_funct_1 @ sk_A)))
% 0.22/0.49         <= ((![X9 : $i]:
% 0.22/0.49                (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ X9)) @ 
% 0.22/0.49                 (k1_tarski @ (sk_C_1 @ X9)))))),
% 0.22/0.49      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.22/0.49  thf('47', plain,
% 0.22/0.49      (((v2_funct_1 @ sk_A))
% 0.22/0.49         <= ((![X9 : $i]:
% 0.22/0.49                (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ X9)) @ 
% 0.22/0.49                 (k1_tarski @ (sk_C_1 @ X9)))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['46'])).
% 0.22/0.49  thf('48', plain, ((~ (v2_funct_1 @ sk_A)) <= (~ ((v2_funct_1 @ sk_A)))),
% 0.22/0.49      inference('split', [status(esa)], ['3'])).
% 0.22/0.49  thf('49', plain,
% 0.22/0.49      (~
% 0.22/0.49       (![X9 : $i]:
% 0.22/0.49          (r1_tarski @ (k10_relat_1 @ sk_A @ (k1_tarski @ X9)) @ 
% 0.22/0.49           (k1_tarski @ (sk_C_1 @ X9)))) | 
% 0.22/0.49       ((v2_funct_1 @ sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.22/0.49  thf('50', plain, ($false),
% 0.22/0.49      inference('sat_resolution*', [status(thm)],
% 0.22/0.49                ['24', '27', '28', '29', '49'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
