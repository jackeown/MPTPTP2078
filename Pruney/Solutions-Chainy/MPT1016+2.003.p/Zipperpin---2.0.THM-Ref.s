%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.opWa40EUa9

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 915 expanded)
%              Number of leaves         :   31 ( 268 expanded)
%              Depth                    :   26
%              Number of atoms          : 1017 (14688 expanded)
%              Number of equality atoms :   87 ( 955 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(t77_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v2_funct_1 @ B )
      <=> ! [C: $i,D: $i] :
            ( ( ( r2_hidden @ C @ A )
              & ( r2_hidden @ D @ A )
              & ( ( k1_funct_1 @ B @ C )
                = ( k1_funct_1 @ B @ D ) ) )
           => ( C = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( v2_funct_1 @ B )
        <=> ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A )
                & ( ( k1_funct_1 @ B @ C )
                  = ( k1_funct_1 @ B @ D ) ) )
             => ( C = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_funct_2])).

thf('0',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
   <= ( r2_hidden @ sk_C_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
   <= ( r2_hidden @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X23 = X22 )
      | ( ( k1_funct_1 @ sk_B_2 @ X23 )
       != ( k1_funct_1 @ sk_B_2 @ X22 ) )
      | ~ ( r2_hidden @ X22 @ sk_A )
      | ~ ( r2_hidden @ X23 @ sk_A )
      | ( v2_funct_1 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_funct_1 @ sk_B_2 )
    | ! [X22: $i,X23: $i] :
        ( ( X23 = X22 )
        | ( ( k1_funct_1 @ sk_B_2 @ X23 )
         != ( k1_funct_1 @ sk_B_2 @ X22 ) )
        | ~ ( r2_hidden @ X22 @ sk_A )
        | ~ ( r2_hidden @ X23 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf(d8_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
              & ( ( k1_funct_1 @ A @ B )
                = ( k1_funct_1 @ A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('6',plain,(
    ! [X9: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X9 ) @ ( k1_relat_1 @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('7',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v4_relat_1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('9',plain,(
    v4_relat_1 @ sk_B_2 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v4_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k1_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_B_2 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B_2 ) @ sk_A ),
    inference(demod,[status(thm)],['11','14'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_B_2 )
    | ( v2_funct_1 @ sk_B_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('20',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_funct_1 @ sk_B_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X9: $i] :
      ( ( ( k1_funct_1 @ X9 @ ( sk_B_1 @ X9 ) )
        = ( k1_funct_1 @ X9 @ ( sk_C_1 @ X9 ) ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('23',plain,
    ( ! [X22: $i,X23: $i] :
        ( ( X23 = X22 )
        | ( ( k1_funct_1 @ sk_B_2 @ X23 )
         != ( k1_funct_1 @ sk_B_2 @ X22 ) )
        | ~ ( r2_hidden @ X22 @ sk_A )
        | ~ ( r2_hidden @ X23 @ sk_A ) )
   <= ! [X22: $i,X23: $i] :
        ( ( X23 = X22 )
        | ( ( k1_funct_1 @ sk_B_2 @ X23 )
         != ( k1_funct_1 @ sk_B_2 @ X22 ) )
        | ~ ( r2_hidden @ X22 @ sk_A )
        | ~ ( r2_hidden @ X23 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_2 @ X0 )
         != ( k1_funct_1 @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) ) )
        | ~ ( v1_relat_1 @ sk_B_2 )
        | ~ ( v1_funct_1 @ sk_B_2 )
        | ( v2_funct_1 @ sk_B_2 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C_1 @ sk_B_2 ) @ sk_A )
        | ( X0
          = ( sk_C_1 @ sk_B_2 ) ) )
   <= ! [X22: $i,X23: $i] :
        ( ( X23 = X22 )
        | ( ( k1_funct_1 @ sk_B_2 @ X23 )
         != ( k1_funct_1 @ sk_B_2 @ X22 ) )
        | ~ ( r2_hidden @ X22 @ sk_A )
        | ~ ( r2_hidden @ X23 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('26',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_2 @ X0 )
         != ( k1_funct_1 @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) ) )
        | ( v2_funct_1 @ sk_B_2 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C_1 @ sk_B_2 ) @ sk_A )
        | ( X0
          = ( sk_C_1 @ sk_B_2 ) ) )
   <= ! [X22: $i,X23: $i] :
        ( ( X23 = X22 )
        | ( ( k1_funct_1 @ sk_B_2 @ X23 )
         != ( k1_funct_1 @ sk_B_2 @ X22 ) )
        | ~ ( r2_hidden @ X22 @ sk_A )
        | ~ ( r2_hidden @ X23 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( v2_funct_1 @ sk_B_2 )
        | ( X0
          = ( sk_C_1 @ sk_B_2 ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( v2_funct_1 @ sk_B_2 )
        | ( ( k1_funct_1 @ sk_B_2 @ X0 )
         != ( k1_funct_1 @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) ) ) )
   <= ! [X22: $i,X23: $i] :
        ( ( X23 = X22 )
        | ( ( k1_funct_1 @ sk_B_2 @ X23 )
         != ( k1_funct_1 @ sk_B_2 @ X22 ) )
        | ~ ( r2_hidden @ X22 @ sk_A )
        | ~ ( r2_hidden @ X23 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_2 @ X0 )
         != ( k1_funct_1 @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( X0
          = ( sk_C_1 @ sk_B_2 ) )
        | ( v2_funct_1 @ sk_B_2 ) )
   <= ! [X22: $i,X23: $i] :
        ( ( X23 = X22 )
        | ( ( k1_funct_1 @ sk_B_2 @ X23 )
         != ( k1_funct_1 @ sk_B_2 @ X22 ) )
        | ~ ( r2_hidden @ X22 @ sk_A )
        | ~ ( r2_hidden @ X23 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ( v2_funct_1 @ sk_B_2 )
      | ( ( sk_B_1 @ sk_B_2 )
        = ( sk_C_1 @ sk_B_2 ) )
      | ~ ( r2_hidden @ ( sk_B_1 @ sk_B_2 ) @ sk_A ) )
   <= ! [X22: $i,X23: $i] :
        ( ( X23 = X22 )
        | ( ( k1_funct_1 @ sk_B_2 @ X23 )
         != ( k1_funct_1 @ sk_B_2 @ X22 ) )
        | ~ ( r2_hidden @ X22 @ sk_A )
        | ~ ( r2_hidden @ X23 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['29'])).

thf('31',plain,(
    ! [X9: $i] :
      ( ( r2_hidden @ ( sk_B_1 @ X9 ) @ ( k1_relat_1 @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_B_2 )
    | ( v2_funct_1 @ sk_B_2 )
    | ( r2_hidden @ ( sk_B_1 @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('35',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_funct_1 @ sk_B_2 )
    | ( r2_hidden @ ( sk_B_1 @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( ( ( sk_B_1 @ sk_B_2 )
        = ( sk_C_1 @ sk_B_2 ) )
      | ( v2_funct_1 @ sk_B_2 ) )
   <= ! [X22: $i,X23: $i] :
        ( ( X23 = X22 )
        | ( ( k1_funct_1 @ sk_B_2 @ X23 )
         != ( k1_funct_1 @ sk_B_2 @ X22 ) )
        | ~ ( r2_hidden @ X22 @ sk_A )
        | ~ ( r2_hidden @ X23 @ sk_A ) ) ),
    inference(clc,[status(thm)],['30','36'])).

thf('38',plain,
    ( ~ ( v2_funct_1 @ sk_B_2 )
   <= ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ( ( sk_B_1 @ sk_B_2 )
      = ( sk_C_1 @ sk_B_2 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_2 )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ( ( k1_funct_1 @ sk_B_2 @ X23 )
           != ( k1_funct_1 @ sk_B_2 @ X22 ) )
          | ~ ( r2_hidden @ X22 @ sk_A )
          | ~ ( r2_hidden @ X23 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X9: $i] :
      ( ( ( sk_B_1 @ X9 )
       != ( sk_C_1 @ X9 ) )
      | ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('41',plain,
    ( ( ( ( sk_B_1 @ sk_B_2 )
       != ( sk_B_1 @ sk_B_2 ) )
      | ~ ( v1_relat_1 @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_B_2 )
      | ( v2_funct_1 @ sk_B_2 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_2 )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ( ( k1_funct_1 @ sk_B_2 @ X23 )
           != ( k1_funct_1 @ sk_B_2 @ X22 ) )
          | ~ ( r2_hidden @ X22 @ sk_A )
          | ~ ( r2_hidden @ X23 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('43',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( ( sk_B_1 @ sk_B_2 )
       != ( sk_B_1 @ sk_B_2 ) )
      | ( v2_funct_1 @ sk_B_2 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_2 )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ( ( k1_funct_1 @ sk_B_2 @ X23 )
           != ( k1_funct_1 @ sk_B_2 @ X22 ) )
          | ~ ( r2_hidden @ X22 @ sk_A )
          | ~ ( r2_hidden @ X23 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( v2_funct_1 @ sk_B_2 )
   <= ( ~ ( v2_funct_1 @ sk_B_2 )
      & ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ( ( k1_funct_1 @ sk_B_2 @ X23 )
           != ( k1_funct_1 @ sk_B_2 @ X22 ) )
          | ~ ( r2_hidden @ X22 @ sk_A )
          | ~ ( r2_hidden @ X23 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ~ ( v2_funct_1 @ sk_B_2 )
   <= ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('47',plain,
    ( ~ ! [X22: $i,X23: $i] :
          ( ( X23 = X22 )
          | ( ( k1_funct_1 @ sk_B_2 @ X23 )
           != ( k1_funct_1 @ sk_B_2 @ X22 ) )
          | ~ ( r2_hidden @ X22 @ sk_A )
          | ~ ( r2_hidden @ X23 @ sk_A ) )
    | ( v2_funct_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','47','48'])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','49'])).

thf('51',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
   <= ( r2_hidden @ sk_C_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','47','48'])).

thf('53',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference(simpl_trail,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ D )
          & ( r2_hidden @ C @ A ) )
       => ( ( B = k1_xboole_0 )
          | ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) )
            = C ) ) ) ) )).

thf('55',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ( X20 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ X21 ) @ ( k1_funct_1 @ X21 @ X18 ) )
        = X18 )
      | ~ ( v2_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t32_funct_2])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B_2 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_2 ) @ ( k1_funct_1 @ sk_B_2 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_2 @ sk_B_2 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B_2 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_funct_2 @ sk_B_2 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B_2 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_2 ) @ ( k1_funct_1 @ sk_B_2 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( v2_funct_1 @ sk_B_2 )
   <= ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['4'])).

thf('61',plain,(
    v2_funct_1 @ sk_B_2 ),
    inference('sat_resolution*',[status(thm)],['5','47'])).

thf('62',plain,(
    v2_funct_1 @ sk_B_2 ),
    inference(simpl_trail,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_2 ) @ ( k1_funct_1 @ sk_B_2 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_2 ) @ ( k1_funct_1 @ sk_B_2 @ sk_C_2 ) )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['53','63'])).

thf('65',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
   <= ( r2_hidden @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['65'])).

thf('67',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['65'])).

thf('68',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','47','67'])).

thf('69',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['66','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_2 ) @ ( k1_funct_1 @ sk_B_2 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('71',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_2 ) @ ( k1_funct_1 @ sk_B_2 @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k1_funct_1 @ sk_B_2 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_2 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( k1_funct_1 @ sk_B_2 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_2 @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B_2 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_2 @ sk_D ) ) ),
    inference(split,[status(esa)],['72'])).

thf('74',plain,
    ( ( ( k1_funct_1 @ sk_B_2 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_2 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['72'])).

thf('75',plain,
    ( ( k1_funct_1 @ sk_B_2 @ sk_C_2 )
    = ( k1_funct_1 @ sk_B_2 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['5','47','74'])).

thf('76',plain,
    ( ( k1_funct_1 @ sk_B_2 @ sk_C_2 )
    = ( k1_funct_1 @ sk_B_2 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['73','75'])).

thf('77',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_2 ) @ ( k1_funct_1 @ sk_B_2 @ sk_C_2 ) )
      = sk_D ) ),
    inference(demod,[status(thm)],['71','76'])).

thf('78',plain,
    ( ( sk_C_2 = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','77'])).

thf('79',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( sk_C_2 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( sk_C_2 != sk_D )
   <= ( sk_C_2 != sk_D ) ),
    inference(split,[status(esa)],['80'])).

thf('82',plain,
    ( ( sk_C_2 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['80'])).

thf('83',plain,(
    sk_C_2 != sk_D ),
    inference('sat_resolution*',[status(thm)],['5','47','82'])).

thf('84',plain,(
    sk_C_2 != sk_D ),
    inference(simpl_trail,[status(thm)],['81','83'])).

thf('85',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['79','84'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('86',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['50','85','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.opWa40EUa9
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:36:29 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 92 iterations in 0.067s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.22/0.54  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.22/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.54  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.22/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.54  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.54  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.22/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.54  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.54  thf(t77_funct_2, conjecture,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.54         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.54       ( ( v2_funct_1 @ B ) <=>
% 0.22/0.54         ( ![C:$i,D:$i]:
% 0.22/0.54           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.22/0.54               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.22/0.54             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i,B:$i]:
% 0.22/0.54        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.54            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.54          ( ( v2_funct_1 @ B ) <=>
% 0.22/0.54            ( ![C:$i,D:$i]:
% 0.22/0.54              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.22/0.54                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.22/0.54                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t77_funct_2])).
% 0.22/0.54  thf('0', plain, (((r2_hidden @ sk_C_2 @ sk_A) | ~ (v2_funct_1 @ sk_B_2))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('1', plain,
% 0.22/0.54      (((r2_hidden @ sk_C_2 @ sk_A)) <= (((r2_hidden @ sk_C_2 @ sk_A)))),
% 0.22/0.54      inference('split', [status(esa)], ['0'])).
% 0.22/0.54  thf(d1_xboole_0, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.54  thf('3', plain,
% 0.22/0.54      ((~ (v1_xboole_0 @ sk_A)) <= (((r2_hidden @ sk_C_2 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.54  thf('4', plain,
% 0.22/0.54      (![X22 : $i, X23 : $i]:
% 0.22/0.54         (((X23) = (X22))
% 0.22/0.54          | ((k1_funct_1 @ sk_B_2 @ X23) != (k1_funct_1 @ sk_B_2 @ X22))
% 0.22/0.54          | ~ (r2_hidden @ X22 @ sk_A)
% 0.22/0.54          | ~ (r2_hidden @ X23 @ sk_A)
% 0.22/0.54          | (v2_funct_1 @ sk_B_2))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('5', plain,
% 0.22/0.54      (((v2_funct_1 @ sk_B_2)) | 
% 0.22/0.54       (![X22 : $i, X23 : $i]:
% 0.22/0.54          (((X23) = (X22))
% 0.22/0.54           | ((k1_funct_1 @ sk_B_2 @ X23) != (k1_funct_1 @ sk_B_2 @ X22))
% 0.22/0.54           | ~ (r2_hidden @ X22 @ sk_A)
% 0.22/0.54           | ~ (r2_hidden @ X23 @ sk_A)))),
% 0.22/0.54      inference('split', [status(esa)], ['4'])).
% 0.22/0.54  thf(d8_funct_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.54       ( ( v2_funct_1 @ A ) <=>
% 0.22/0.54         ( ![B:$i,C:$i]:
% 0.22/0.54           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.22/0.54               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.22/0.54               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.22/0.54             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.22/0.54  thf('6', plain,
% 0.22/0.54      (![X9 : $i]:
% 0.22/0.54         ((r2_hidden @ (sk_C_1 @ X9) @ (k1_relat_1 @ X9))
% 0.22/0.54          | (v2_funct_1 @ X9)
% 0.22/0.54          | ~ (v1_funct_1 @ X9)
% 0.22/0.54          | ~ (v1_relat_1 @ X9))),
% 0.22/0.54      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.22/0.54  thf('7', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(cc2_relset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.54  thf('8', plain,
% 0.22/0.54      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.54         ((v4_relat_1 @ X15 @ X16)
% 0.22/0.54          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.54  thf('9', plain, ((v4_relat_1 @ sk_B_2 @ sk_A)),
% 0.22/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.54  thf(d18_relat_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ B ) =>
% 0.22/0.54       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      (![X7 : $i, X8 : $i]:
% 0.22/0.54         (~ (v4_relat_1 @ X7 @ X8)
% 0.22/0.54          | (r1_tarski @ (k1_relat_1 @ X7) @ X8)
% 0.22/0.54          | ~ (v1_relat_1 @ X7))),
% 0.22/0.54      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      ((~ (v1_relat_1 @ sk_B_2) | (r1_tarski @ (k1_relat_1 @ sk_B_2) @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.54  thf('12', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(cc1_relset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.54       ( v1_relat_1 @ C ) ))).
% 0.22/0.54  thf('13', plain,
% 0.22/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.54         ((v1_relat_1 @ X12)
% 0.22/0.54          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.54  thf('14', plain, ((v1_relat_1 @ sk_B_2)),
% 0.22/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.54  thf('15', plain, ((r1_tarski @ (k1_relat_1 @ sk_B_2) @ sk_A)),
% 0.22/0.54      inference('demod', [status(thm)], ['11', '14'])).
% 0.22/0.54  thf(d3_tarski, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X3 @ X4)
% 0.22/0.54          | (r2_hidden @ X3 @ X5)
% 0.22/0.54          | ~ (r1_tarski @ X4 @ X5))),
% 0.22/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_2)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.54  thf('18', plain,
% 0.22/0.54      ((~ (v1_relat_1 @ sk_B_2)
% 0.22/0.54        | ~ (v1_funct_1 @ sk_B_2)
% 0.22/0.54        | (v2_funct_1 @ sk_B_2)
% 0.22/0.54        | (r2_hidden @ (sk_C_1 @ sk_B_2) @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['6', '17'])).
% 0.22/0.54  thf('19', plain, ((v1_relat_1 @ sk_B_2)),
% 0.22/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.54  thf('20', plain, ((v1_funct_1 @ sk_B_2)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      (((v2_funct_1 @ sk_B_2) | (r2_hidden @ (sk_C_1 @ sk_B_2) @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      (![X9 : $i]:
% 0.22/0.54         (((k1_funct_1 @ X9 @ (sk_B_1 @ X9))
% 0.22/0.54            = (k1_funct_1 @ X9 @ (sk_C_1 @ X9)))
% 0.22/0.54          | (v2_funct_1 @ X9)
% 0.22/0.54          | ~ (v1_funct_1 @ X9)
% 0.22/0.54          | ~ (v1_relat_1 @ X9))),
% 0.22/0.54      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      ((![X22 : $i, X23 : $i]:
% 0.22/0.54          (((X23) = (X22))
% 0.22/0.54           | ((k1_funct_1 @ sk_B_2 @ X23) != (k1_funct_1 @ sk_B_2 @ X22))
% 0.22/0.54           | ~ (r2_hidden @ X22 @ sk_A)
% 0.22/0.54           | ~ (r2_hidden @ X23 @ sk_A)))
% 0.22/0.54         <= ((![X22 : $i, X23 : $i]:
% 0.22/0.54                (((X23) = (X22))
% 0.22/0.54                 | ((k1_funct_1 @ sk_B_2 @ X23) != (k1_funct_1 @ sk_B_2 @ X22))
% 0.22/0.54                 | ~ (r2_hidden @ X22 @ sk_A)
% 0.22/0.54                 | ~ (r2_hidden @ X23 @ sk_A))))),
% 0.22/0.54      inference('split', [status(esa)], ['4'])).
% 0.22/0.54  thf('24', plain,
% 0.22/0.54      ((![X0 : $i]:
% 0.22/0.54          (((k1_funct_1 @ sk_B_2 @ X0)
% 0.22/0.54             != (k1_funct_1 @ sk_B_2 @ (sk_B_1 @ sk_B_2)))
% 0.22/0.54           | ~ (v1_relat_1 @ sk_B_2)
% 0.22/0.54           | ~ (v1_funct_1 @ sk_B_2)
% 0.22/0.54           | (v2_funct_1 @ sk_B_2)
% 0.22/0.54           | ~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.54           | ~ (r2_hidden @ (sk_C_1 @ sk_B_2) @ sk_A)
% 0.22/0.54           | ((X0) = (sk_C_1 @ sk_B_2))))
% 0.22/0.54         <= ((![X22 : $i, X23 : $i]:
% 0.22/0.54                (((X23) = (X22))
% 0.22/0.54                 | ((k1_funct_1 @ sk_B_2 @ X23) != (k1_funct_1 @ sk_B_2 @ X22))
% 0.22/0.54                 | ~ (r2_hidden @ X22 @ sk_A)
% 0.22/0.54                 | ~ (r2_hidden @ X23 @ sk_A))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.54  thf('25', plain, ((v1_relat_1 @ sk_B_2)),
% 0.22/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.54  thf('26', plain, ((v1_funct_1 @ sk_B_2)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('27', plain,
% 0.22/0.54      ((![X0 : $i]:
% 0.22/0.54          (((k1_funct_1 @ sk_B_2 @ X0)
% 0.22/0.54             != (k1_funct_1 @ sk_B_2 @ (sk_B_1 @ sk_B_2)))
% 0.22/0.54           | (v2_funct_1 @ sk_B_2)
% 0.22/0.54           | ~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.54           | ~ (r2_hidden @ (sk_C_1 @ sk_B_2) @ sk_A)
% 0.22/0.54           | ((X0) = (sk_C_1 @ sk_B_2))))
% 0.22/0.54         <= ((![X22 : $i, X23 : $i]:
% 0.22/0.54                (((X23) = (X22))
% 0.22/0.54                 | ((k1_funct_1 @ sk_B_2 @ X23) != (k1_funct_1 @ sk_B_2 @ X22))
% 0.22/0.54                 | ~ (r2_hidden @ X22 @ sk_A)
% 0.22/0.54                 | ~ (r2_hidden @ X23 @ sk_A))))),
% 0.22/0.54      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.22/0.54  thf('28', plain,
% 0.22/0.54      ((![X0 : $i]:
% 0.22/0.54          ((v2_funct_1 @ sk_B_2)
% 0.22/0.54           | ((X0) = (sk_C_1 @ sk_B_2))
% 0.22/0.54           | ~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.54           | (v2_funct_1 @ sk_B_2)
% 0.22/0.54           | ((k1_funct_1 @ sk_B_2 @ X0)
% 0.22/0.54               != (k1_funct_1 @ sk_B_2 @ (sk_B_1 @ sk_B_2)))))
% 0.22/0.54         <= ((![X22 : $i, X23 : $i]:
% 0.22/0.54                (((X23) = (X22))
% 0.22/0.54                 | ((k1_funct_1 @ sk_B_2 @ X23) != (k1_funct_1 @ sk_B_2 @ X22))
% 0.22/0.54                 | ~ (r2_hidden @ X22 @ sk_A)
% 0.22/0.54                 | ~ (r2_hidden @ X23 @ sk_A))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['21', '27'])).
% 0.22/0.54  thf('29', plain,
% 0.22/0.54      ((![X0 : $i]:
% 0.22/0.54          (((k1_funct_1 @ sk_B_2 @ X0)
% 0.22/0.54             != (k1_funct_1 @ sk_B_2 @ (sk_B_1 @ sk_B_2)))
% 0.22/0.54           | ~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.54           | ((X0) = (sk_C_1 @ sk_B_2))
% 0.22/0.54           | (v2_funct_1 @ sk_B_2)))
% 0.22/0.54         <= ((![X22 : $i, X23 : $i]:
% 0.22/0.54                (((X23) = (X22))
% 0.22/0.54                 | ((k1_funct_1 @ sk_B_2 @ X23) != (k1_funct_1 @ sk_B_2 @ X22))
% 0.22/0.54                 | ~ (r2_hidden @ X22 @ sk_A)
% 0.22/0.54                 | ~ (r2_hidden @ X23 @ sk_A))))),
% 0.22/0.55      inference('simplify', [status(thm)], ['28'])).
% 0.22/0.55  thf('30', plain,
% 0.22/0.55      ((((v2_funct_1 @ sk_B_2)
% 0.22/0.55         | ((sk_B_1 @ sk_B_2) = (sk_C_1 @ sk_B_2))
% 0.22/0.55         | ~ (r2_hidden @ (sk_B_1 @ sk_B_2) @ sk_A)))
% 0.22/0.55         <= ((![X22 : $i, X23 : $i]:
% 0.22/0.55                (((X23) = (X22))
% 0.22/0.55                 | ((k1_funct_1 @ sk_B_2 @ X23) != (k1_funct_1 @ sk_B_2 @ X22))
% 0.22/0.55                 | ~ (r2_hidden @ X22 @ sk_A)
% 0.22/0.55                 | ~ (r2_hidden @ X23 @ sk_A))))),
% 0.22/0.55      inference('eq_res', [status(thm)], ['29'])).
% 0.22/0.55  thf('31', plain,
% 0.22/0.55      (![X9 : $i]:
% 0.22/0.55         ((r2_hidden @ (sk_B_1 @ X9) @ (k1_relat_1 @ X9))
% 0.22/0.55          | (v2_funct_1 @ X9)
% 0.22/0.55          | ~ (v1_funct_1 @ X9)
% 0.22/0.55          | ~ (v1_relat_1 @ X9))),
% 0.22/0.55      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.22/0.55  thf('32', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_2)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.55  thf('33', plain,
% 0.22/0.55      ((~ (v1_relat_1 @ sk_B_2)
% 0.22/0.55        | ~ (v1_funct_1 @ sk_B_2)
% 0.22/0.55        | (v2_funct_1 @ sk_B_2)
% 0.22/0.55        | (r2_hidden @ (sk_B_1 @ sk_B_2) @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.55  thf('34', plain, ((v1_relat_1 @ sk_B_2)),
% 0.22/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.55  thf('35', plain, ((v1_funct_1 @ sk_B_2)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('36', plain,
% 0.22/0.55      (((v2_funct_1 @ sk_B_2) | (r2_hidden @ (sk_B_1 @ sk_B_2) @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.22/0.55  thf('37', plain,
% 0.22/0.55      (((((sk_B_1 @ sk_B_2) = (sk_C_1 @ sk_B_2)) | (v2_funct_1 @ sk_B_2)))
% 0.22/0.55         <= ((![X22 : $i, X23 : $i]:
% 0.22/0.55                (((X23) = (X22))
% 0.22/0.55                 | ((k1_funct_1 @ sk_B_2 @ X23) != (k1_funct_1 @ sk_B_2 @ X22))
% 0.22/0.55                 | ~ (r2_hidden @ X22 @ sk_A)
% 0.22/0.55                 | ~ (r2_hidden @ X23 @ sk_A))))),
% 0.22/0.55      inference('clc', [status(thm)], ['30', '36'])).
% 0.22/0.55  thf('38', plain, ((~ (v2_funct_1 @ sk_B_2)) <= (~ ((v2_funct_1 @ sk_B_2)))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf('39', plain,
% 0.22/0.55      ((((sk_B_1 @ sk_B_2) = (sk_C_1 @ sk_B_2)))
% 0.22/0.55         <= (~ ((v2_funct_1 @ sk_B_2)) & 
% 0.22/0.55             (![X22 : $i, X23 : $i]:
% 0.22/0.55                (((X23) = (X22))
% 0.22/0.55                 | ((k1_funct_1 @ sk_B_2 @ X23) != (k1_funct_1 @ sk_B_2 @ X22))
% 0.22/0.55                 | ~ (r2_hidden @ X22 @ sk_A)
% 0.22/0.55                 | ~ (r2_hidden @ X23 @ sk_A))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.55  thf('40', plain,
% 0.22/0.55      (![X9 : $i]:
% 0.22/0.55         (((sk_B_1 @ X9) != (sk_C_1 @ X9))
% 0.22/0.55          | (v2_funct_1 @ X9)
% 0.22/0.55          | ~ (v1_funct_1 @ X9)
% 0.22/0.55          | ~ (v1_relat_1 @ X9))),
% 0.22/0.55      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.22/0.55  thf('41', plain,
% 0.22/0.55      (((((sk_B_1 @ sk_B_2) != (sk_B_1 @ sk_B_2))
% 0.22/0.55         | ~ (v1_relat_1 @ sk_B_2)
% 0.22/0.55         | ~ (v1_funct_1 @ sk_B_2)
% 0.22/0.55         | (v2_funct_1 @ sk_B_2)))
% 0.22/0.55         <= (~ ((v2_funct_1 @ sk_B_2)) & 
% 0.22/0.55             (![X22 : $i, X23 : $i]:
% 0.22/0.55                (((X23) = (X22))
% 0.22/0.55                 | ((k1_funct_1 @ sk_B_2 @ X23) != (k1_funct_1 @ sk_B_2 @ X22))
% 0.22/0.55                 | ~ (r2_hidden @ X22 @ sk_A)
% 0.22/0.55                 | ~ (r2_hidden @ X23 @ sk_A))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.55  thf('42', plain, ((v1_relat_1 @ sk_B_2)),
% 0.22/0.55      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.55  thf('43', plain, ((v1_funct_1 @ sk_B_2)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('44', plain,
% 0.22/0.55      (((((sk_B_1 @ sk_B_2) != (sk_B_1 @ sk_B_2)) | (v2_funct_1 @ sk_B_2)))
% 0.22/0.55         <= (~ ((v2_funct_1 @ sk_B_2)) & 
% 0.22/0.55             (![X22 : $i, X23 : $i]:
% 0.22/0.55                (((X23) = (X22))
% 0.22/0.55                 | ((k1_funct_1 @ sk_B_2 @ X23) != (k1_funct_1 @ sk_B_2 @ X22))
% 0.22/0.55                 | ~ (r2_hidden @ X22 @ sk_A)
% 0.22/0.55                 | ~ (r2_hidden @ X23 @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.22/0.55  thf('45', plain,
% 0.22/0.55      (((v2_funct_1 @ sk_B_2))
% 0.22/0.55         <= (~ ((v2_funct_1 @ sk_B_2)) & 
% 0.22/0.55             (![X22 : $i, X23 : $i]:
% 0.22/0.55                (((X23) = (X22))
% 0.22/0.55                 | ((k1_funct_1 @ sk_B_2 @ X23) != (k1_funct_1 @ sk_B_2 @ X22))
% 0.22/0.55                 | ~ (r2_hidden @ X22 @ sk_A)
% 0.22/0.55                 | ~ (r2_hidden @ X23 @ sk_A))))),
% 0.22/0.55      inference('simplify', [status(thm)], ['44'])).
% 0.22/0.55  thf('46', plain, ((~ (v2_funct_1 @ sk_B_2)) <= (~ ((v2_funct_1 @ sk_B_2)))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf('47', plain,
% 0.22/0.55      (~
% 0.22/0.55       (![X22 : $i, X23 : $i]:
% 0.22/0.55          (((X23) = (X22))
% 0.22/0.55           | ((k1_funct_1 @ sk_B_2 @ X23) != (k1_funct_1 @ sk_B_2 @ X22))
% 0.22/0.55           | ~ (r2_hidden @ X22 @ sk_A)
% 0.22/0.55           | ~ (r2_hidden @ X23 @ sk_A))) | 
% 0.22/0.55       ((v2_funct_1 @ sk_B_2))),
% 0.22/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.55  thf('48', plain, (((r2_hidden @ sk_C_2 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_2))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf('49', plain, (((r2_hidden @ sk_C_2 @ sk_A))),
% 0.22/0.55      inference('sat_resolution*', [status(thm)], ['5', '47', '48'])).
% 0.22/0.55  thf('50', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.55      inference('simpl_trail', [status(thm)], ['3', '49'])).
% 0.22/0.55  thf('51', plain,
% 0.22/0.55      (((r2_hidden @ sk_C_2 @ sk_A)) <= (((r2_hidden @ sk_C_2 @ sk_A)))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf('52', plain, (((r2_hidden @ sk_C_2 @ sk_A))),
% 0.22/0.55      inference('sat_resolution*', [status(thm)], ['5', '47', '48'])).
% 0.22/0.55  thf('53', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.22/0.55      inference('simpl_trail', [status(thm)], ['51', '52'])).
% 0.22/0.55  thf('54', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t32_funct_2, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.55       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.22/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.55           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.22/0.55             ( C ) ) ) ) ))).
% 0.22/0.55  thf('55', plain,
% 0.22/0.55      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X18 @ X19)
% 0.22/0.55          | ((X20) = (k1_xboole_0))
% 0.22/0.55          | ~ (v1_funct_1 @ X21)
% 0.22/0.55          | ~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.22/0.55          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.22/0.55          | ((k1_funct_1 @ (k2_funct_1 @ X21) @ (k1_funct_1 @ X21 @ X18))
% 0.22/0.55              = (X18))
% 0.22/0.55          | ~ (v2_funct_1 @ X21))),
% 0.22/0.55      inference('cnf', [status(esa)], [t32_funct_2])).
% 0.22/0.55  thf('56', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (v2_funct_1 @ sk_B_2)
% 0.22/0.55          | ((k1_funct_1 @ (k2_funct_1 @ sk_B_2) @ (k1_funct_1 @ sk_B_2 @ X0))
% 0.22/0.55              = (X0))
% 0.22/0.55          | ~ (v1_funct_2 @ sk_B_2 @ sk_A @ sk_A)
% 0.22/0.55          | ~ (v1_funct_1 @ sk_B_2)
% 0.22/0.55          | ((sk_A) = (k1_xboole_0))
% 0.22/0.55          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['54', '55'])).
% 0.22/0.55  thf('57', plain, ((v1_funct_2 @ sk_B_2 @ sk_A @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('58', plain, ((v1_funct_1 @ sk_B_2)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('59', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (~ (v2_funct_1 @ sk_B_2)
% 0.22/0.55          | ((k1_funct_1 @ (k2_funct_1 @ sk_B_2) @ (k1_funct_1 @ sk_B_2 @ X0))
% 0.22/0.55              = (X0))
% 0.22/0.55          | ((sk_A) = (k1_xboole_0))
% 0.22/0.55          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.22/0.55  thf('60', plain, (((v2_funct_1 @ sk_B_2)) <= (((v2_funct_1 @ sk_B_2)))),
% 0.22/0.55      inference('split', [status(esa)], ['4'])).
% 0.22/0.55  thf('61', plain, (((v2_funct_1 @ sk_B_2))),
% 0.22/0.55      inference('sat_resolution*', [status(thm)], ['5', '47'])).
% 0.22/0.55  thf('62', plain, ((v2_funct_1 @ sk_B_2)),
% 0.22/0.55      inference('simpl_trail', [status(thm)], ['60', '61'])).
% 0.22/0.55  thf('63', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (((k1_funct_1 @ (k2_funct_1 @ sk_B_2) @ (k1_funct_1 @ sk_B_2 @ X0))
% 0.22/0.55            = (X0))
% 0.22/0.55          | ((sk_A) = (k1_xboole_0))
% 0.22/0.55          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['59', '62'])).
% 0.22/0.55  thf('64', plain,
% 0.22/0.55      ((((sk_A) = (k1_xboole_0))
% 0.22/0.55        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_2) @ (k1_funct_1 @ sk_B_2 @ sk_C_2))
% 0.22/0.55            = (sk_C_2)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['53', '63'])).
% 0.22/0.55  thf('65', plain, (((r2_hidden @ sk_D @ sk_A) | ~ (v2_funct_1 @ sk_B_2))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('66', plain,
% 0.22/0.55      (((r2_hidden @ sk_D @ sk_A)) <= (((r2_hidden @ sk_D @ sk_A)))),
% 0.22/0.55      inference('split', [status(esa)], ['65'])).
% 0.22/0.55  thf('67', plain, (((r2_hidden @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_B_2))),
% 0.22/0.55      inference('split', [status(esa)], ['65'])).
% 0.22/0.55  thf('68', plain, (((r2_hidden @ sk_D @ sk_A))),
% 0.22/0.55      inference('sat_resolution*', [status(thm)], ['5', '47', '67'])).
% 0.22/0.55  thf('69', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.22/0.55      inference('simpl_trail', [status(thm)], ['66', '68'])).
% 0.22/0.55  thf('70', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (((k1_funct_1 @ (k2_funct_1 @ sk_B_2) @ (k1_funct_1 @ sk_B_2 @ X0))
% 0.22/0.55            = (X0))
% 0.22/0.55          | ((sk_A) = (k1_xboole_0))
% 0.22/0.55          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)], ['59', '62'])).
% 0.22/0.55  thf('71', plain,
% 0.22/0.55      ((((sk_A) = (k1_xboole_0))
% 0.22/0.55        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_2) @ (k1_funct_1 @ sk_B_2 @ sk_D))
% 0.22/0.55            = (sk_D)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['69', '70'])).
% 0.22/0.55  thf('72', plain,
% 0.22/0.55      ((((k1_funct_1 @ sk_B_2 @ sk_C_2) = (k1_funct_1 @ sk_B_2 @ sk_D))
% 0.22/0.55        | ~ (v2_funct_1 @ sk_B_2))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('73', plain,
% 0.22/0.55      ((((k1_funct_1 @ sk_B_2 @ sk_C_2) = (k1_funct_1 @ sk_B_2 @ sk_D)))
% 0.22/0.55         <= ((((k1_funct_1 @ sk_B_2 @ sk_C_2) = (k1_funct_1 @ sk_B_2 @ sk_D))))),
% 0.22/0.55      inference('split', [status(esa)], ['72'])).
% 0.22/0.55  thf('74', plain,
% 0.22/0.55      ((((k1_funct_1 @ sk_B_2 @ sk_C_2) = (k1_funct_1 @ sk_B_2 @ sk_D))) | 
% 0.22/0.55       ~ ((v2_funct_1 @ sk_B_2))),
% 0.22/0.55      inference('split', [status(esa)], ['72'])).
% 0.22/0.55  thf('75', plain,
% 0.22/0.55      ((((k1_funct_1 @ sk_B_2 @ sk_C_2) = (k1_funct_1 @ sk_B_2 @ sk_D)))),
% 0.22/0.55      inference('sat_resolution*', [status(thm)], ['5', '47', '74'])).
% 0.22/0.55  thf('76', plain,
% 0.22/0.55      (((k1_funct_1 @ sk_B_2 @ sk_C_2) = (k1_funct_1 @ sk_B_2 @ sk_D))),
% 0.22/0.55      inference('simpl_trail', [status(thm)], ['73', '75'])).
% 0.22/0.55  thf('77', plain,
% 0.22/0.55      ((((sk_A) = (k1_xboole_0))
% 0.22/0.55        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_2) @ (k1_funct_1 @ sk_B_2 @ sk_C_2))
% 0.22/0.55            = (sk_D)))),
% 0.22/0.55      inference('demod', [status(thm)], ['71', '76'])).
% 0.22/0.55  thf('78', plain,
% 0.22/0.55      ((((sk_C_2) = (sk_D))
% 0.22/0.55        | ((sk_A) = (k1_xboole_0))
% 0.22/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.55      inference('sup+', [status(thm)], ['64', '77'])).
% 0.22/0.55  thf('79', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_2) = (sk_D)))),
% 0.22/0.55      inference('simplify', [status(thm)], ['78'])).
% 0.22/0.55  thf('80', plain, ((((sk_C_2) != (sk_D)) | ~ (v2_funct_1 @ sk_B_2))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('81', plain, ((((sk_C_2) != (sk_D))) <= (~ (((sk_C_2) = (sk_D))))),
% 0.22/0.55      inference('split', [status(esa)], ['80'])).
% 0.22/0.55  thf('82', plain, (~ (((sk_C_2) = (sk_D))) | ~ ((v2_funct_1 @ sk_B_2))),
% 0.22/0.55      inference('split', [status(esa)], ['80'])).
% 0.22/0.55  thf('83', plain, (~ (((sk_C_2) = (sk_D)))),
% 0.22/0.55      inference('sat_resolution*', [status(thm)], ['5', '47', '82'])).
% 0.22/0.55  thf('84', plain, (((sk_C_2) != (sk_D))),
% 0.22/0.55      inference('simpl_trail', [status(thm)], ['81', '83'])).
% 0.22/0.55  thf('85', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.55      inference('simplify_reflect-', [status(thm)], ['79', '84'])).
% 0.22/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.55  thf('86', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.55  thf('87', plain, ($false),
% 0.22/0.55      inference('demod', [status(thm)], ['50', '85', '86'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
