%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nX5XHpnTmU

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  123 (1041 expanded)
%              Number of leaves         :   32 ( 310 expanded)
%              Depth                    :   26
%              Number of atoms          : 1031 (15276 expanded)
%              Number of equality atoms :   87 ( 955 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X23: $i,X24: $i] :
      ( ( X24 = X23 )
      | ( ( k1_funct_1 @ sk_B_2 @ X24 )
       != ( k1_funct_1 @ sk_B_2 @ X23 ) )
      | ~ ( r2_hidden @ X23 @ sk_A )
      | ~ ( r2_hidden @ X24 @ sk_A )
      | ( v2_funct_1 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_funct_1 @ sk_B_2 )
    | ! [X23: $i,X24: $i] :
        ( ( X24 = X23 )
        | ( ( k1_funct_1 @ sk_B_2 @ X24 )
         != ( k1_funct_1 @ sk_B_2 @ X23 ) )
        | ~ ( r2_hidden @ X23 @ sk_A )
        | ~ ( r2_hidden @ X24 @ sk_A ) ) ),
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
    ! [X13: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X13 ) @ ( k1_relat_1 @ X13 ) )
      | ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( v4_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k1_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_B_2 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B_2 ) @ sk_A ),
    inference(demod,[status(thm)],['11','16'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_B_2 )
    | ( v2_funct_1 @ sk_B_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(demod,[status(thm)],['14','15'])).

thf('22',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_funct_1 @ sk_B_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X13: $i] :
      ( ( ( k1_funct_1 @ X13 @ ( sk_B_1 @ X13 ) )
        = ( k1_funct_1 @ X13 @ ( sk_C_1 @ X13 ) ) )
      | ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('25',plain,
    ( ! [X23: $i,X24: $i] :
        ( ( X24 = X23 )
        | ( ( k1_funct_1 @ sk_B_2 @ X24 )
         != ( k1_funct_1 @ sk_B_2 @ X23 ) )
        | ~ ( r2_hidden @ X23 @ sk_A )
        | ~ ( r2_hidden @ X24 @ sk_A ) )
   <= ! [X23: $i,X24: $i] :
        ( ( X24 = X23 )
        | ( ( k1_funct_1 @ sk_B_2 @ X24 )
         != ( k1_funct_1 @ sk_B_2 @ X23 ) )
        | ~ ( r2_hidden @ X23 @ sk_A )
        | ~ ( r2_hidden @ X24 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('26',plain,
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
   <= ! [X23: $i,X24: $i] :
        ( ( X24 = X23 )
        | ( ( k1_funct_1 @ sk_B_2 @ X24 )
         != ( k1_funct_1 @ sk_B_2 @ X23 ) )
        | ~ ( r2_hidden @ X23 @ sk_A )
        | ~ ( r2_hidden @ X24 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(demod,[status(thm)],['14','15'])).

thf('28',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_2 @ X0 )
         != ( k1_funct_1 @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) ) )
        | ( v2_funct_1 @ sk_B_2 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C_1 @ sk_B_2 ) @ sk_A )
        | ( X0
          = ( sk_C_1 @ sk_B_2 ) ) )
   <= ! [X23: $i,X24: $i] :
        ( ( X24 = X23 )
        | ( ( k1_funct_1 @ sk_B_2 @ X24 )
         != ( k1_funct_1 @ sk_B_2 @ X23 ) )
        | ~ ( r2_hidden @ X23 @ sk_A )
        | ~ ( r2_hidden @ X24 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( v2_funct_1 @ sk_B_2 )
        | ( X0
          = ( sk_C_1 @ sk_B_2 ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( v2_funct_1 @ sk_B_2 )
        | ( ( k1_funct_1 @ sk_B_2 @ X0 )
         != ( k1_funct_1 @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) ) ) )
   <= ! [X23: $i,X24: $i] :
        ( ( X24 = X23 )
        | ( ( k1_funct_1 @ sk_B_2 @ X24 )
         != ( k1_funct_1 @ sk_B_2 @ X23 ) )
        | ~ ( r2_hidden @ X23 @ sk_A )
        | ~ ( r2_hidden @ X24 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_2 @ X0 )
         != ( k1_funct_1 @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( X0
          = ( sk_C_1 @ sk_B_2 ) )
        | ( v2_funct_1 @ sk_B_2 ) )
   <= ! [X23: $i,X24: $i] :
        ( ( X24 = X23 )
        | ( ( k1_funct_1 @ sk_B_2 @ X24 )
         != ( k1_funct_1 @ sk_B_2 @ X23 ) )
        | ~ ( r2_hidden @ X23 @ sk_A )
        | ~ ( r2_hidden @ X24 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( v2_funct_1 @ sk_B_2 )
      | ( ( sk_B_1 @ sk_B_2 )
        = ( sk_C_1 @ sk_B_2 ) )
      | ~ ( r2_hidden @ ( sk_B_1 @ sk_B_2 ) @ sk_A ) )
   <= ! [X23: $i,X24: $i] :
        ( ( X24 = X23 )
        | ( ( k1_funct_1 @ sk_B_2 @ X24 )
         != ( k1_funct_1 @ sk_B_2 @ X23 ) )
        | ~ ( r2_hidden @ X23 @ sk_A )
        | ~ ( r2_hidden @ X24 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['31'])).

thf('33',plain,(
    ! [X13: $i] :
      ( ( r2_hidden @ ( sk_B_1 @ X13 ) @ ( k1_relat_1 @ X13 ) )
      | ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_B_2 )
    | ( v2_funct_1 @ sk_B_2 )
    | ( r2_hidden @ ( sk_B_1 @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(demod,[status(thm)],['14','15'])).

thf('37',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_funct_1 @ sk_B_2 )
    | ( r2_hidden @ ( sk_B_1 @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( ( ( sk_B_1 @ sk_B_2 )
        = ( sk_C_1 @ sk_B_2 ) )
      | ( v2_funct_1 @ sk_B_2 ) )
   <= ! [X23: $i,X24: $i] :
        ( ( X24 = X23 )
        | ( ( k1_funct_1 @ sk_B_2 @ X24 )
         != ( k1_funct_1 @ sk_B_2 @ X23 ) )
        | ~ ( r2_hidden @ X23 @ sk_A )
        | ~ ( r2_hidden @ X24 @ sk_A ) ) ),
    inference(clc,[status(thm)],['32','38'])).

thf('40',plain,
    ( ~ ( v2_funct_1 @ sk_B_2 )
   <= ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ( ( sk_B_1 @ sk_B_2 )
      = ( sk_C_1 @ sk_B_2 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_2 )
      & ! [X23: $i,X24: $i] :
          ( ( X24 = X23 )
          | ( ( k1_funct_1 @ sk_B_2 @ X24 )
           != ( k1_funct_1 @ sk_B_2 @ X23 ) )
          | ~ ( r2_hidden @ X23 @ sk_A )
          | ~ ( r2_hidden @ X24 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X13: $i] :
      ( ( ( sk_B_1 @ X13 )
       != ( sk_C_1 @ X13 ) )
      | ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('43',plain,
    ( ( ( ( sk_B_1 @ sk_B_2 )
       != ( sk_B_1 @ sk_B_2 ) )
      | ~ ( v1_relat_1 @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_B_2 )
      | ( v2_funct_1 @ sk_B_2 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_2 )
      & ! [X23: $i,X24: $i] :
          ( ( X24 = X23 )
          | ( ( k1_funct_1 @ sk_B_2 @ X24 )
           != ( k1_funct_1 @ sk_B_2 @ X23 ) )
          | ~ ( r2_hidden @ X23 @ sk_A )
          | ~ ( r2_hidden @ X24 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(demod,[status(thm)],['14','15'])).

thf('45',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( ( sk_B_1 @ sk_B_2 )
       != ( sk_B_1 @ sk_B_2 ) )
      | ( v2_funct_1 @ sk_B_2 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_2 )
      & ! [X23: $i,X24: $i] :
          ( ( X24 = X23 )
          | ( ( k1_funct_1 @ sk_B_2 @ X24 )
           != ( k1_funct_1 @ sk_B_2 @ X23 ) )
          | ~ ( r2_hidden @ X23 @ sk_A )
          | ~ ( r2_hidden @ X24 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( v2_funct_1 @ sk_B_2 )
   <= ( ~ ( v2_funct_1 @ sk_B_2 )
      & ! [X23: $i,X24: $i] :
          ( ( X24 = X23 )
          | ( ( k1_funct_1 @ sk_B_2 @ X24 )
           != ( k1_funct_1 @ sk_B_2 @ X23 ) )
          | ~ ( r2_hidden @ X23 @ sk_A )
          | ~ ( r2_hidden @ X24 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( v2_funct_1 @ sk_B_2 )
   <= ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ~ ! [X23: $i,X24: $i] :
          ( ( X24 = X23 )
          | ( ( k1_funct_1 @ sk_B_2 @ X24 )
           != ( k1_funct_1 @ sk_B_2 @ X23 ) )
          | ~ ( r2_hidden @ X23 @ sk_A )
          | ~ ( r2_hidden @ X24 @ sk_A ) )
    | ( v2_funct_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','49','50'])).

thf('52',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','51'])).

thf('53',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
   <= ( r2_hidden @ sk_C_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','49','50'])).

thf('55',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference(simpl_trail,[status(thm)],['53','54'])).

thf('56',plain,(
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

thf('57',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ( X21 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ X22 ) @ ( k1_funct_1 @ X22 @ X19 ) )
        = X19 )
      | ~ ( v2_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t32_funct_2])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B_2 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_2 ) @ ( k1_funct_1 @ sk_B_2 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_2 @ sk_B_2 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B_2 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_2 @ sk_B_2 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B_2 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_2 ) @ ( k1_funct_1 @ sk_B_2 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( v2_funct_1 @ sk_B_2 )
   <= ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['4'])).

thf('63',plain,(
    v2_funct_1 @ sk_B_2 ),
    inference('sat_resolution*',[status(thm)],['5','49'])).

thf('64',plain,(
    v2_funct_1 @ sk_B_2 ),
    inference(simpl_trail,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_2 ) @ ( k1_funct_1 @ sk_B_2 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_2 ) @ ( k1_funct_1 @ sk_B_2 @ sk_C_2 ) )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['55','65'])).

thf('67',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
   <= ( r2_hidden @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['67'])).

thf('69',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['67'])).

thf('70',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','49','69'])).

thf('71',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['68','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_2 ) @ ( k1_funct_1 @ sk_B_2 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('73',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_2 ) @ ( k1_funct_1 @ sk_B_2 @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( k1_funct_1 @ sk_B_2 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_2 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( k1_funct_1 @ sk_B_2 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_2 @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B_2 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_2 @ sk_D ) ) ),
    inference(split,[status(esa)],['74'])).

thf('76',plain,
    ( ( ( k1_funct_1 @ sk_B_2 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_2 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['74'])).

thf('77',plain,
    ( ( k1_funct_1 @ sk_B_2 @ sk_C_2 )
    = ( k1_funct_1 @ sk_B_2 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['5','49','76'])).

thf('78',plain,
    ( ( k1_funct_1 @ sk_B_2 @ sk_C_2 )
    = ( k1_funct_1 @ sk_B_2 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['75','77'])).

thf('79',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_2 ) @ ( k1_funct_1 @ sk_B_2 @ sk_C_2 ) )
      = sk_D ) ),
    inference(demod,[status(thm)],['73','78'])).

thf('80',plain,
    ( ( sk_C_2 = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','79'])).

thf('81',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( sk_C_2 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( sk_C_2 != sk_D )
   <= ( sk_C_2 != sk_D ) ),
    inference(split,[status(esa)],['82'])).

thf('84',plain,
    ( ( sk_C_2 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['82'])).

thf('85',plain,(
    sk_C_2 != sk_D ),
    inference('sat_resolution*',[status(thm)],['5','49','84'])).

thf('86',plain,(
    sk_C_2 != sk_D ),
    inference(simpl_trail,[status(thm)],['83','85'])).

thf('87',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['81','86'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('88',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['52','87','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nX5XHpnTmU
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 93 iterations in 0.042s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.50  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.20/0.50  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.20/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(t77_funct_2, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.50       ( ( v2_funct_1 @ B ) <=>
% 0.20/0.50         ( ![C:$i,D:$i]:
% 0.20/0.50           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.20/0.50               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.20/0.50             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.50            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.50          ( ( v2_funct_1 @ B ) <=>
% 0.20/0.50            ( ![C:$i,D:$i]:
% 0.20/0.50              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.20/0.50                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.20/0.50                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t77_funct_2])).
% 0.20/0.50  thf('0', plain, (((r2_hidden @ sk_C_2 @ sk_A) | ~ (v2_funct_1 @ sk_B_2))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (((r2_hidden @ sk_C_2 @ sk_A)) <= (((r2_hidden @ sk_C_2 @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf(d1_xboole_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      ((~ (v1_xboole_0 @ sk_A)) <= (((r2_hidden @ sk_C_2 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X23 : $i, X24 : $i]:
% 0.20/0.50         (((X24) = (X23))
% 0.20/0.50          | ((k1_funct_1 @ sk_B_2 @ X24) != (k1_funct_1 @ sk_B_2 @ X23))
% 0.20/0.50          | ~ (r2_hidden @ X23 @ sk_A)
% 0.20/0.50          | ~ (r2_hidden @ X24 @ sk_A)
% 0.20/0.50          | (v2_funct_1 @ sk_B_2))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (((v2_funct_1 @ sk_B_2)) | 
% 0.20/0.50       (![X23 : $i, X24 : $i]:
% 0.20/0.50          (((X24) = (X23))
% 0.20/0.50           | ((k1_funct_1 @ sk_B_2 @ X24) != (k1_funct_1 @ sk_B_2 @ X23))
% 0.20/0.50           | ~ (r2_hidden @ X23 @ sk_A)
% 0.20/0.50           | ~ (r2_hidden @ X24 @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['4'])).
% 0.20/0.50  thf(d8_funct_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.50       ( ( v2_funct_1 @ A ) <=>
% 0.20/0.50         ( ![B:$i,C:$i]:
% 0.20/0.50           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.50               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.50               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.20/0.50             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X13 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_C_1 @ X13) @ (k1_relat_1 @ X13))
% 0.20/0.50          | (v2_funct_1 @ X13)
% 0.20/0.50          | ~ (v1_funct_1 @ X13)
% 0.20/0.50          | ~ (v1_relat_1 @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc2_relset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.50         ((v4_relat_1 @ X16 @ X17)
% 0.20/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.50  thf('9', plain, ((v4_relat_1 @ sk_B_2 @ sk_A)),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf(d18_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X9 : $i, X10 : $i]:
% 0.20/0.50         (~ (v4_relat_1 @ X9 @ X10)
% 0.20/0.50          | (r1_tarski @ (k1_relat_1 @ X9) @ X10)
% 0.20/0.50          | ~ (v1_relat_1 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_B_2) | (r1_tarski @ (k1_relat_1 @ sk_B_2) @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc2_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.20/0.50          | (v1_relat_1 @ X7)
% 0.20/0.50          | ~ (v1_relat_1 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf(fc6_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.20/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.50  thf('16', plain, ((v1_relat_1 @ sk_B_2)),
% 0.20/0.50      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('17', plain, ((r1_tarski @ (k1_relat_1 @ sk_B_2) @ sk_A)),
% 0.20/0.50      inference('demod', [status(thm)], ['11', '16'])).
% 0.20/0.50  thf(d3_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.50          | (r2_hidden @ X3 @ X5)
% 0.20/0.50          | ~ (r1_tarski @ X4 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_B_2)
% 0.20/0.50        | ~ (v1_funct_1 @ sk_B_2)
% 0.20/0.50        | (v2_funct_1 @ sk_B_2)
% 0.20/0.50        | (r2_hidden @ (sk_C_1 @ sk_B_2) @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '19'])).
% 0.20/0.50  thf('21', plain, ((v1_relat_1 @ sk_B_2)),
% 0.20/0.50      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('22', plain, ((v1_funct_1 @ sk_B_2)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (((v2_funct_1 @ sk_B_2) | (r2_hidden @ (sk_C_1 @ sk_B_2) @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X13 : $i]:
% 0.20/0.50         (((k1_funct_1 @ X13 @ (sk_B_1 @ X13))
% 0.20/0.50            = (k1_funct_1 @ X13 @ (sk_C_1 @ X13)))
% 0.20/0.50          | (v2_funct_1 @ X13)
% 0.20/0.50          | ~ (v1_funct_1 @ X13)
% 0.20/0.50          | ~ (v1_relat_1 @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      ((![X23 : $i, X24 : $i]:
% 0.20/0.50          (((X24) = (X23))
% 0.20/0.50           | ((k1_funct_1 @ sk_B_2 @ X24) != (k1_funct_1 @ sk_B_2 @ X23))
% 0.20/0.50           | ~ (r2_hidden @ X23 @ sk_A)
% 0.20/0.50           | ~ (r2_hidden @ X24 @ sk_A)))
% 0.20/0.50         <= ((![X23 : $i, X24 : $i]:
% 0.20/0.50                (((X24) = (X23))
% 0.20/0.50                 | ((k1_funct_1 @ sk_B_2 @ X24) != (k1_funct_1 @ sk_B_2 @ X23))
% 0.20/0.50                 | ~ (r2_hidden @ X23 @ sk_A)
% 0.20/0.50                 | ~ (r2_hidden @ X24 @ sk_A))))),
% 0.20/0.50      inference('split', [status(esa)], ['4'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (((k1_funct_1 @ sk_B_2 @ X0)
% 0.20/0.50             != (k1_funct_1 @ sk_B_2 @ (sk_B_1 @ sk_B_2)))
% 0.20/0.50           | ~ (v1_relat_1 @ sk_B_2)
% 0.20/0.50           | ~ (v1_funct_1 @ sk_B_2)
% 0.20/0.50           | (v2_funct_1 @ sk_B_2)
% 0.20/0.50           | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.50           | ~ (r2_hidden @ (sk_C_1 @ sk_B_2) @ sk_A)
% 0.20/0.50           | ((X0) = (sk_C_1 @ sk_B_2))))
% 0.20/0.50         <= ((![X23 : $i, X24 : $i]:
% 0.20/0.50                (((X24) = (X23))
% 0.20/0.50                 | ((k1_funct_1 @ sk_B_2 @ X24) != (k1_funct_1 @ sk_B_2 @ X23))
% 0.20/0.50                 | ~ (r2_hidden @ X23 @ sk_A)
% 0.20/0.50                 | ~ (r2_hidden @ X24 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain, ((v1_relat_1 @ sk_B_2)),
% 0.20/0.50      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('28', plain, ((v1_funct_1 @ sk_B_2)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (((k1_funct_1 @ sk_B_2 @ X0)
% 0.20/0.50             != (k1_funct_1 @ sk_B_2 @ (sk_B_1 @ sk_B_2)))
% 0.20/0.50           | (v2_funct_1 @ sk_B_2)
% 0.20/0.50           | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.50           | ~ (r2_hidden @ (sk_C_1 @ sk_B_2) @ sk_A)
% 0.20/0.50           | ((X0) = (sk_C_1 @ sk_B_2))))
% 0.20/0.50         <= ((![X23 : $i, X24 : $i]:
% 0.20/0.50                (((X24) = (X23))
% 0.20/0.50                 | ((k1_funct_1 @ sk_B_2 @ X24) != (k1_funct_1 @ sk_B_2 @ X23))
% 0.20/0.50                 | ~ (r2_hidden @ X23 @ sk_A)
% 0.20/0.50                 | ~ (r2_hidden @ X24 @ sk_A))))),
% 0.20/0.50      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          ((v2_funct_1 @ sk_B_2)
% 0.20/0.50           | ((X0) = (sk_C_1 @ sk_B_2))
% 0.20/0.50           | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.50           | (v2_funct_1 @ sk_B_2)
% 0.20/0.50           | ((k1_funct_1 @ sk_B_2 @ X0)
% 0.20/0.50               != (k1_funct_1 @ sk_B_2 @ (sk_B_1 @ sk_B_2)))))
% 0.20/0.50         <= ((![X23 : $i, X24 : $i]:
% 0.20/0.50                (((X24) = (X23))
% 0.20/0.50                 | ((k1_funct_1 @ sk_B_2 @ X24) != (k1_funct_1 @ sk_B_2 @ X23))
% 0.20/0.50                 | ~ (r2_hidden @ X23 @ sk_A)
% 0.20/0.50                 | ~ (r2_hidden @ X24 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['23', '29'])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          (((k1_funct_1 @ sk_B_2 @ X0)
% 0.20/0.50             != (k1_funct_1 @ sk_B_2 @ (sk_B_1 @ sk_B_2)))
% 0.20/0.50           | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.50           | ((X0) = (sk_C_1 @ sk_B_2))
% 0.20/0.50           | (v2_funct_1 @ sk_B_2)))
% 0.20/0.50         <= ((![X23 : $i, X24 : $i]:
% 0.20/0.50                (((X24) = (X23))
% 0.20/0.50                 | ((k1_funct_1 @ sk_B_2 @ X24) != (k1_funct_1 @ sk_B_2 @ X23))
% 0.20/0.50                 | ~ (r2_hidden @ X23 @ sk_A)
% 0.20/0.50                 | ~ (r2_hidden @ X24 @ sk_A))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      ((((v2_funct_1 @ sk_B_2)
% 0.20/0.50         | ((sk_B_1 @ sk_B_2) = (sk_C_1 @ sk_B_2))
% 0.20/0.50         | ~ (r2_hidden @ (sk_B_1 @ sk_B_2) @ sk_A)))
% 0.20/0.50         <= ((![X23 : $i, X24 : $i]:
% 0.20/0.50                (((X24) = (X23))
% 0.20/0.50                 | ((k1_funct_1 @ sk_B_2 @ X24) != (k1_funct_1 @ sk_B_2 @ X23))
% 0.20/0.50                 | ~ (r2_hidden @ X23 @ sk_A)
% 0.20/0.50                 | ~ (r2_hidden @ X24 @ sk_A))))),
% 0.20/0.50      inference('eq_res', [status(thm)], ['31'])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (![X13 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_B_1 @ X13) @ (k1_relat_1 @ X13))
% 0.20/0.50          | (v2_funct_1 @ X13)
% 0.20/0.50          | ~ (v1_funct_1 @ X13)
% 0.20/0.50          | ~ (v1_relat_1 @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_B_2)
% 0.20/0.50        | ~ (v1_funct_1 @ sk_B_2)
% 0.20/0.50        | (v2_funct_1 @ sk_B_2)
% 0.20/0.50        | (r2_hidden @ (sk_B_1 @ sk_B_2) @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain, ((v1_relat_1 @ sk_B_2)),
% 0.20/0.50      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('37', plain, ((v1_funct_1 @ sk_B_2)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (((v2_funct_1 @ sk_B_2) | (r2_hidden @ (sk_B_1 @ sk_B_2) @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (((((sk_B_1 @ sk_B_2) = (sk_C_1 @ sk_B_2)) | (v2_funct_1 @ sk_B_2)))
% 0.20/0.50         <= ((![X23 : $i, X24 : $i]:
% 0.20/0.50                (((X24) = (X23))
% 0.20/0.50                 | ((k1_funct_1 @ sk_B_2 @ X24) != (k1_funct_1 @ sk_B_2 @ X23))
% 0.20/0.50                 | ~ (r2_hidden @ X23 @ sk_A)
% 0.20/0.50                 | ~ (r2_hidden @ X24 @ sk_A))))),
% 0.20/0.50      inference('clc', [status(thm)], ['32', '38'])).
% 0.20/0.50  thf('40', plain, ((~ (v2_funct_1 @ sk_B_2)) <= (~ ((v2_funct_1 @ sk_B_2)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      ((((sk_B_1 @ sk_B_2) = (sk_C_1 @ sk_B_2)))
% 0.20/0.50         <= (~ ((v2_funct_1 @ sk_B_2)) & 
% 0.20/0.50             (![X23 : $i, X24 : $i]:
% 0.20/0.50                (((X24) = (X23))
% 0.20/0.50                 | ((k1_funct_1 @ sk_B_2 @ X24) != (k1_funct_1 @ sk_B_2 @ X23))
% 0.20/0.50                 | ~ (r2_hidden @ X23 @ sk_A)
% 0.20/0.50                 | ~ (r2_hidden @ X24 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X13 : $i]:
% 0.20/0.50         (((sk_B_1 @ X13) != (sk_C_1 @ X13))
% 0.20/0.50          | (v2_funct_1 @ X13)
% 0.20/0.50          | ~ (v1_funct_1 @ X13)
% 0.20/0.50          | ~ (v1_relat_1 @ X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.50  thf('43', plain,
% 0.20/0.50      (((((sk_B_1 @ sk_B_2) != (sk_B_1 @ sk_B_2))
% 0.20/0.50         | ~ (v1_relat_1 @ sk_B_2)
% 0.20/0.50         | ~ (v1_funct_1 @ sk_B_2)
% 0.20/0.50         | (v2_funct_1 @ sk_B_2)))
% 0.20/0.50         <= (~ ((v2_funct_1 @ sk_B_2)) & 
% 0.20/0.50             (![X23 : $i, X24 : $i]:
% 0.20/0.50                (((X24) = (X23))
% 0.20/0.50                 | ((k1_funct_1 @ sk_B_2 @ X24) != (k1_funct_1 @ sk_B_2 @ X23))
% 0.20/0.50                 | ~ (r2_hidden @ X23 @ sk_A)
% 0.20/0.50                 | ~ (r2_hidden @ X24 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.50  thf('44', plain, ((v1_relat_1 @ sk_B_2)),
% 0.20/0.50      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.50  thf('45', plain, ((v1_funct_1 @ sk_B_2)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (((((sk_B_1 @ sk_B_2) != (sk_B_1 @ sk_B_2)) | (v2_funct_1 @ sk_B_2)))
% 0.20/0.50         <= (~ ((v2_funct_1 @ sk_B_2)) & 
% 0.20/0.50             (![X23 : $i, X24 : $i]:
% 0.20/0.50                (((X24) = (X23))
% 0.20/0.50                 | ((k1_funct_1 @ sk_B_2 @ X24) != (k1_funct_1 @ sk_B_2 @ X23))
% 0.20/0.50                 | ~ (r2_hidden @ X23 @ sk_A)
% 0.20/0.50                 | ~ (r2_hidden @ X24 @ sk_A))))),
% 0.20/0.50      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      (((v2_funct_1 @ sk_B_2))
% 0.20/0.50         <= (~ ((v2_funct_1 @ sk_B_2)) & 
% 0.20/0.50             (![X23 : $i, X24 : $i]:
% 0.20/0.50                (((X24) = (X23))
% 0.20/0.50                 | ((k1_funct_1 @ sk_B_2 @ X24) != (k1_funct_1 @ sk_B_2 @ X23))
% 0.20/0.50                 | ~ (r2_hidden @ X23 @ sk_A)
% 0.20/0.50                 | ~ (r2_hidden @ X24 @ sk_A))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['46'])).
% 0.20/0.50  thf('48', plain, ((~ (v2_funct_1 @ sk_B_2)) <= (~ ((v2_funct_1 @ sk_B_2)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (~
% 0.20/0.50       (![X23 : $i, X24 : $i]:
% 0.20/0.50          (((X24) = (X23))
% 0.20/0.50           | ((k1_funct_1 @ sk_B_2 @ X24) != (k1_funct_1 @ sk_B_2 @ X23))
% 0.20/0.50           | ~ (r2_hidden @ X23 @ sk_A)
% 0.20/0.50           | ~ (r2_hidden @ X24 @ sk_A))) | 
% 0.20/0.50       ((v2_funct_1 @ sk_B_2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.50  thf('50', plain, (((r2_hidden @ sk_C_2 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_2))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('51', plain, (((r2_hidden @ sk_C_2 @ sk_A))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['5', '49', '50'])).
% 0.20/0.50  thf('52', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['3', '51'])).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      (((r2_hidden @ sk_C_2 @ sk_A)) <= (((r2_hidden @ sk_C_2 @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['0'])).
% 0.20/0.50  thf('54', plain, (((r2_hidden @ sk_C_2 @ sk_A))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['5', '49', '50'])).
% 0.20/0.50  thf('55', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['53', '54'])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t32_funct_2, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.50         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.50       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.20/0.50         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.50           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.20/0.50             ( C ) ) ) ) ))).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X19 @ X20)
% 0.20/0.50          | ((X21) = (k1_xboole_0))
% 0.20/0.50          | ~ (v1_funct_1 @ X22)
% 0.20/0.50          | ~ (v1_funct_2 @ X22 @ X20 @ X21)
% 0.20/0.50          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.20/0.50          | ((k1_funct_1 @ (k2_funct_1 @ X22) @ (k1_funct_1 @ X22 @ X19))
% 0.20/0.50              = (X19))
% 0.20/0.50          | ~ (v2_funct_1 @ X22))),
% 0.20/0.50      inference('cnf', [status(esa)], [t32_funct_2])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v2_funct_1 @ sk_B_2)
% 0.20/0.50          | ((k1_funct_1 @ (k2_funct_1 @ sk_B_2) @ (k1_funct_1 @ sk_B_2 @ X0))
% 0.20/0.50              = (X0))
% 0.20/0.50          | ~ (v1_funct_2 @ sk_B_2 @ sk_A @ sk_A)
% 0.20/0.50          | ~ (v1_funct_1 @ sk_B_2)
% 0.20/0.50          | ((sk_A) = (k1_xboole_0))
% 0.20/0.50          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.50  thf('59', plain, ((v1_funct_2 @ sk_B_2 @ sk_A @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('60', plain, ((v1_funct_1 @ sk_B_2)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v2_funct_1 @ sk_B_2)
% 0.20/0.50          | ((k1_funct_1 @ (k2_funct_1 @ sk_B_2) @ (k1_funct_1 @ sk_B_2 @ X0))
% 0.20/0.50              = (X0))
% 0.20/0.50          | ((sk_A) = (k1_xboole_0))
% 0.20/0.50          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.20/0.50  thf('62', plain, (((v2_funct_1 @ sk_B_2)) <= (((v2_funct_1 @ sk_B_2)))),
% 0.20/0.50      inference('split', [status(esa)], ['4'])).
% 0.20/0.50  thf('63', plain, (((v2_funct_1 @ sk_B_2))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['5', '49'])).
% 0.20/0.50  thf('64', plain, ((v2_funct_1 @ sk_B_2)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['62', '63'])).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k1_funct_1 @ (k2_funct_1 @ sk_B_2) @ (k1_funct_1 @ sk_B_2 @ X0))
% 0.20/0.50            = (X0))
% 0.20/0.50          | ((sk_A) = (k1_xboole_0))
% 0.20/0.50          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['61', '64'])).
% 0.20/0.50  thf('66', plain,
% 0.20/0.50      ((((sk_A) = (k1_xboole_0))
% 0.20/0.50        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_2) @ (k1_funct_1 @ sk_B_2 @ sk_C_2))
% 0.20/0.50            = (sk_C_2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['55', '65'])).
% 0.20/0.50  thf('67', plain, (((r2_hidden @ sk_D @ sk_A) | ~ (v2_funct_1 @ sk_B_2))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('68', plain,
% 0.20/0.50      (((r2_hidden @ sk_D @ sk_A)) <= (((r2_hidden @ sk_D @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['67'])).
% 0.20/0.50  thf('69', plain, (((r2_hidden @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_B_2))),
% 0.20/0.50      inference('split', [status(esa)], ['67'])).
% 0.20/0.50  thf('70', plain, (((r2_hidden @ sk_D @ sk_A))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['5', '49', '69'])).
% 0.20/0.50  thf('71', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['68', '70'])).
% 0.20/0.50  thf('72', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k1_funct_1 @ (k2_funct_1 @ sk_B_2) @ (k1_funct_1 @ sk_B_2 @ X0))
% 0.20/0.50            = (X0))
% 0.20/0.50          | ((sk_A) = (k1_xboole_0))
% 0.20/0.50          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['61', '64'])).
% 0.20/0.50  thf('73', plain,
% 0.20/0.50      ((((sk_A) = (k1_xboole_0))
% 0.20/0.50        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_2) @ (k1_funct_1 @ sk_B_2 @ sk_D))
% 0.20/0.50            = (sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['71', '72'])).
% 0.20/0.50  thf('74', plain,
% 0.20/0.50      ((((k1_funct_1 @ sk_B_2 @ sk_C_2) = (k1_funct_1 @ sk_B_2 @ sk_D))
% 0.20/0.50        | ~ (v2_funct_1 @ sk_B_2))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('75', plain,
% 0.20/0.50      ((((k1_funct_1 @ sk_B_2 @ sk_C_2) = (k1_funct_1 @ sk_B_2 @ sk_D)))
% 0.20/0.50         <= ((((k1_funct_1 @ sk_B_2 @ sk_C_2) = (k1_funct_1 @ sk_B_2 @ sk_D))))),
% 0.20/0.50      inference('split', [status(esa)], ['74'])).
% 0.20/0.50  thf('76', plain,
% 0.20/0.50      ((((k1_funct_1 @ sk_B_2 @ sk_C_2) = (k1_funct_1 @ sk_B_2 @ sk_D))) | 
% 0.20/0.50       ~ ((v2_funct_1 @ sk_B_2))),
% 0.20/0.50      inference('split', [status(esa)], ['74'])).
% 0.20/0.50  thf('77', plain,
% 0.20/0.50      ((((k1_funct_1 @ sk_B_2 @ sk_C_2) = (k1_funct_1 @ sk_B_2 @ sk_D)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['5', '49', '76'])).
% 0.20/0.50  thf('78', plain,
% 0.20/0.50      (((k1_funct_1 @ sk_B_2 @ sk_C_2) = (k1_funct_1 @ sk_B_2 @ sk_D))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['75', '77'])).
% 0.20/0.50  thf('79', plain,
% 0.20/0.50      ((((sk_A) = (k1_xboole_0))
% 0.20/0.50        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_2) @ (k1_funct_1 @ sk_B_2 @ sk_C_2))
% 0.20/0.50            = (sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['73', '78'])).
% 0.20/0.50  thf('80', plain,
% 0.20/0.50      ((((sk_C_2) = (sk_D))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['66', '79'])).
% 0.20/0.50  thf('81', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_2) = (sk_D)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['80'])).
% 0.20/0.50  thf('82', plain, ((((sk_C_2) != (sk_D)) | ~ (v2_funct_1 @ sk_B_2))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('83', plain, ((((sk_C_2) != (sk_D))) <= (~ (((sk_C_2) = (sk_D))))),
% 0.20/0.50      inference('split', [status(esa)], ['82'])).
% 0.20/0.50  thf('84', plain, (~ (((sk_C_2) = (sk_D))) | ~ ((v2_funct_1 @ sk_B_2))),
% 0.20/0.50      inference('split', [status(esa)], ['82'])).
% 0.20/0.50  thf('85', plain, (~ (((sk_C_2) = (sk_D)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['5', '49', '84'])).
% 0.20/0.50  thf('86', plain, (((sk_C_2) != (sk_D))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['83', '85'])).
% 0.20/0.50  thf('87', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['81', '86'])).
% 0.20/0.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.50  thf('88', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.50  thf('89', plain, ($false),
% 0.20/0.50      inference('demod', [status(thm)], ['52', '87', '88'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
