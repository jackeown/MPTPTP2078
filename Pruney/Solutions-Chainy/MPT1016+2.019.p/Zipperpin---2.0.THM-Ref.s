%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KHbxRVZGwP

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  153 (2334 expanded)
%              Number of leaves         :   33 ( 681 expanded)
%              Depth                    :   33
%              Number of atoms          : 1189 (33526 expanded)
%              Number of equality atoms :   95 (2049 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

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
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
   <= ( r2_hidden @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X30 = X29 )
      | ( ( k1_funct_1 @ sk_B_1 @ X30 )
       != ( k1_funct_1 @ sk_B_1 @ X29 ) )
      | ~ ( r2_hidden @ X29 @ sk_A )
      | ~ ( r2_hidden @ X30 @ sk_A )
      | ( v2_funct_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ! [X29: $i,X30: $i] :
        ( ( X30 = X29 )
        | ( ( k1_funct_1 @ sk_B_1 @ X30 )
         != ( k1_funct_1 @ sk_B_1 @ X29 ) )
        | ~ ( r2_hidden @ X29 @ sk_A )
        | ~ ( r2_hidden @ X30 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

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

thf('4',plain,(
    ! [X19: $i] :
      ( ( r2_hidden @ ( sk_C @ X19 ) @ ( k1_relat_1 @ X19 ) )
      | ( v2_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v4_relat_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['9','14'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('18',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('22',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X19: $i] :
      ( ( ( k1_funct_1 @ X19 @ ( sk_B @ X19 ) )
        = ( k1_funct_1 @ X19 @ ( sk_C @ X19 ) ) )
      | ( v2_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('25',plain,
    ( ! [X29: $i,X30: $i] :
        ( ( X30 = X29 )
        | ( ( k1_funct_1 @ sk_B_1 @ X30 )
         != ( k1_funct_1 @ sk_B_1 @ X29 ) )
        | ~ ( r2_hidden @ X29 @ sk_A )
        | ~ ( r2_hidden @ X30 @ sk_A ) )
   <= ! [X29: $i,X30: $i] :
        ( ( X30 = X29 )
        | ( ( k1_funct_1 @ sk_B_1 @ X30 )
         != ( k1_funct_1 @ sk_B_1 @ X29 ) )
        | ~ ( r2_hidden @ X29 @ sk_A )
        | ~ ( r2_hidden @ X30 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ~ ( v1_relat_1 @ sk_B_1 )
        | ~ ( v1_funct_1 @ sk_B_1 )
        | ( v2_funct_1 @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_1 ) ) )
   <= ! [X29: $i,X30: $i] :
        ( ( X30 = X29 )
        | ( ( k1_funct_1 @ sk_B_1 @ X30 )
         != ( k1_funct_1 @ sk_B_1 @ X29 ) )
        | ~ ( r2_hidden @ X29 @ sk_A )
        | ~ ( r2_hidden @ X30 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('28',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ( v2_funct_1 @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_1 ) ) )
   <= ! [X29: $i,X30: $i] :
        ( ( X30 = X29 )
        | ( ( k1_funct_1 @ sk_B_1 @ X30 )
         != ( k1_funct_1 @ sk_B_1 @ X29 ) )
        | ~ ( r2_hidden @ X29 @ sk_A )
        | ~ ( r2_hidden @ X30 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( v2_funct_1 @ sk_B_1 )
        | ( X0
          = ( sk_C @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( v2_funct_1 @ sk_B_1 )
        | ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
   <= ! [X29: $i,X30: $i] :
        ( ( X30 = X29 )
        | ( ( k1_funct_1 @ sk_B_1 @ X30 )
         != ( k1_funct_1 @ sk_B_1 @ X29 ) )
        | ~ ( r2_hidden @ X29 @ sk_A )
        | ~ ( r2_hidden @ X30 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_1 ) )
        | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X29: $i,X30: $i] :
        ( ( X30 = X29 )
        | ( ( k1_funct_1 @ sk_B_1 @ X30 )
         != ( k1_funct_1 @ sk_B_1 @ X29 ) )
        | ~ ( r2_hidden @ X29 @ sk_A )
        | ~ ( r2_hidden @ X30 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( v2_funct_1 @ sk_B_1 )
      | ( ( sk_B @ sk_B_1 )
        = ( sk_C @ sk_B_1 ) )
      | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) )
   <= ! [X29: $i,X30: $i] :
        ( ( X30 = X29 )
        | ( ( k1_funct_1 @ sk_B_1 @ X30 )
         != ( k1_funct_1 @ sk_B_1 @ X29 ) )
        | ~ ( r2_hidden @ X29 @ sk_A )
        | ~ ( r2_hidden @ X30 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['31'])).

thf('33',plain,(
    ! [X19: $i] :
      ( ( r2_hidden @ ( sk_B @ X19 ) @ ( k1_relat_1 @ X19 ) )
      | ( v2_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('37',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( ( ( sk_B @ sk_B_1 )
        = ( sk_C @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X29: $i,X30: $i] :
        ( ( X30 = X29 )
        | ( ( k1_funct_1 @ sk_B_1 @ X30 )
         != ( k1_funct_1 @ sk_B_1 @ X29 ) )
        | ~ ( r2_hidden @ X29 @ sk_A )
        | ~ ( r2_hidden @ X30 @ sk_A ) ) ),
    inference(clc,[status(thm)],['32','38'])).

thf('40',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,
    ( ( ( sk_B @ sk_B_1 )
      = ( sk_C @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X29: $i,X30: $i] :
          ( ( X30 = X29 )
          | ( ( k1_funct_1 @ sk_B_1 @ X30 )
           != ( k1_funct_1 @ sk_B_1 @ X29 ) )
          | ~ ( r2_hidden @ X29 @ sk_A )
          | ~ ( r2_hidden @ X30 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X19: $i] :
      ( ( ( sk_B @ X19 )
       != ( sk_C @ X19 ) )
      | ( v2_funct_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('44',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X29: $i,X30: $i] :
          ( ( X30 = X29 )
          | ( ( k1_funct_1 @ sk_B_1 @ X30 )
           != ( k1_funct_1 @ sk_B_1 @ X29 ) )
          | ~ ( r2_hidden @ X29 @ sk_A )
          | ~ ( r2_hidden @ X30 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['12','13'])).

thf('46',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X29: $i,X30: $i] :
          ( ( X30 = X29 )
          | ( ( k1_funct_1 @ sk_B_1 @ X30 )
           != ( k1_funct_1 @ sk_B_1 @ X29 ) )
          | ~ ( r2_hidden @ X29 @ sk_A )
          | ~ ( r2_hidden @ X30 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X29: $i,X30: $i] :
          ( ( X30 = X29 )
          | ( ( k1_funct_1 @ sk_B_1 @ X30 )
           != ( k1_funct_1 @ sk_B_1 @ X29 ) )
          | ~ ( r2_hidden @ X29 @ sk_A )
          | ~ ( r2_hidden @ X30 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['40'])).

thf('50',plain,
    ( ~ ! [X29: $i,X30: $i] :
          ( ( X30 = X29 )
          | ( ( k1_funct_1 @ sk_B_1 @ X30 )
           != ( k1_funct_1 @ sk_B_1 @ X29 ) )
          | ~ ( r2_hidden @ X29 @ sk_A )
          | ~ ( r2_hidden @ X30 @ sk_A ) )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','50','51'])).

thf('53',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['1','52'])).

thf('54',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['40'])).

thf('55',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['40'])).

thf('56',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','50','55'])).

thf('57',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['54','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('59',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( X27 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ X28 ) @ ( k1_funct_1 @ X28 @ X25 ) )
        = X25 )
      | ~ ( v2_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t32_funct_2])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('62',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['3','50'])).

thf('63',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','63','64','65'])).

thf('67',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['57','66'])).

thf('68',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['1','52'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','63','64','65'])).

thf('70',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['71'])).

thf('73',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['71'])).

thf('74',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','50','73'])).

thf('75',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['72','74'])).

thf('76',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) )
      = sk_D ) ),
    inference(demod,[status(thm)],['70','75'])).

thf('77',plain,
    ( ( sk_C_1 = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','76'])).

thf('78',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( sk_C_1 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( sk_C_1 != sk_D )
   <= ( sk_C_1 != sk_D ) ),
    inference(split,[status(esa)],['79'])).

thf('81',plain,
    ( ( sk_C_1 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['79'])).

thf('82',plain,(
    sk_C_1 != sk_D ),
    inference('sat_resolution*',[status(thm)],['3','50','81'])).

thf('83',plain,(
    sk_C_1 != sk_D ),
    inference(simpl_trail,[status(thm)],['80','82'])).

thf('84',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['78','83'])).

thf('85',plain,(
    r2_hidden @ sk_D @ k1_xboole_0 ),
    inference(demod,[status(thm)],['53','84'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('86',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('87',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('88',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_D @ X0 ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('93',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('95',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('96',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( m1_subset_1 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_D @ X0 ) ),
    inference('sup-',[status(thm)],['91','97'])).

thf('99',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('100',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_D @ X0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    sk_D = k1_xboole_0 ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,(
    sk_C_1 != sk_D ),
    inference(simpl_trail,[status(thm)],['80','82'])).

thf('106',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['54','56'])).

thf('107',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['78','83'])).

thf('108',plain,(
    r2_hidden @ sk_C_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('110',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_C_1 @ X0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('112',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_C_1 @ X0 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('114',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C_1 @ X0 ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('116',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    k1_xboole_0 != sk_D ),
    inference(demod,[status(thm)],['105','116'])).

thf('118',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['104','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KHbxRVZGwP
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 211 iterations in 0.100s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i > $i).
% 0.20/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.55  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.55  thf(t77_funct_2, conjecture,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.55       ( ( v2_funct_1 @ B ) <=>
% 0.20/0.55         ( ![C:$i,D:$i]:
% 0.20/0.55           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.20/0.55               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.20/0.55             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i]:
% 0.20/0.55        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.55            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.55          ( ( v2_funct_1 @ B ) <=>
% 0.20/0.55            ( ![C:$i,D:$i]:
% 0.20/0.55              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.20/0.55                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.20/0.55                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t77_funct_2])).
% 0.20/0.55  thf('0', plain, (((r2_hidden @ sk_D @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      (((r2_hidden @ sk_D @ sk_A)) <= (((r2_hidden @ sk_D @ sk_A)))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (![X29 : $i, X30 : $i]:
% 0.20/0.55         (((X30) = (X29))
% 0.20/0.55          | ((k1_funct_1 @ sk_B_1 @ X30) != (k1_funct_1 @ sk_B_1 @ X29))
% 0.20/0.55          | ~ (r2_hidden @ X29 @ sk_A)
% 0.20/0.55          | ~ (r2_hidden @ X30 @ sk_A)
% 0.20/0.55          | (v2_funct_1 @ sk_B_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (((v2_funct_1 @ sk_B_1)) | 
% 0.20/0.55       (![X29 : $i, X30 : $i]:
% 0.20/0.55          (((X30) = (X29))
% 0.20/0.55           | ((k1_funct_1 @ sk_B_1 @ X30) != (k1_funct_1 @ sk_B_1 @ X29))
% 0.20/0.55           | ~ (r2_hidden @ X29 @ sk_A)
% 0.20/0.55           | ~ (r2_hidden @ X30 @ sk_A)))),
% 0.20/0.55      inference('split', [status(esa)], ['2'])).
% 0.20/0.55  thf(d8_funct_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.55       ( ( v2_funct_1 @ A ) <=>
% 0.20/0.55         ( ![B:$i,C:$i]:
% 0.20/0.55           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.55               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.55               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.20/0.55             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (![X19 : $i]:
% 0.20/0.55         ((r2_hidden @ (sk_C @ X19) @ (k1_relat_1 @ X19))
% 0.20/0.55          | (v2_funct_1 @ X19)
% 0.20/0.55          | ~ (v1_funct_1 @ X19)
% 0.20/0.55          | ~ (v1_relat_1 @ X19))),
% 0.20/0.55      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(cc2_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.55  thf('6', plain,
% 0.20/0.55      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.55         ((v4_relat_1 @ X22 @ X23)
% 0.20/0.55          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.55  thf('7', plain, ((v4_relat_1 @ sk_B_1 @ sk_A)),
% 0.20/0.55      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.55  thf(d18_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ B ) =>
% 0.20/0.55       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (![X15 : $i, X16 : $i]:
% 0.20/0.55         (~ (v4_relat_1 @ X15 @ X16)
% 0.20/0.55          | (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 0.20/0.55          | ~ (v1_relat_1 @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      ((~ (v1_relat_1 @ sk_B_1) | (r1_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(cc2_relat_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (![X13 : $i, X14 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.20/0.55          | (v1_relat_1 @ X13)
% 0.20/0.55          | ~ (v1_relat_1 @ X14))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.55  thf(fc6_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.55  thf('14', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('15', plain, ((r1_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.20/0.55      inference('demod', [status(thm)], ['9', '14'])).
% 0.20/0.55  thf(t3_subset, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (![X7 : $i, X9 : $i]:
% 0.20/0.55         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      ((m1_subset_1 @ (k1_relat_1 @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.55  thf(l3_subset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X4 @ X5)
% 0.20/0.55          | (r2_hidden @ X4 @ X6)
% 0.20/0.55          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.20/0.55      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      ((~ (v1_relat_1 @ sk_B_1)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.55        | (v2_funct_1 @ sk_B_1)
% 0.20/0.55        | (r2_hidden @ (sk_C @ sk_B_1) @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['4', '19'])).
% 0.20/0.55  thf('21', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('22', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (((v2_funct_1 @ sk_B_1) | (r2_hidden @ (sk_C @ sk_B_1) @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.20/0.55  thf('24', plain,
% 0.20/0.55      (![X19 : $i]:
% 0.20/0.55         (((k1_funct_1 @ X19 @ (sk_B @ X19))
% 0.20/0.55            = (k1_funct_1 @ X19 @ (sk_C @ X19)))
% 0.20/0.55          | (v2_funct_1 @ X19)
% 0.20/0.55          | ~ (v1_funct_1 @ X19)
% 0.20/0.55          | ~ (v1_relat_1 @ X19))),
% 0.20/0.55      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      ((![X29 : $i, X30 : $i]:
% 0.20/0.55          (((X30) = (X29))
% 0.20/0.55           | ((k1_funct_1 @ sk_B_1 @ X30) != (k1_funct_1 @ sk_B_1 @ X29))
% 0.20/0.55           | ~ (r2_hidden @ X29 @ sk_A)
% 0.20/0.55           | ~ (r2_hidden @ X30 @ sk_A)))
% 0.20/0.55         <= ((![X29 : $i, X30 : $i]:
% 0.20/0.55                (((X30) = (X29))
% 0.20/0.55                 | ((k1_funct_1 @ sk_B_1 @ X30) != (k1_funct_1 @ sk_B_1 @ X29))
% 0.20/0.55                 | ~ (r2_hidden @ X29 @ sk_A)
% 0.20/0.55                 | ~ (r2_hidden @ X30 @ sk_A))))),
% 0.20/0.55      inference('split', [status(esa)], ['2'])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.20/0.55             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.20/0.55           | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.55           | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.55           | (v2_funct_1 @ sk_B_1)
% 0.20/0.55           | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.55           | ~ (r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.20/0.55           | ((X0) = (sk_C @ sk_B_1))))
% 0.20/0.55         <= ((![X29 : $i, X30 : $i]:
% 0.20/0.55                (((X30) = (X29))
% 0.20/0.55                 | ((k1_funct_1 @ sk_B_1 @ X30) != (k1_funct_1 @ sk_B_1 @ X29))
% 0.20/0.55                 | ~ (r2_hidden @ X29 @ sk_A)
% 0.20/0.55                 | ~ (r2_hidden @ X30 @ sk_A))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.55  thf('27', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('28', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.20/0.55             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.20/0.55           | (v2_funct_1 @ sk_B_1)
% 0.20/0.55           | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.55           | ~ (r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.20/0.55           | ((X0) = (sk_C @ sk_B_1))))
% 0.20/0.55         <= ((![X29 : $i, X30 : $i]:
% 0.20/0.55                (((X30) = (X29))
% 0.20/0.55                 | ((k1_funct_1 @ sk_B_1 @ X30) != (k1_funct_1 @ sk_B_1 @ X29))
% 0.20/0.55                 | ~ (r2_hidden @ X29 @ sk_A)
% 0.20/0.55                 | ~ (r2_hidden @ X30 @ sk_A))))),
% 0.20/0.55      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          ((v2_funct_1 @ sk_B_1)
% 0.20/0.55           | ((X0) = (sk_C @ sk_B_1))
% 0.20/0.55           | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.55           | (v2_funct_1 @ sk_B_1)
% 0.20/0.55           | ((k1_funct_1 @ sk_B_1 @ X0)
% 0.20/0.55               != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 0.20/0.55         <= ((![X29 : $i, X30 : $i]:
% 0.20/0.55                (((X30) = (X29))
% 0.20/0.55                 | ((k1_funct_1 @ sk_B_1 @ X30) != (k1_funct_1 @ sk_B_1 @ X29))
% 0.20/0.55                 | ~ (r2_hidden @ X29 @ sk_A)
% 0.20/0.55                 | ~ (r2_hidden @ X30 @ sk_A))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['23', '29'])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      ((![X0 : $i]:
% 0.20/0.55          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.20/0.55             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.20/0.55           | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.55           | ((X0) = (sk_C @ sk_B_1))
% 0.20/0.55           | (v2_funct_1 @ sk_B_1)))
% 0.20/0.55         <= ((![X29 : $i, X30 : $i]:
% 0.20/0.55                (((X30) = (X29))
% 0.20/0.55                 | ((k1_funct_1 @ sk_B_1 @ X30) != (k1_funct_1 @ sk_B_1 @ X29))
% 0.20/0.55                 | ~ (r2_hidden @ X29 @ sk_A)
% 0.20/0.55                 | ~ (r2_hidden @ X30 @ sk_A))))),
% 0.20/0.55      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      ((((v2_funct_1 @ sk_B_1)
% 0.20/0.55         | ((sk_B @ sk_B_1) = (sk_C @ sk_B_1))
% 0.20/0.55         | ~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_A)))
% 0.20/0.55         <= ((![X29 : $i, X30 : $i]:
% 0.20/0.55                (((X30) = (X29))
% 0.20/0.55                 | ((k1_funct_1 @ sk_B_1 @ X30) != (k1_funct_1 @ sk_B_1 @ X29))
% 0.20/0.55                 | ~ (r2_hidden @ X29 @ sk_A)
% 0.20/0.55                 | ~ (r2_hidden @ X30 @ sk_A))))),
% 0.20/0.55      inference('eq_res', [status(thm)], ['31'])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      (![X19 : $i]:
% 0.20/0.55         ((r2_hidden @ (sk_B @ X19) @ (k1_relat_1 @ X19))
% 0.20/0.55          | (v2_funct_1 @ X19)
% 0.20/0.55          | ~ (v1_funct_1 @ X19)
% 0.20/0.55          | ~ (v1_relat_1 @ X19))),
% 0.20/0.55      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      ((~ (v1_relat_1 @ sk_B_1)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.55        | (v2_funct_1 @ sk_B_1)
% 0.20/0.55        | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.55  thf('36', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('37', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (((v2_funct_1 @ sk_B_1) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      (((((sk_B @ sk_B_1) = (sk_C @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.20/0.55         <= ((![X29 : $i, X30 : $i]:
% 0.20/0.55                (((X30) = (X29))
% 0.20/0.55                 | ((k1_funct_1 @ sk_B_1 @ X30) != (k1_funct_1 @ sk_B_1 @ X29))
% 0.20/0.55                 | ~ (r2_hidden @ X29 @ sk_A)
% 0.20/0.55                 | ~ (r2_hidden @ X30 @ sk_A))))),
% 0.20/0.55      inference('clc', [status(thm)], ['32', '38'])).
% 0.20/0.55  thf('40', plain, (((r2_hidden @ sk_C_1 @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('41', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.20/0.55      inference('split', [status(esa)], ['40'])).
% 0.20/0.55  thf('42', plain,
% 0.20/0.55      ((((sk_B @ sk_B_1) = (sk_C @ sk_B_1)))
% 0.20/0.55         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.20/0.55             (![X29 : $i, X30 : $i]:
% 0.20/0.55                (((X30) = (X29))
% 0.20/0.55                 | ((k1_funct_1 @ sk_B_1 @ X30) != (k1_funct_1 @ sk_B_1 @ X29))
% 0.20/0.55                 | ~ (r2_hidden @ X29 @ sk_A)
% 0.20/0.55                 | ~ (r2_hidden @ X30 @ sk_A))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['39', '41'])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      (![X19 : $i]:
% 0.20/0.55         (((sk_B @ X19) != (sk_C @ X19))
% 0.20/0.55          | (v2_funct_1 @ X19)
% 0.20/0.55          | ~ (v1_funct_1 @ X19)
% 0.20/0.55          | ~ (v1_relat_1 @ X19))),
% 0.20/0.55      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.55  thf('44', plain,
% 0.20/0.55      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1))
% 0.20/0.55         | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.55         | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.55         | (v2_funct_1 @ sk_B_1)))
% 0.20/0.55         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.20/0.55             (![X29 : $i, X30 : $i]:
% 0.20/0.55                (((X30) = (X29))
% 0.20/0.55                 | ((k1_funct_1 @ sk_B_1 @ X30) != (k1_funct_1 @ sk_B_1 @ X29))
% 0.20/0.55                 | ~ (r2_hidden @ X29 @ sk_A)
% 0.20/0.55                 | ~ (r2_hidden @ X30 @ sk_A))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.55  thf('45', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('46', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('47', plain,
% 0.20/0.55      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.20/0.55         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.20/0.55             (![X29 : $i, X30 : $i]:
% 0.20/0.55                (((X30) = (X29))
% 0.20/0.55                 | ((k1_funct_1 @ sk_B_1 @ X30) != (k1_funct_1 @ sk_B_1 @ X29))
% 0.20/0.55                 | ~ (r2_hidden @ X29 @ sk_A)
% 0.20/0.55                 | ~ (r2_hidden @ X30 @ sk_A))))),
% 0.20/0.55      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      (((v2_funct_1 @ sk_B_1))
% 0.20/0.55         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.20/0.55             (![X29 : $i, X30 : $i]:
% 0.20/0.55                (((X30) = (X29))
% 0.20/0.55                 | ((k1_funct_1 @ sk_B_1 @ X30) != (k1_funct_1 @ sk_B_1 @ X29))
% 0.20/0.55                 | ~ (r2_hidden @ X29 @ sk_A)
% 0.20/0.55                 | ~ (r2_hidden @ X30 @ sk_A))))),
% 0.20/0.55      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.55  thf('49', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.20/0.55      inference('split', [status(esa)], ['40'])).
% 0.20/0.55  thf('50', plain,
% 0.20/0.55      (~
% 0.20/0.55       (![X29 : $i, X30 : $i]:
% 0.20/0.55          (((X30) = (X29))
% 0.20/0.55           | ((k1_funct_1 @ sk_B_1 @ X30) != (k1_funct_1 @ sk_B_1 @ X29))
% 0.20/0.55           | ~ (r2_hidden @ X29 @ sk_A)
% 0.20/0.55           | ~ (r2_hidden @ X30 @ sk_A))) | 
% 0.20/0.55       ((v2_funct_1 @ sk_B_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.55  thf('51', plain, (((r2_hidden @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('52', plain, (((r2_hidden @ sk_D @ sk_A))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['3', '50', '51'])).
% 0.20/0.55  thf('53', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['1', '52'])).
% 0.20/0.55  thf('54', plain,
% 0.20/0.55      (((r2_hidden @ sk_C_1 @ sk_A)) <= (((r2_hidden @ sk_C_1 @ sk_A)))),
% 0.20/0.55      inference('split', [status(esa)], ['40'])).
% 0.20/0.55  thf('55', plain, (((r2_hidden @ sk_C_1 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.20/0.55      inference('split', [status(esa)], ['40'])).
% 0.20/0.55  thf('56', plain, (((r2_hidden @ sk_C_1 @ sk_A))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['3', '50', '55'])).
% 0.20/0.55  thf('57', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['54', '56'])).
% 0.20/0.55  thf('58', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t32_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.55       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.20/0.55         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.55           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.20/0.55             ( C ) ) ) ) ))).
% 0.20/0.55  thf('59', plain,
% 0.20/0.55      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X25 @ X26)
% 0.20/0.55          | ((X27) = (k1_xboole_0))
% 0.20/0.55          | ~ (v1_funct_1 @ X28)
% 0.20/0.55          | ~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.20/0.55          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.20/0.55          | ((k1_funct_1 @ (k2_funct_1 @ X28) @ (k1_funct_1 @ X28 @ X25))
% 0.20/0.55              = (X25))
% 0.20/0.55          | ~ (v2_funct_1 @ X28))),
% 0.20/0.55      inference('cnf', [status(esa)], [t32_funct_2])).
% 0.20/0.55  thf('60', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v2_funct_1 @ sk_B_1)
% 0.20/0.55          | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.20/0.55              = (X0))
% 0.20/0.55          | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.20/0.55          | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.55          | ((sk_A) = (k1_xboole_0))
% 0.20/0.55          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.55  thf('61', plain, (((v2_funct_1 @ sk_B_1)) <= (((v2_funct_1 @ sk_B_1)))),
% 0.20/0.55      inference('split', [status(esa)], ['2'])).
% 0.20/0.55  thf('62', plain, (((v2_funct_1 @ sk_B_1))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['3', '50'])).
% 0.20/0.55  thf('63', plain, ((v2_funct_1 @ sk_B_1)),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['61', '62'])).
% 0.20/0.55  thf('64', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('65', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('66', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.20/0.55            = (X0))
% 0.20/0.55          | ((sk_A) = (k1_xboole_0))
% 0.20/0.55          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['60', '63', '64', '65'])).
% 0.20/0.55  thf('67', plain,
% 0.20/0.55      ((((sk_A) = (k1_xboole_0))
% 0.20/0.55        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_1))
% 0.20/0.55            = (sk_C_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['57', '66'])).
% 0.20/0.55  thf('68', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['1', '52'])).
% 0.20/0.55  thf('69', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.20/0.55            = (X0))
% 0.20/0.55          | ((sk_A) = (k1_xboole_0))
% 0.20/0.55          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['60', '63', '64', '65'])).
% 0.20/0.55  thf('70', plain,
% 0.20/0.55      ((((sk_A) = (k1_xboole_0))
% 0.20/0.55        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.20/0.55            = (sk_D)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.55  thf('71', plain,
% 0.20/0.55      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.20/0.55        | ~ (v2_funct_1 @ sk_B_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('72', plain,
% 0.20/0.55      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D)))
% 0.20/0.55         <= ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))))),
% 0.20/0.55      inference('split', [status(esa)], ['71'])).
% 0.20/0.55  thf('73', plain,
% 0.20/0.55      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))) | 
% 0.20/0.55       ~ ((v2_funct_1 @ sk_B_1))),
% 0.20/0.55      inference('split', [status(esa)], ['71'])).
% 0.20/0.55  thf('74', plain,
% 0.20/0.55      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D)))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['3', '50', '73'])).
% 0.20/0.55  thf('75', plain,
% 0.20/0.55      (((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['72', '74'])).
% 0.20/0.55  thf('76', plain,
% 0.20/0.55      ((((sk_A) = (k1_xboole_0))
% 0.20/0.55        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_1))
% 0.20/0.55            = (sk_D)))),
% 0.20/0.55      inference('demod', [status(thm)], ['70', '75'])).
% 0.20/0.55  thf('77', plain,
% 0.20/0.55      ((((sk_C_1) = (sk_D))
% 0.20/0.55        | ((sk_A) = (k1_xboole_0))
% 0.20/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['67', '76'])).
% 0.20/0.55  thf('78', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_1) = (sk_D)))),
% 0.20/0.55      inference('simplify', [status(thm)], ['77'])).
% 0.20/0.55  thf('79', plain, ((((sk_C_1) != (sk_D)) | ~ (v2_funct_1 @ sk_B_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('80', plain, ((((sk_C_1) != (sk_D))) <= (~ (((sk_C_1) = (sk_D))))),
% 0.20/0.55      inference('split', [status(esa)], ['79'])).
% 0.20/0.55  thf('81', plain, (~ (((sk_C_1) = (sk_D))) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.20/0.55      inference('split', [status(esa)], ['79'])).
% 0.20/0.55  thf('82', plain, (~ (((sk_C_1) = (sk_D)))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['3', '50', '81'])).
% 0.20/0.55  thf('83', plain, (((sk_C_1) != (sk_D))),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['80', '82'])).
% 0.20/0.55  thf('84', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['78', '83'])).
% 0.20/0.55  thf('85', plain, ((r2_hidden @ sk_D @ k1_xboole_0)),
% 0.20/0.55      inference('demod', [status(thm)], ['53', '84'])).
% 0.20/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.55  thf('86', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.20/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.55  thf('87', plain,
% 0.20/0.55      (![X7 : $i, X9 : $i]:
% 0.20/0.55         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.55  thf('88', plain,
% 0.20/0.55      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['86', '87'])).
% 0.20/0.55  thf('89', plain,
% 0.20/0.55      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X4 @ X5)
% 0.20/0.55          | (r2_hidden @ X4 @ X6)
% 0.20/0.55          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.20/0.55      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.55  thf('90', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['88', '89'])).
% 0.20/0.55  thf('91', plain, (![X0 : $i]: (r2_hidden @ sk_D @ X0)),
% 0.20/0.55      inference('sup-', [status(thm)], ['85', '90'])).
% 0.20/0.55  thf(d10_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.55  thf('92', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.55  thf('93', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.55      inference('simplify', [status(thm)], ['92'])).
% 0.20/0.55  thf('94', plain,
% 0.20/0.55      (![X7 : $i, X9 : $i]:
% 0.20/0.55         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.55  thf('95', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['93', '94'])).
% 0.20/0.55  thf(t4_subset, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.55       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.55  thf('96', plain,
% 0.20/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X10 @ X11)
% 0.20/0.55          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.20/0.55          | (m1_subset_1 @ X10 @ X12))),
% 0.20/0.55      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.55  thf('97', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['95', '96'])).
% 0.20/0.55  thf('98', plain, (![X0 : $i]: (m1_subset_1 @ sk_D @ X0)),
% 0.20/0.55      inference('sup-', [status(thm)], ['91', '97'])).
% 0.20/0.55  thf('99', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i]:
% 0.20/0.55         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.55  thf('100', plain, (![X0 : $i]: (r1_tarski @ sk_D @ X0)),
% 0.20/0.55      inference('sup-', [status(thm)], ['98', '99'])).
% 0.20/0.55  thf('101', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.20/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.55  thf('102', plain,
% 0.20/0.55      (![X0 : $i, X2 : $i]:
% 0.20/0.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.55  thf('103', plain,
% 0.20/0.55      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['101', '102'])).
% 0.20/0.55  thf('104', plain, (((sk_D) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['100', '103'])).
% 0.20/0.55  thf('105', plain, (((sk_C_1) != (sk_D))),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['80', '82'])).
% 0.20/0.55  thf('106', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['54', '56'])).
% 0.20/0.55  thf('107', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['78', '83'])).
% 0.20/0.55  thf('108', plain, ((r2_hidden @ sk_C_1 @ k1_xboole_0)),
% 0.20/0.55      inference('demod', [status(thm)], ['106', '107'])).
% 0.20/0.55  thf('109', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['88', '89'])).
% 0.20/0.55  thf('110', plain, (![X0 : $i]: (r2_hidden @ sk_C_1 @ X0)),
% 0.20/0.55      inference('sup-', [status(thm)], ['108', '109'])).
% 0.20/0.55  thf('111', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['95', '96'])).
% 0.20/0.55  thf('112', plain, (![X0 : $i]: (m1_subset_1 @ sk_C_1 @ X0)),
% 0.20/0.55      inference('sup-', [status(thm)], ['110', '111'])).
% 0.20/0.55  thf('113', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i]:
% 0.20/0.55         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.55  thf('114', plain, (![X0 : $i]: (r1_tarski @ sk_C_1 @ X0)),
% 0.20/0.55      inference('sup-', [status(thm)], ['112', '113'])).
% 0.20/0.55  thf('115', plain,
% 0.20/0.55      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['101', '102'])).
% 0.20/0.55  thf('116', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['114', '115'])).
% 0.20/0.55  thf('117', plain, (((k1_xboole_0) != (sk_D))),
% 0.20/0.55      inference('demod', [status(thm)], ['105', '116'])).
% 0.20/0.55  thf('118', plain, ($false),
% 0.20/0.55      inference('simplify_reflect-', [status(thm)], ['104', '117'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
