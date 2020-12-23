%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uV83q8kFRm

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 995 expanded)
%              Number of leaves         :   31 ( 294 expanded)
%              Depth                    :   26
%              Number of atoms          : 1062 (15320 expanded)
%              Number of equality atoms :   88 ( 993 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
   <= ( r2_hidden @ sk_C_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C_2 )
   <= ( r2_hidden @ sk_C_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X27: $i,X28: $i] :
      ( ( X28 = X27 )
      | ( ( k1_funct_1 @ sk_B_1 @ X28 )
       != ( k1_funct_1 @ sk_B_1 @ X27 ) )
      | ~ ( r2_hidden @ X27 @ sk_A )
      | ~ ( r2_hidden @ X28 @ sk_A )
      | ( v2_funct_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
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
    ! [X12: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('9',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('23',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','23','24'])).

thf('26',plain,(
    ! [X12: $i] :
      ( ( ( k1_funct_1 @ X12 @ ( sk_B @ X12 ) )
        = ( k1_funct_1 @ X12 @ ( sk_C_1 @ X12 ) ) )
      | ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('27',plain,
    ( ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) )
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ~ ( v1_relat_1 @ sk_B_1 )
        | ~ ( v1_funct_1 @ sk_B_1 )
        | ( v2_funct_1 @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) @ sk_A )
        | ( X0
          = ( sk_C_1 @ sk_B_1 ) ) )
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['21','22'])).

thf('30',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ( v2_funct_1 @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) @ sk_A )
        | ( X0
          = ( sk_C_1 @ sk_B_1 ) ) )
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( v2_funct_1 @ sk_B_1 )
        | ( X0
          = ( sk_C_1 @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( v2_funct_1 @ sk_B_1 )
        | ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( X0
          = ( sk_C_1 @ sk_B_1 ) )
        | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( v2_funct_1 @ sk_B_1 )
      | ( ( sk_B @ sk_B_1 )
        = ( sk_C_1 @ sk_B_1 ) )
      | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) )
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['33'])).

thf('35',plain,(
    ! [X12: $i] :
      ( ( r2_hidden @ ( sk_B @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['21','22'])).

thf('39',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( ( ( sk_B @ sk_B_1 )
        = ( sk_C_1 @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
    inference(clc,[status(thm)],['34','40'])).

thf('42',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ( ( sk_B @ sk_B_1 )
      = ( sk_C_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X27: $i,X28: $i] :
          ( ( X28 = X27 )
          | ( ( k1_funct_1 @ sk_B_1 @ X28 )
           != ( k1_funct_1 @ sk_B_1 @ X27 ) )
          | ~ ( r2_hidden @ X27 @ sk_A )
          | ~ ( r2_hidden @ X28 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X12: $i] :
      ( ( ( sk_B @ X12 )
       != ( sk_C_1 @ X12 ) )
      | ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('45',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X27: $i,X28: $i] :
          ( ( X28 = X27 )
          | ( ( k1_funct_1 @ sk_B_1 @ X28 )
           != ( k1_funct_1 @ sk_B_1 @ X27 ) )
          | ~ ( r2_hidden @ X27 @ sk_A )
          | ~ ( r2_hidden @ X28 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['21','22'])).

thf('47',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X27: $i,X28: $i] :
          ( ( X28 = X27 )
          | ( ( k1_funct_1 @ sk_B_1 @ X28 )
           != ( k1_funct_1 @ sk_B_1 @ X27 ) )
          | ~ ( r2_hidden @ X27 @ sk_A )
          | ~ ( r2_hidden @ X28 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X27: $i,X28: $i] :
          ( ( X28 = X27 )
          | ( ( k1_funct_1 @ sk_B_1 @ X28 )
           != ( k1_funct_1 @ sk_B_1 @ X27 ) )
          | ~ ( r2_hidden @ X27 @ sk_A )
          | ~ ( r2_hidden @ X28 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,
    ( ~ ! [X27: $i,X28: $i] :
          ( ( X28 = X27 )
          | ( ( k1_funct_1 @ sk_B_1 @ X28 )
           != ( k1_funct_1 @ sk_B_1 @ X27 ) )
          | ~ ( r2_hidden @ X27 @ sk_A )
          | ~ ( r2_hidden @ X28 @ sk_A ) )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','51','52'])).

thf('54',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','53'])).

thf('55',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
   <= ( r2_hidden @ sk_C_2 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('56',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','51','52'])).

thf('57',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference(simpl_trail,[status(thm)],['55','56'])).

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
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ( X25 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ X26 ) @ ( k1_funct_1 @ X26 @ X23 ) )
        = X23 )
      | ~ ( v2_funct_1 @ X26 ) ) ),
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
    inference(split,[status(esa)],['4'])).

thf('62',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['5','51'])).

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
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_2 ) )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['57','66'])).

thf('68',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
   <= ( r2_hidden @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['68'])).

thf('70',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['68'])).

thf('71',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','51','70'])).

thf('72',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['69','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','63','64','65'])).

thf('74',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['75'])).

thf('77',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['75'])).

thf('78',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['5','51','77'])).

thf('79',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['76','78'])).

thf('80',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_2 ) )
      = sk_D ) ),
    inference(demod,[status(thm)],['74','79'])).

thf('81',plain,
    ( ( sk_C_2 = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','80'])).

thf('82',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( sk_C_2 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( sk_C_2 != sk_D )
   <= ( sk_C_2 != sk_D ) ),
    inference(split,[status(esa)],['83'])).

thf('85',plain,
    ( ( sk_C_2 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['83'])).

thf('86',plain,(
    sk_C_2 != sk_D ),
    inference('sat_resolution*',[status(thm)],['5','51','85'])).

thf('87',plain,(
    sk_C_2 != sk_D ),
    inference(simpl_trail,[status(thm)],['84','86'])).

thf('88',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['82','87'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('89',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['54','88','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uV83q8kFRm
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:55:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 136 iterations in 0.073s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.53  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.53  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.20/0.53  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(t77_funct_2, conjecture,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.53       ( ( v2_funct_1 @ B ) <=>
% 0.20/0.53         ( ![C:$i,D:$i]:
% 0.20/0.53           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.20/0.53               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.20/0.53             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i]:
% 0.20/0.53        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.53            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.53          ( ( v2_funct_1 @ B ) <=>
% 0.20/0.53            ( ![C:$i,D:$i]:
% 0.20/0.53              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.20/0.53                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.20/0.53                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t77_funct_2])).
% 0.20/0.53  thf('0', plain, (((r2_hidden @ sk_C_2 @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (((r2_hidden @ sk_C_2 @ sk_A)) <= (((r2_hidden @ sk_C_2 @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf(t7_ordinal1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      ((~ (r1_tarski @ sk_A @ sk_C_2)) <= (((r2_hidden @ sk_C_2 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X27 : $i, X28 : $i]:
% 0.20/0.53         (((X28) = (X27))
% 0.20/0.53          | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.20/0.53          | ~ (r2_hidden @ X27 @ sk_A)
% 0.20/0.53          | ~ (r2_hidden @ X28 @ sk_A)
% 0.20/0.53          | (v2_funct_1 @ sk_B_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (((v2_funct_1 @ sk_B_1)) | 
% 0.20/0.53       (![X27 : $i, X28 : $i]:
% 0.20/0.53          (((X28) = (X27))
% 0.20/0.53           | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.20/0.53           | ~ (r2_hidden @ X27 @ sk_A)
% 0.20/0.53           | ~ (r2_hidden @ X28 @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['4'])).
% 0.20/0.53  thf(d8_funct_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.53       ( ( v2_funct_1 @ A ) <=>
% 0.20/0.53         ( ![B:$i,C:$i]:
% 0.20/0.53           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.53               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.53               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.20/0.53             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X12 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_C_1 @ X12) @ (k1_relat_1 @ X12))
% 0.20/0.53          | (v2_funct_1 @ X12)
% 0.20/0.53          | ~ (v1_funct_1 @ X12)
% 0.20/0.53          | ~ (v1_relat_1 @ X12))),
% 0.20/0.53      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(dt_k1_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.53         ((m1_subset_1 @ (k1_relset_1 @ X17 @ X18 @ X19) @ (k1_zfmisc_1 @ X17))
% 0.20/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B_1) @ 
% 0.20/0.53        (k1_zfmisc_1 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.53         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.20/0.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      ((m1_subset_1 @ (k1_relat_1 @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['9', '12'])).
% 0.20/0.53  thf(t3_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i]:
% 0.20/0.53         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('15', plain, ((r1_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf(d3_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.53          | (r2_hidden @ X0 @ X2)
% 0.20/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ sk_B_1)
% 0.20/0.53        | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.53        | (v2_funct_1 @ sk_B_1)
% 0.20/0.53        | (r2_hidden @ (sk_C_1 @ sk_B_1) @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '17'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(cc2_relat_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X8 : $i, X9 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.20/0.53          | (v1_relat_1 @ X8)
% 0.20/0.53          | ~ (v1_relat_1 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf(fc6_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.53  thf('23', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('24', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (((v2_funct_1 @ sk_B_1) | (r2_hidden @ (sk_C_1 @ sk_B_1) @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['18', '23', '24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X12 : $i]:
% 0.20/0.53         (((k1_funct_1 @ X12 @ (sk_B @ X12))
% 0.20/0.53            = (k1_funct_1 @ X12 @ (sk_C_1 @ X12)))
% 0.20/0.53          | (v2_funct_1 @ X12)
% 0.20/0.53          | ~ (v1_funct_1 @ X12)
% 0.20/0.53          | ~ (v1_relat_1 @ X12))),
% 0.20/0.53      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      ((![X27 : $i, X28 : $i]:
% 0.20/0.53          (((X28) = (X27))
% 0.20/0.53           | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.20/0.53           | ~ (r2_hidden @ X27 @ sk_A)
% 0.20/0.53           | ~ (r2_hidden @ X28 @ sk_A)))
% 0.20/0.53         <= ((![X27 : $i, X28 : $i]:
% 0.20/0.53                (((X28) = (X27))
% 0.20/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.20/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.20/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['4'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.20/0.53             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.20/0.53           | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.53           | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.53           | (v2_funct_1 @ sk_B_1)
% 0.20/0.53           | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.53           | ~ (r2_hidden @ (sk_C_1 @ sk_B_1) @ sk_A)
% 0.20/0.53           | ((X0) = (sk_C_1 @ sk_B_1))))
% 0.20/0.53         <= ((![X27 : $i, X28 : $i]:
% 0.20/0.53                (((X28) = (X27))
% 0.20/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.20/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.20/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('30', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.20/0.53             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.20/0.53           | (v2_funct_1 @ sk_B_1)
% 0.20/0.53           | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.53           | ~ (r2_hidden @ (sk_C_1 @ sk_B_1) @ sk_A)
% 0.20/0.53           | ((X0) = (sk_C_1 @ sk_B_1))))
% 0.20/0.53         <= ((![X27 : $i, X28 : $i]:
% 0.20/0.53                (((X28) = (X27))
% 0.20/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.20/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.20/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((v2_funct_1 @ sk_B_1)
% 0.20/0.53           | ((X0) = (sk_C_1 @ sk_B_1))
% 0.20/0.53           | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.53           | (v2_funct_1 @ sk_B_1)
% 0.20/0.53           | ((k1_funct_1 @ sk_B_1 @ X0)
% 0.20/0.53               != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 0.20/0.53         <= ((![X27 : $i, X28 : $i]:
% 0.20/0.53                (((X28) = (X27))
% 0.20/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.20/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.20/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['25', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.20/0.53             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.20/0.53           | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.53           | ((X0) = (sk_C_1 @ sk_B_1))
% 0.20/0.53           | (v2_funct_1 @ sk_B_1)))
% 0.20/0.53         <= ((![X27 : $i, X28 : $i]:
% 0.20/0.53                (((X28) = (X27))
% 0.20/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.20/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.20/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      ((((v2_funct_1 @ sk_B_1)
% 0.20/0.53         | ((sk_B @ sk_B_1) = (sk_C_1 @ sk_B_1))
% 0.20/0.53         | ~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_A)))
% 0.20/0.53         <= ((![X27 : $i, X28 : $i]:
% 0.20/0.53                (((X28) = (X27))
% 0.20/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.20/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.20/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.20/0.53      inference('eq_res', [status(thm)], ['33'])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X12 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_B @ X12) @ (k1_relat_1 @ X12))
% 0.20/0.53          | (v2_funct_1 @ X12)
% 0.20/0.53          | ~ (v1_funct_1 @ X12)
% 0.20/0.53          | ~ (v1_relat_1 @ X12))),
% 0.20/0.53      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ sk_B_1)
% 0.20/0.53        | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.53        | (v2_funct_1 @ sk_B_1)
% 0.20/0.53        | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf('38', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('39', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (((v2_funct_1 @ sk_B_1) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (((((sk_B @ sk_B_1) = (sk_C_1 @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.20/0.53         <= ((![X27 : $i, X28 : $i]:
% 0.20/0.53                (((X28) = (X27))
% 0.20/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.20/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.20/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.20/0.53      inference('clc', [status(thm)], ['34', '40'])).
% 0.20/0.53  thf('42', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      ((((sk_B @ sk_B_1) = (sk_C_1 @ sk_B_1)))
% 0.20/0.53         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.20/0.53             (![X27 : $i, X28 : $i]:
% 0.20/0.53                (((X28) = (X27))
% 0.20/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.20/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.20/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (![X12 : $i]:
% 0.20/0.53         (((sk_B @ X12) != (sk_C_1 @ X12))
% 0.20/0.53          | (v2_funct_1 @ X12)
% 0.20/0.53          | ~ (v1_funct_1 @ X12)
% 0.20/0.53          | ~ (v1_relat_1 @ X12))),
% 0.20/0.53      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1))
% 0.20/0.53         | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.53         | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.53         | (v2_funct_1 @ sk_B_1)))
% 0.20/0.53         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.20/0.53             (![X27 : $i, X28 : $i]:
% 0.20/0.53                (((X28) = (X27))
% 0.20/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.20/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.20/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.53  thf('46', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('47', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.20/0.53         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.20/0.53             (![X27 : $i, X28 : $i]:
% 0.20/0.53                (((X28) = (X27))
% 0.20/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.20/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.20/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (((v2_funct_1 @ sk_B_1))
% 0.20/0.53         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.20/0.53             (![X27 : $i, X28 : $i]:
% 0.20/0.53                (((X28) = (X27))
% 0.20/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.20/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.20/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.53  thf('50', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('51', plain,
% 0.20/0.54      (~
% 0.20/0.54       (![X27 : $i, X28 : $i]:
% 0.20/0.54          (((X28) = (X27))
% 0.20/0.54           | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.20/0.54           | ~ (r2_hidden @ X27 @ sk_A)
% 0.20/0.54           | ~ (r2_hidden @ X28 @ sk_A))) | 
% 0.20/0.54       ((v2_funct_1 @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.54  thf('52', plain, (((r2_hidden @ sk_C_2 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('53', plain, (((r2_hidden @ sk_C_2 @ sk_A))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['5', '51', '52'])).
% 0.20/0.54  thf('54', plain, (~ (r1_tarski @ sk_A @ sk_C_2)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['3', '53'])).
% 0.20/0.54  thf('55', plain,
% 0.20/0.54      (((r2_hidden @ sk_C_2 @ sk_A)) <= (((r2_hidden @ sk_C_2 @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['0'])).
% 0.20/0.54  thf('56', plain, (((r2_hidden @ sk_C_2 @ sk_A))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['5', '51', '52'])).
% 0.20/0.54  thf('57', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['55', '56'])).
% 0.20/0.54  thf('58', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(t32_funct_2, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.54       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.20/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.54           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.20/0.54             ( C ) ) ) ) ))).
% 0.20/0.54  thf('59', plain,
% 0.20/0.54      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X23 @ X24)
% 0.20/0.54          | ((X25) = (k1_xboole_0))
% 0.20/0.54          | ~ (v1_funct_1 @ X26)
% 0.20/0.54          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.20/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.20/0.54          | ((k1_funct_1 @ (k2_funct_1 @ X26) @ (k1_funct_1 @ X26 @ X23))
% 0.20/0.54              = (X23))
% 0.20/0.54          | ~ (v2_funct_1 @ X26))),
% 0.20/0.54      inference('cnf', [status(esa)], [t32_funct_2])).
% 0.20/0.54  thf('60', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (v2_funct_1 @ sk_B_1)
% 0.20/0.54          | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.20/0.54              = (X0))
% 0.20/0.54          | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.20/0.54          | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.54          | ((sk_A) = (k1_xboole_0))
% 0.20/0.54          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.54  thf('61', plain, (((v2_funct_1 @ sk_B_1)) <= (((v2_funct_1 @ sk_B_1)))),
% 0.20/0.54      inference('split', [status(esa)], ['4'])).
% 0.20/0.54  thf('62', plain, (((v2_funct_1 @ sk_B_1))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['5', '51'])).
% 0.20/0.54  thf('63', plain, ((v2_funct_1 @ sk_B_1)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['61', '62'])).
% 0.20/0.54  thf('64', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('65', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('66', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.20/0.54            = (X0))
% 0.20/0.54          | ((sk_A) = (k1_xboole_0))
% 0.20/0.54          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['60', '63', '64', '65'])).
% 0.20/0.54  thf('67', plain,
% 0.20/0.54      ((((sk_A) = (k1_xboole_0))
% 0.20/0.54        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_2))
% 0.20/0.54            = (sk_C_2)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['57', '66'])).
% 0.20/0.54  thf('68', plain, (((r2_hidden @ sk_D @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('69', plain,
% 0.20/0.54      (((r2_hidden @ sk_D @ sk_A)) <= (((r2_hidden @ sk_D @ sk_A)))),
% 0.20/0.54      inference('split', [status(esa)], ['68'])).
% 0.20/0.54  thf('70', plain, (((r2_hidden @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.20/0.54      inference('split', [status(esa)], ['68'])).
% 0.20/0.54  thf('71', plain, (((r2_hidden @ sk_D @ sk_A))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['5', '51', '70'])).
% 0.20/0.54  thf('72', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['69', '71'])).
% 0.20/0.54  thf('73', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.20/0.54            = (X0))
% 0.20/0.54          | ((sk_A) = (k1_xboole_0))
% 0.20/0.54          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['60', '63', '64', '65'])).
% 0.20/0.54  thf('74', plain,
% 0.20/0.54      ((((sk_A) = (k1_xboole_0))
% 0.20/0.54        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.20/0.54            = (sk_D)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.54  thf('75', plain,
% 0.20/0.54      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.20/0.54        | ~ (v2_funct_1 @ sk_B_1))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('76', plain,
% 0.20/0.54      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D)))
% 0.20/0.54         <= ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))))),
% 0.20/0.54      inference('split', [status(esa)], ['75'])).
% 0.20/0.54  thf('77', plain,
% 0.20/0.54      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))) | 
% 0.20/0.54       ~ ((v2_funct_1 @ sk_B_1))),
% 0.20/0.54      inference('split', [status(esa)], ['75'])).
% 0.20/0.54  thf('78', plain,
% 0.20/0.54      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D)))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['5', '51', '77'])).
% 0.20/0.54  thf('79', plain,
% 0.20/0.54      (((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['76', '78'])).
% 0.20/0.54  thf('80', plain,
% 0.20/0.54      ((((sk_A) = (k1_xboole_0))
% 0.20/0.54        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_2))
% 0.20/0.54            = (sk_D)))),
% 0.20/0.54      inference('demod', [status(thm)], ['74', '79'])).
% 0.20/0.54  thf('81', plain,
% 0.20/0.54      ((((sk_C_2) = (sk_D))
% 0.20/0.54        | ((sk_A) = (k1_xboole_0))
% 0.20/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['67', '80'])).
% 0.20/0.54  thf('82', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_2) = (sk_D)))),
% 0.20/0.54      inference('simplify', [status(thm)], ['81'])).
% 0.20/0.54  thf('83', plain, ((((sk_C_2) != (sk_D)) | ~ (v2_funct_1 @ sk_B_1))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('84', plain, ((((sk_C_2) != (sk_D))) <= (~ (((sk_C_2) = (sk_D))))),
% 0.20/0.54      inference('split', [status(esa)], ['83'])).
% 0.20/0.54  thf('85', plain, (~ (((sk_C_2) = (sk_D))) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.20/0.54      inference('split', [status(esa)], ['83'])).
% 0.20/0.54  thf('86', plain, (~ (((sk_C_2) = (sk_D)))),
% 0.20/0.54      inference('sat_resolution*', [status(thm)], ['5', '51', '85'])).
% 0.20/0.54  thf('87', plain, (((sk_C_2) != (sk_D))),
% 0.20/0.54      inference('simpl_trail', [status(thm)], ['84', '86'])).
% 0.20/0.54  thf('88', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['82', '87'])).
% 0.20/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.54  thf('89', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.20/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.54  thf('90', plain, ($false),
% 0.20/0.54      inference('demod', [status(thm)], ['54', '88', '89'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
