%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YtiIft2lsH

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:52 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 957 expanded)
%              Number of leaves         :   31 ( 282 expanded)
%              Depth                    :   27
%              Number of atoms          : 1040 (14975 expanded)
%              Number of equality atoms :   85 ( 951 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ( ( r2_hidden @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
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
    ( ~ ( r1_tarski @ sk_A @ sk_C_1 )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
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
      ( ( r2_hidden @ ( sk_C @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('9',plain,(
    v4_relat_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['11','14'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
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
    inference('sup-',[status(thm)],['6','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('22',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X12: $i] :
      ( ( ( k1_funct_1 @ X12 @ ( sk_B @ X12 ) )
        = ( k1_funct_1 @ X12 @ ( sk_C @ X12 ) ) )
      | ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('25',plain,
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
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['12','13'])).

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
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
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
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_1 ) )
        | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( v2_funct_1 @ sk_B_1 )
      | ( ( sk_B @ sk_B_1 )
        = ( sk_C @ sk_B_1 ) )
      | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) )
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['31'])).

thf('33',plain,(
    ! [X12: $i] :
      ( ( r2_hidden @ ( sk_B @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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
    inference('sup-',[status(thm)],['12','13'])).

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
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
    inference(clc,[status(thm)],['32','38'])).

thf('40',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ( ( sk_B @ sk_B_1 )
      = ( sk_C @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X27: $i,X28: $i] :
          ( ( X28 = X27 )
          | ( ( k1_funct_1 @ sk_B_1 @ X28 )
           != ( k1_funct_1 @ sk_B_1 @ X27 ) )
          | ~ ( r2_hidden @ X27 @ sk_A )
          | ~ ( r2_hidden @ X28 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X12: $i] :
      ( ( ( sk_B @ X12 )
       != ( sk_C @ X12 ) )
      | ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('43',plain,
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
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('45',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
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
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X27: $i,X28: $i] :
          ( ( X28 = X27 )
          | ( ( k1_funct_1 @ sk_B_1 @ X28 )
           != ( k1_funct_1 @ sk_B_1 @ X27 ) )
          | ~ ( r2_hidden @ X27 @ sk_A )
          | ~ ( r2_hidden @ X28 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ~ ! [X27: $i,X28: $i] :
          ( ( X28 = X27 )
          | ( ( k1_funct_1 @ sk_B_1 @ X28 )
           != ( k1_funct_1 @ sk_B_1 @ X27 ) )
          | ~ ( r2_hidden @ X27 @ sk_A )
          | ~ ( r2_hidden @ X28 @ sk_A ) )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','49','50'])).

thf('52',plain,(
    ~ ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['3','51'])).

thf('53',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('54',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','49','50'])).

thf('55',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['53','54'])).

thf('56',plain,(
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

thf('57',plain,(
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

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['4'])).

thf('60',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['5','49'])).

thf('61',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','61','62','63'])).

thf('65',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['55','64'])).

thf('66',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
   <= ( r2_hidden @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['66'])).

thf('68',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['66'])).

thf('69',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','49','68'])).

thf('70',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['67','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','61','62','63'])).

thf('72',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['73'])).

thf('75',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['73'])).

thf('76',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['5','49','75'])).

thf('77',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['74','76'])).

thf('78',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_1 ) )
      = sk_D ) ),
    inference(demod,[status(thm)],['72','77'])).

thf('79',plain,
    ( ( sk_C_1 = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','78'])).

thf('80',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( sk_C_1 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( sk_C_1 != sk_D )
   <= ( sk_C_1 != sk_D ) ),
    inference(split,[status(esa)],['81'])).

thf('83',plain,
    ( ( sk_C_1 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['81'])).

thf('84',plain,(
    sk_C_1 != sk_D ),
    inference('sat_resolution*',[status(thm)],['5','49','83'])).

thf('85',plain,(
    sk_C_1 != sk_D ),
    inference(simpl_trail,[status(thm)],['82','84'])).

thf('86',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['80','85'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('87',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('88',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('89',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['52','86','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YtiIft2lsH
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.19/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.51  % Solved by: fo/fo7.sh
% 0.19/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.51  % done 138 iterations in 0.057s
% 0.19/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.51  % SZS output start Refutation
% 0.19/0.51  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.19/0.51  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.19/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.51  thf(sk_C_type, type, sk_C: $i > $i).
% 0.19/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.51  thf(t77_funct_2, conjecture,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.19/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.19/0.51       ( ( v2_funct_1 @ B ) <=>
% 0.19/0.51         ( ![C:$i,D:$i]:
% 0.19/0.51           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.19/0.51               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.19/0.51             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.19/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.51    (~( ![A:$i,B:$i]:
% 0.19/0.51        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.19/0.51            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.19/0.51          ( ( v2_funct_1 @ B ) <=>
% 0.19/0.51            ( ![C:$i,D:$i]:
% 0.19/0.51              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.19/0.51                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.19/0.51                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.19/0.51    inference('cnf.neg', [status(esa)], [t77_funct_2])).
% 0.19/0.51  thf('0', plain, (((r2_hidden @ sk_C_1 @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('1', plain,
% 0.19/0.51      (((r2_hidden @ sk_C_1 @ sk_A)) <= (((r2_hidden @ sk_C_1 @ sk_A)))),
% 0.19/0.51      inference('split', [status(esa)], ['0'])).
% 0.19/0.51  thf(t7_ordinal1, axiom,
% 0.19/0.51    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.51  thf('2', plain,
% 0.19/0.51      (![X15 : $i, X16 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X15 @ X16) | ~ (r1_tarski @ X16 @ X15))),
% 0.19/0.51      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.19/0.51  thf('3', plain,
% 0.19/0.51      ((~ (r1_tarski @ sk_A @ sk_C_1)) <= (((r2_hidden @ sk_C_1 @ sk_A)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.51  thf('4', plain,
% 0.19/0.51      (![X27 : $i, X28 : $i]:
% 0.19/0.51         (((X28) = (X27))
% 0.19/0.51          | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.19/0.51          | ~ (r2_hidden @ X27 @ sk_A)
% 0.19/0.51          | ~ (r2_hidden @ X28 @ sk_A)
% 0.19/0.51          | (v2_funct_1 @ sk_B_1))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('5', plain,
% 0.19/0.51      (((v2_funct_1 @ sk_B_1)) | 
% 0.19/0.51       (![X27 : $i, X28 : $i]:
% 0.19/0.51          (((X28) = (X27))
% 0.19/0.51           | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.19/0.51           | ~ (r2_hidden @ X27 @ sk_A)
% 0.19/0.51           | ~ (r2_hidden @ X28 @ sk_A)))),
% 0.19/0.51      inference('split', [status(esa)], ['4'])).
% 0.19/0.51  thf(d8_funct_1, axiom,
% 0.19/0.51    (![A:$i]:
% 0.19/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.51       ( ( v2_funct_1 @ A ) <=>
% 0.19/0.51         ( ![B:$i,C:$i]:
% 0.19/0.51           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.19/0.51               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.19/0.51               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.19/0.51             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.19/0.51  thf('6', plain,
% 0.19/0.51      (![X12 : $i]:
% 0.19/0.51         ((r2_hidden @ (sk_C @ X12) @ (k1_relat_1 @ X12))
% 0.19/0.51          | (v2_funct_1 @ X12)
% 0.19/0.51          | ~ (v1_funct_1 @ X12)
% 0.19/0.51          | ~ (v1_relat_1 @ X12))),
% 0.19/0.51      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.19/0.51  thf('7', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(cc2_relset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.51  thf('8', plain,
% 0.19/0.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.51         ((v4_relat_1 @ X20 @ X21)
% 0.19/0.51          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.19/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.51  thf('9', plain, ((v4_relat_1 @ sk_B_1 @ sk_A)),
% 0.19/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.51  thf(d18_relat_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( v1_relat_1 @ B ) =>
% 0.19/0.51       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.51  thf('10', plain,
% 0.19/0.51      (![X10 : $i, X11 : $i]:
% 0.19/0.51         (~ (v4_relat_1 @ X10 @ X11)
% 0.19/0.51          | (r1_tarski @ (k1_relat_1 @ X10) @ X11)
% 0.19/0.51          | ~ (v1_relat_1 @ X10))),
% 0.19/0.51      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.19/0.51  thf('11', plain,
% 0.19/0.51      ((~ (v1_relat_1 @ sk_B_1) | (r1_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.51  thf('12', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(cc1_relset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.51       ( v1_relat_1 @ C ) ))).
% 0.19/0.51  thf('13', plain,
% 0.19/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.51         ((v1_relat_1 @ X17)
% 0.19/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.19/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.51  thf('14', plain, ((v1_relat_1 @ sk_B_1)),
% 0.19/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.51  thf('15', plain, ((r1_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.19/0.51      inference('demod', [status(thm)], ['11', '14'])).
% 0.19/0.51  thf(t3_subset, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.51  thf('16', plain,
% 0.19/0.51      (![X4 : $i, X6 : $i]:
% 0.19/0.51         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.19/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.51  thf('17', plain,
% 0.19/0.51      ((m1_subset_1 @ (k1_relat_1 @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.51  thf(l3_subset_1, axiom,
% 0.19/0.51    (![A:$i,B:$i]:
% 0.19/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.19/0.51  thf('18', plain,
% 0.19/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.51          | (r2_hidden @ X0 @ X2)
% 0.19/0.51          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.19/0.51      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.19/0.51  thf('19', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.51  thf('20', plain,
% 0.19/0.51      ((~ (v1_relat_1 @ sk_B_1)
% 0.19/0.51        | ~ (v1_funct_1 @ sk_B_1)
% 0.19/0.51        | (v2_funct_1 @ sk_B_1)
% 0.19/0.51        | (r2_hidden @ (sk_C @ sk_B_1) @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['6', '19'])).
% 0.19/0.51  thf('21', plain, ((v1_relat_1 @ sk_B_1)),
% 0.19/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.51  thf('22', plain, ((v1_funct_1 @ sk_B_1)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('23', plain,
% 0.19/0.51      (((v2_funct_1 @ sk_B_1) | (r2_hidden @ (sk_C @ sk_B_1) @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.19/0.51  thf('24', plain,
% 0.19/0.51      (![X12 : $i]:
% 0.19/0.51         (((k1_funct_1 @ X12 @ (sk_B @ X12))
% 0.19/0.51            = (k1_funct_1 @ X12 @ (sk_C @ X12)))
% 0.19/0.51          | (v2_funct_1 @ X12)
% 0.19/0.51          | ~ (v1_funct_1 @ X12)
% 0.19/0.51          | ~ (v1_relat_1 @ X12))),
% 0.19/0.51      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.19/0.51  thf('25', plain,
% 0.19/0.51      ((![X27 : $i, X28 : $i]:
% 0.19/0.51          (((X28) = (X27))
% 0.19/0.51           | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.19/0.51           | ~ (r2_hidden @ X27 @ sk_A)
% 0.19/0.51           | ~ (r2_hidden @ X28 @ sk_A)))
% 0.19/0.51         <= ((![X27 : $i, X28 : $i]:
% 0.19/0.51                (((X28) = (X27))
% 0.19/0.51                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.19/0.51                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.19/0.51                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.19/0.51      inference('split', [status(esa)], ['4'])).
% 0.19/0.51  thf('26', plain,
% 0.19/0.51      ((![X0 : $i]:
% 0.19/0.51          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.19/0.51             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.19/0.51           | ~ (v1_relat_1 @ sk_B_1)
% 0.19/0.51           | ~ (v1_funct_1 @ sk_B_1)
% 0.19/0.51           | (v2_funct_1 @ sk_B_1)
% 0.19/0.51           | ~ (r2_hidden @ X0 @ sk_A)
% 0.19/0.51           | ~ (r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.19/0.51           | ((X0) = (sk_C @ sk_B_1))))
% 0.19/0.51         <= ((![X27 : $i, X28 : $i]:
% 0.19/0.51                (((X28) = (X27))
% 0.19/0.51                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.19/0.51                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.19/0.51                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.51  thf('27', plain, ((v1_relat_1 @ sk_B_1)),
% 0.19/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.51  thf('28', plain, ((v1_funct_1 @ sk_B_1)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('29', plain,
% 0.19/0.51      ((![X0 : $i]:
% 0.19/0.51          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.19/0.51             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.19/0.51           | (v2_funct_1 @ sk_B_1)
% 0.19/0.51           | ~ (r2_hidden @ X0 @ sk_A)
% 0.19/0.51           | ~ (r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.19/0.51           | ((X0) = (sk_C @ sk_B_1))))
% 0.19/0.51         <= ((![X27 : $i, X28 : $i]:
% 0.19/0.51                (((X28) = (X27))
% 0.19/0.51                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.19/0.51                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.19/0.51                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.19/0.51      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.19/0.51  thf('30', plain,
% 0.19/0.51      ((![X0 : $i]:
% 0.19/0.51          ((v2_funct_1 @ sk_B_1)
% 0.19/0.51           | ((X0) = (sk_C @ sk_B_1))
% 0.19/0.51           | ~ (r2_hidden @ X0 @ sk_A)
% 0.19/0.51           | (v2_funct_1 @ sk_B_1)
% 0.19/0.51           | ((k1_funct_1 @ sk_B_1 @ X0)
% 0.19/0.51               != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 0.19/0.51         <= ((![X27 : $i, X28 : $i]:
% 0.19/0.51                (((X28) = (X27))
% 0.19/0.51                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.19/0.51                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.19/0.51                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['23', '29'])).
% 0.19/0.51  thf('31', plain,
% 0.19/0.51      ((![X0 : $i]:
% 0.19/0.51          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.19/0.51             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.19/0.51           | ~ (r2_hidden @ X0 @ sk_A)
% 0.19/0.51           | ((X0) = (sk_C @ sk_B_1))
% 0.19/0.51           | (v2_funct_1 @ sk_B_1)))
% 0.19/0.51         <= ((![X27 : $i, X28 : $i]:
% 0.19/0.51                (((X28) = (X27))
% 0.19/0.51                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.19/0.51                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.19/0.51                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.19/0.51      inference('simplify', [status(thm)], ['30'])).
% 0.19/0.51  thf('32', plain,
% 0.19/0.51      ((((v2_funct_1 @ sk_B_1)
% 0.19/0.51         | ((sk_B @ sk_B_1) = (sk_C @ sk_B_1))
% 0.19/0.51         | ~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_A)))
% 0.19/0.51         <= ((![X27 : $i, X28 : $i]:
% 0.19/0.51                (((X28) = (X27))
% 0.19/0.51                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.19/0.51                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.19/0.51                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.19/0.51      inference('eq_res', [status(thm)], ['31'])).
% 0.19/0.51  thf('33', plain,
% 0.19/0.51      (![X12 : $i]:
% 0.19/0.51         ((r2_hidden @ (sk_B @ X12) @ (k1_relat_1 @ X12))
% 0.19/0.51          | (v2_funct_1 @ X12)
% 0.19/0.51          | ~ (v1_funct_1 @ X12)
% 0.19/0.51          | ~ (v1_relat_1 @ X12))),
% 0.19/0.51      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.19/0.51  thf('34', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.51  thf('35', plain,
% 0.19/0.51      ((~ (v1_relat_1 @ sk_B_1)
% 0.19/0.51        | ~ (v1_funct_1 @ sk_B_1)
% 0.19/0.51        | (v2_funct_1 @ sk_B_1)
% 0.19/0.51        | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.51  thf('36', plain, ((v1_relat_1 @ sk_B_1)),
% 0.19/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.51  thf('37', plain, ((v1_funct_1 @ sk_B_1)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('38', plain,
% 0.19/0.51      (((v2_funct_1 @ sk_B_1) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.19/0.51  thf('39', plain,
% 0.19/0.51      (((((sk_B @ sk_B_1) = (sk_C @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.19/0.51         <= ((![X27 : $i, X28 : $i]:
% 0.19/0.51                (((X28) = (X27))
% 0.19/0.51                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.19/0.51                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.19/0.51                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.19/0.51      inference('clc', [status(thm)], ['32', '38'])).
% 0.19/0.51  thf('40', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.19/0.51      inference('split', [status(esa)], ['0'])).
% 0.19/0.51  thf('41', plain,
% 0.19/0.51      ((((sk_B @ sk_B_1) = (sk_C @ sk_B_1)))
% 0.19/0.51         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.19/0.51             (![X27 : $i, X28 : $i]:
% 0.19/0.51                (((X28) = (X27))
% 0.19/0.51                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.19/0.51                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.19/0.51                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.19/0.51  thf('42', plain,
% 0.19/0.51      (![X12 : $i]:
% 0.19/0.51         (((sk_B @ X12) != (sk_C @ X12))
% 0.19/0.51          | (v2_funct_1 @ X12)
% 0.19/0.51          | ~ (v1_funct_1 @ X12)
% 0.19/0.51          | ~ (v1_relat_1 @ X12))),
% 0.19/0.51      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.19/0.51  thf('43', plain,
% 0.19/0.51      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1))
% 0.19/0.51         | ~ (v1_relat_1 @ sk_B_1)
% 0.19/0.51         | ~ (v1_funct_1 @ sk_B_1)
% 0.19/0.51         | (v2_funct_1 @ sk_B_1)))
% 0.19/0.51         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.19/0.51             (![X27 : $i, X28 : $i]:
% 0.19/0.51                (((X28) = (X27))
% 0.19/0.51                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.19/0.51                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.19/0.51                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.19/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.19/0.51  thf('44', plain, ((v1_relat_1 @ sk_B_1)),
% 0.19/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.51  thf('45', plain, ((v1_funct_1 @ sk_B_1)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('46', plain,
% 0.19/0.51      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.19/0.51         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.19/0.51             (![X27 : $i, X28 : $i]:
% 0.19/0.51                (((X28) = (X27))
% 0.19/0.51                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.19/0.51                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.19/0.51                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.19/0.51      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.19/0.51  thf('47', plain,
% 0.19/0.51      (((v2_funct_1 @ sk_B_1))
% 0.19/0.51         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.19/0.51             (![X27 : $i, X28 : $i]:
% 0.19/0.51                (((X28) = (X27))
% 0.19/0.51                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.19/0.51                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.19/0.51                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.19/0.51      inference('simplify', [status(thm)], ['46'])).
% 0.19/0.51  thf('48', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.19/0.51      inference('split', [status(esa)], ['0'])).
% 0.19/0.51  thf('49', plain,
% 0.19/0.51      (~
% 0.19/0.51       (![X27 : $i, X28 : $i]:
% 0.19/0.51          (((X28) = (X27))
% 0.19/0.51           | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.19/0.51           | ~ (r2_hidden @ X27 @ sk_A)
% 0.19/0.51           | ~ (r2_hidden @ X28 @ sk_A))) | 
% 0.19/0.51       ((v2_funct_1 @ sk_B_1))),
% 0.19/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.51  thf('50', plain, (((r2_hidden @ sk_C_1 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.19/0.51      inference('split', [status(esa)], ['0'])).
% 0.19/0.51  thf('51', plain, (((r2_hidden @ sk_C_1 @ sk_A))),
% 0.19/0.51      inference('sat_resolution*', [status(thm)], ['5', '49', '50'])).
% 0.19/0.51  thf('52', plain, (~ (r1_tarski @ sk_A @ sk_C_1)),
% 0.19/0.51      inference('simpl_trail', [status(thm)], ['3', '51'])).
% 0.19/0.51  thf('53', plain,
% 0.19/0.51      (((r2_hidden @ sk_C_1 @ sk_A)) <= (((r2_hidden @ sk_C_1 @ sk_A)))),
% 0.19/0.51      inference('split', [status(esa)], ['0'])).
% 0.19/0.51  thf('54', plain, (((r2_hidden @ sk_C_1 @ sk_A))),
% 0.19/0.51      inference('sat_resolution*', [status(thm)], ['5', '49', '50'])).
% 0.19/0.51  thf('55', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.19/0.51      inference('simpl_trail', [status(thm)], ['53', '54'])).
% 0.19/0.51  thf('56', plain,
% 0.19/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf(t32_funct_2, axiom,
% 0.19/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.19/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.51       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.19/0.51         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.19/0.51           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.19/0.51             ( C ) ) ) ) ))).
% 0.19/0.51  thf('57', plain,
% 0.19/0.51      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.19/0.51         (~ (r2_hidden @ X23 @ X24)
% 0.19/0.51          | ((X25) = (k1_xboole_0))
% 0.19/0.51          | ~ (v1_funct_1 @ X26)
% 0.19/0.51          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.19/0.51          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.19/0.51          | ((k1_funct_1 @ (k2_funct_1 @ X26) @ (k1_funct_1 @ X26 @ X23))
% 0.19/0.51              = (X23))
% 0.19/0.51          | ~ (v2_funct_1 @ X26))),
% 0.19/0.51      inference('cnf', [status(esa)], [t32_funct_2])).
% 0.19/0.51  thf('58', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (~ (v2_funct_1 @ sk_B_1)
% 0.19/0.51          | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.19/0.51              = (X0))
% 0.19/0.51          | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.19/0.51          | ~ (v1_funct_1 @ sk_B_1)
% 0.19/0.51          | ((sk_A) = (k1_xboole_0))
% 0.19/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.19/0.51      inference('sup-', [status(thm)], ['56', '57'])).
% 0.19/0.51  thf('59', plain, (((v2_funct_1 @ sk_B_1)) <= (((v2_funct_1 @ sk_B_1)))),
% 0.19/0.51      inference('split', [status(esa)], ['4'])).
% 0.19/0.51  thf('60', plain, (((v2_funct_1 @ sk_B_1))),
% 0.19/0.51      inference('sat_resolution*', [status(thm)], ['5', '49'])).
% 0.19/0.51  thf('61', plain, ((v2_funct_1 @ sk_B_1)),
% 0.19/0.51      inference('simpl_trail', [status(thm)], ['59', '60'])).
% 0.19/0.51  thf('62', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('63', plain, ((v1_funct_1 @ sk_B_1)),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('64', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.19/0.51            = (X0))
% 0.19/0.51          | ((sk_A) = (k1_xboole_0))
% 0.19/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['58', '61', '62', '63'])).
% 0.19/0.51  thf('65', plain,
% 0.19/0.51      ((((sk_A) = (k1_xboole_0))
% 0.19/0.51        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_1))
% 0.19/0.51            = (sk_C_1)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['55', '64'])).
% 0.19/0.51  thf('66', plain, (((r2_hidden @ sk_D @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('67', plain,
% 0.19/0.51      (((r2_hidden @ sk_D @ sk_A)) <= (((r2_hidden @ sk_D @ sk_A)))),
% 0.19/0.51      inference('split', [status(esa)], ['66'])).
% 0.19/0.51  thf('68', plain, (((r2_hidden @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.19/0.51      inference('split', [status(esa)], ['66'])).
% 0.19/0.51  thf('69', plain, (((r2_hidden @ sk_D @ sk_A))),
% 0.19/0.51      inference('sat_resolution*', [status(thm)], ['5', '49', '68'])).
% 0.19/0.51  thf('70', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.19/0.51      inference('simpl_trail', [status(thm)], ['67', '69'])).
% 0.19/0.51  thf('71', plain,
% 0.19/0.51      (![X0 : $i]:
% 0.19/0.51         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.19/0.51            = (X0))
% 0.19/0.51          | ((sk_A) = (k1_xboole_0))
% 0.19/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.19/0.51      inference('demod', [status(thm)], ['58', '61', '62', '63'])).
% 0.19/0.51  thf('72', plain,
% 0.19/0.51      ((((sk_A) = (k1_xboole_0))
% 0.19/0.51        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.19/0.51            = (sk_D)))),
% 0.19/0.51      inference('sup-', [status(thm)], ['70', '71'])).
% 0.19/0.51  thf('73', plain,
% 0.19/0.51      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.19/0.51        | ~ (v2_funct_1 @ sk_B_1))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('74', plain,
% 0.19/0.51      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D)))
% 0.19/0.51         <= ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))))),
% 0.19/0.51      inference('split', [status(esa)], ['73'])).
% 0.19/0.51  thf('75', plain,
% 0.19/0.51      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))) | 
% 0.19/0.51       ~ ((v2_funct_1 @ sk_B_1))),
% 0.19/0.51      inference('split', [status(esa)], ['73'])).
% 0.19/0.51  thf('76', plain,
% 0.19/0.51      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D)))),
% 0.19/0.51      inference('sat_resolution*', [status(thm)], ['5', '49', '75'])).
% 0.19/0.51  thf('77', plain,
% 0.19/0.51      (((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.19/0.51      inference('simpl_trail', [status(thm)], ['74', '76'])).
% 0.19/0.51  thf('78', plain,
% 0.19/0.51      ((((sk_A) = (k1_xboole_0))
% 0.19/0.51        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_1))
% 0.19/0.51            = (sk_D)))),
% 0.19/0.51      inference('demod', [status(thm)], ['72', '77'])).
% 0.19/0.51  thf('79', plain,
% 0.19/0.51      ((((sk_C_1) = (sk_D))
% 0.19/0.51        | ((sk_A) = (k1_xboole_0))
% 0.19/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.51      inference('sup+', [status(thm)], ['65', '78'])).
% 0.19/0.51  thf('80', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_1) = (sk_D)))),
% 0.19/0.51      inference('simplify', [status(thm)], ['79'])).
% 0.19/0.51  thf('81', plain, ((((sk_C_1) != (sk_D)) | ~ (v2_funct_1 @ sk_B_1))),
% 0.19/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.51  thf('82', plain, ((((sk_C_1) != (sk_D))) <= (~ (((sk_C_1) = (sk_D))))),
% 0.19/0.51      inference('split', [status(esa)], ['81'])).
% 0.19/0.51  thf('83', plain, (~ (((sk_C_1) = (sk_D))) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.19/0.51      inference('split', [status(esa)], ['81'])).
% 0.19/0.51  thf('84', plain, (~ (((sk_C_1) = (sk_D)))),
% 0.19/0.51      inference('sat_resolution*', [status(thm)], ['5', '49', '83'])).
% 0.19/0.51  thf('85', plain, (((sk_C_1) != (sk_D))),
% 0.19/0.51      inference('simpl_trail', [status(thm)], ['82', '84'])).
% 0.19/0.51  thf('86', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.51      inference('simplify_reflect-', [status(thm)], ['80', '85'])).
% 0.19/0.51  thf(t4_subset_1, axiom,
% 0.19/0.51    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.51  thf('87', plain,
% 0.19/0.51      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.19/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.19/0.51  thf('88', plain,
% 0.19/0.51      (![X4 : $i, X5 : $i]:
% 0.19/0.51         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.19/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.51  thf('89', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.51      inference('sup-', [status(thm)], ['87', '88'])).
% 0.19/0.51  thf('90', plain, ($false),
% 0.19/0.51      inference('demod', [status(thm)], ['52', '86', '89'])).
% 0.19/0.51  
% 0.19/0.51  % SZS output end Refutation
% 0.19/0.51  
% 0.19/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
