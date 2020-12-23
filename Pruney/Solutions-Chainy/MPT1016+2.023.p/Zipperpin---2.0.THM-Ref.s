%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9pnbPDkpGf

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  150 (5922 expanded)
%              Number of leaves         :   33 (1679 expanded)
%              Depth                    :   32
%              Number of atoms          : 1243 (92754 expanded)
%              Number of equality atoms :  107 (6028 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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

thf('2',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X31 = X30 )
      | ( ( k1_funct_1 @ sk_B_1 @ X31 )
       != ( k1_funct_1 @ sk_B_1 @ X30 ) )
      | ~ ( r2_hidden @ X30 @ sk_A )
      | ~ ( r2_hidden @ X31 @ sk_A )
      | ( v2_funct_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ! [X30: $i,X31: $i] :
        ( ( X31 = X30 )
        | ( ( k1_funct_1 @ sk_B_1 @ X31 )
         != ( k1_funct_1 @ sk_B_1 @ X30 ) )
        | ~ ( r2_hidden @ X30 @ sk_A )
        | ~ ( r2_hidden @ X31 @ sk_A ) ) ),
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
    ! [X15: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X20 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('7',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['7','10'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('21',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['16','21','22'])).

thf('24',plain,(
    ! [X15: $i] :
      ( ( ( k1_funct_1 @ X15 @ ( sk_B @ X15 ) )
        = ( k1_funct_1 @ X15 @ ( sk_C_1 @ X15 ) ) )
      | ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('25',plain,
    ( ! [X30: $i,X31: $i] :
        ( ( X31 = X30 )
        | ( ( k1_funct_1 @ sk_B_1 @ X31 )
         != ( k1_funct_1 @ sk_B_1 @ X30 ) )
        | ~ ( r2_hidden @ X30 @ sk_A )
        | ~ ( r2_hidden @ X31 @ sk_A ) )
   <= ! [X30: $i,X31: $i] :
        ( ( X31 = X30 )
        | ( ( k1_funct_1 @ sk_B_1 @ X31 )
         != ( k1_funct_1 @ sk_B_1 @ X30 ) )
        | ~ ( r2_hidden @ X30 @ sk_A )
        | ~ ( r2_hidden @ X31 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('26',plain,
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
   <= ! [X30: $i,X31: $i] :
        ( ( X31 = X30 )
        | ( ( k1_funct_1 @ sk_B_1 @ X31 )
         != ( k1_funct_1 @ sk_B_1 @ X30 ) )
        | ~ ( r2_hidden @ X30 @ sk_A )
        | ~ ( r2_hidden @ X31 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['19','20'])).

thf('28',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ( v2_funct_1 @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) @ sk_A )
        | ( X0
          = ( sk_C_1 @ sk_B_1 ) ) )
   <= ! [X30: $i,X31: $i] :
        ( ( X31 = X30 )
        | ( ( k1_funct_1 @ sk_B_1 @ X31 )
         != ( k1_funct_1 @ sk_B_1 @ X30 ) )
        | ~ ( r2_hidden @ X30 @ sk_A )
        | ~ ( r2_hidden @ X31 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( v2_funct_1 @ sk_B_1 )
        | ( X0
          = ( sk_C_1 @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( v2_funct_1 @ sk_B_1 )
        | ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
   <= ! [X30: $i,X31: $i] :
        ( ( X31 = X30 )
        | ( ( k1_funct_1 @ sk_B_1 @ X31 )
         != ( k1_funct_1 @ sk_B_1 @ X30 ) )
        | ~ ( r2_hidden @ X30 @ sk_A )
        | ~ ( r2_hidden @ X31 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( X0
          = ( sk_C_1 @ sk_B_1 ) )
        | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X30: $i,X31: $i] :
        ( ( X31 = X30 )
        | ( ( k1_funct_1 @ sk_B_1 @ X31 )
         != ( k1_funct_1 @ sk_B_1 @ X30 ) )
        | ~ ( r2_hidden @ X30 @ sk_A )
        | ~ ( r2_hidden @ X31 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( v2_funct_1 @ sk_B_1 )
      | ( ( sk_B @ sk_B_1 )
        = ( sk_C_1 @ sk_B_1 ) )
      | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) )
   <= ! [X30: $i,X31: $i] :
        ( ( X31 = X30 )
        | ( ( k1_funct_1 @ sk_B_1 @ X31 )
         != ( k1_funct_1 @ sk_B_1 @ X30 ) )
        | ~ ( r2_hidden @ X30 @ sk_A )
        | ~ ( r2_hidden @ X31 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['31'])).

thf('33',plain,(
    ! [X15: $i] :
      ( ( r2_hidden @ ( sk_B @ X15 ) @ ( k1_relat_1 @ X15 ) )
      | ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['19','20'])).

thf('37',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( ( ( sk_B @ sk_B_1 )
        = ( sk_C_1 @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X30: $i,X31: $i] :
        ( ( X31 = X30 )
        | ( ( k1_funct_1 @ sk_B_1 @ X31 )
         != ( k1_funct_1 @ sk_B_1 @ X30 ) )
        | ~ ( r2_hidden @ X30 @ sk_A )
        | ~ ( r2_hidden @ X31 @ sk_A ) ) ),
    inference(clc,[status(thm)],['32','38'])).

thf('40',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ( ( sk_B @ sk_B_1 )
      = ( sk_C_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X30: $i,X31: $i] :
          ( ( X31 = X30 )
          | ( ( k1_funct_1 @ sk_B_1 @ X31 )
           != ( k1_funct_1 @ sk_B_1 @ X30 ) )
          | ~ ( r2_hidden @ X30 @ sk_A )
          | ~ ( r2_hidden @ X31 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X15: $i] :
      ( ( ( sk_B @ X15 )
       != ( sk_C_1 @ X15 ) )
      | ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('43',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X30: $i,X31: $i] :
          ( ( X31 = X30 )
          | ( ( k1_funct_1 @ sk_B_1 @ X31 )
           != ( k1_funct_1 @ sk_B_1 @ X30 ) )
          | ~ ( r2_hidden @ X30 @ sk_A )
          | ~ ( r2_hidden @ X31 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['19','20'])).

thf('45',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X30: $i,X31: $i] :
          ( ( X31 = X30 )
          | ( ( k1_funct_1 @ sk_B_1 @ X31 )
           != ( k1_funct_1 @ sk_B_1 @ X30 ) )
          | ~ ( r2_hidden @ X30 @ sk_A )
          | ~ ( r2_hidden @ X31 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X30: $i,X31: $i] :
          ( ( X31 = X30 )
          | ( ( k1_funct_1 @ sk_B_1 @ X31 )
           != ( k1_funct_1 @ sk_B_1 @ X30 ) )
          | ~ ( r2_hidden @ X30 @ sk_A )
          | ~ ( r2_hidden @ X31 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ~ ! [X30: $i,X31: $i] :
          ( ( X31 = X30 )
          | ( ( k1_funct_1 @ sk_B_1 @ X31 )
           != ( k1_funct_1 @ sk_B_1 @ X30 ) )
          | ~ ( r2_hidden @ X30 @ sk_A )
          | ~ ( r2_hidden @ X31 @ sk_A ) )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','49','50'])).

thf('52',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference(simpl_trail,[status(thm)],['1','51'])).

thf('53',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference(simpl_trail,[status(thm)],['1','51'])).

thf('54',plain,(
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

thf('55',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ( X28 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ X29 ) @ ( k1_funct_1 @ X29 @ X26 ) )
        = X26 )
      | ~ ( v2_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t32_funct_2])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('58',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['3','49'])).

thf('59',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','59','60','61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_2 ) )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['53','62'])).

thf('64',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
   <= ( r2_hidden @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['64'])).

thf('67',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','49','66'])).

thf('68',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['65','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','59','60','61'])).

thf('70',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['71'])).

thf('73',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['71'])).

thf('74',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','49','73'])).

thf('75',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['72','74'])).

thf('76',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_2 ) )
      = sk_D ) ),
    inference(demod,[status(thm)],['70','75'])).

thf('77',plain,
    ( ( sk_C_2 = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','76'])).

thf('78',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( sk_C_2 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( sk_C_2 != sk_D )
   <= ( sk_C_2 != sk_D ) ),
    inference(split,[status(esa)],['79'])).

thf('81',plain,
    ( ( sk_C_2 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['79'])).

thf('82',plain,(
    sk_C_2 != sk_D ),
    inference('sat_resolution*',[status(thm)],['3','49','81'])).

thf('83',plain,(
    sk_C_2 != sk_D ),
    inference(simpl_trail,[status(thm)],['80','82'])).

thf('84',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['78','83'])).

thf('85',plain,(
    r2_hidden @ sk_C_2 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['52','84'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('86',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_C_2 @ X0 ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('91',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('92',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['78','83'])).

thf('94',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('95',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['78','83'])).

thf('96',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf(t56_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ) )).

thf('97',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X18 ) )
      | ( X19
        = ( k1_funct_1 @ ( k2_funct_1 @ X18 ) @ ( k1_funct_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t56_funct_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['19','20'])).

thf('100',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['57','58'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('103',plain,
    ( sk_C_2
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['89','102'])).

thf('104',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['65','67'])).

thf('105',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['78','83'])).

thf('106',plain,(
    r2_hidden @ sk_D @ k1_xboole_0 ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('108',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_D @ X0 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('110',plain,
    ( sk_D
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['72','74'])).

thf('112',plain,
    ( sk_D
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    sk_D = sk_C_2 ),
    inference('sup+',[status(thm)],['103','112'])).

thf('114',plain,(
    sk_C_2 != sk_D ),
    inference(simpl_trail,[status(thm)],['80','82'])).

thf('115',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['113','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9pnbPDkpGf
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:21:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 176 iterations in 0.061s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(t77_funct_2, conjecture,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.51       ( ( v2_funct_1 @ B ) <=>
% 0.20/0.51         ( ![C:$i,D:$i]:
% 0.20/0.51           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.20/0.51               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.20/0.51             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i]:
% 0.20/0.51        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.51            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.51          ( ( v2_funct_1 @ B ) <=>
% 0.20/0.51            ( ![C:$i,D:$i]:
% 0.20/0.51              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.20/0.51                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.20/0.51                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t77_funct_2])).
% 0.20/0.51  thf('0', plain, (((r2_hidden @ sk_C_2 @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (((r2_hidden @ sk_C_2 @ sk_A)) <= (((r2_hidden @ sk_C_2 @ sk_A)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X30 : $i, X31 : $i]:
% 0.20/0.51         (((X31) = (X30))
% 0.20/0.51          | ((k1_funct_1 @ sk_B_1 @ X31) != (k1_funct_1 @ sk_B_1 @ X30))
% 0.20/0.51          | ~ (r2_hidden @ X30 @ sk_A)
% 0.20/0.51          | ~ (r2_hidden @ X31 @ sk_A)
% 0.20/0.51          | (v2_funct_1 @ sk_B_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (((v2_funct_1 @ sk_B_1)) | 
% 0.20/0.51       (![X30 : $i, X31 : $i]:
% 0.20/0.51          (((X31) = (X30))
% 0.20/0.51           | ((k1_funct_1 @ sk_B_1 @ X31) != (k1_funct_1 @ sk_B_1 @ X30))
% 0.20/0.51           | ~ (r2_hidden @ X30 @ sk_A)
% 0.20/0.51           | ~ (r2_hidden @ X31 @ sk_A)))),
% 0.20/0.51      inference('split', [status(esa)], ['2'])).
% 0.20/0.51  thf(d8_funct_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.51       ( ( v2_funct_1 @ A ) <=>
% 0.20/0.51         ( ![B:$i,C:$i]:
% 0.20/0.51           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.51               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.51               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.20/0.51             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X15 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_C_1 @ X15) @ (k1_relat_1 @ X15))
% 0.20/0.51          | (v2_funct_1 @ X15)
% 0.20/0.51          | ~ (v1_funct_1 @ X15)
% 0.20/0.51          | ~ (v1_relat_1 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(dt_k1_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.51         ((m1_subset_1 @ (k1_relset_1 @ X20 @ X21 @ X22) @ (k1_zfmisc_1 @ X20))
% 0.20/0.51          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B_1) @ 
% 0.20/0.51        (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.51         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.20/0.51          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      ((m1_subset_1 @ (k1_relat_1 @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['7', '10'])).
% 0.20/0.51  thf(t3_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i]:
% 0.20/0.51         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.51  thf('13', plain, ((r1_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.51  thf(d3_tarski, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.51          | (r2_hidden @ X0 @ X2)
% 0.20/0.51          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ sk_B_1)
% 0.20/0.51        | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.51        | (v2_funct_1 @ sk_B_1)
% 0.20/0.51        | (r2_hidden @ (sk_C_1 @ sk_B_1) @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc2_relat_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.20/0.51          | (v1_relat_1 @ X11)
% 0.20/0.51          | ~ (v1_relat_1 @ X12))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf(fc6_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.51  thf('21', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('22', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (((v2_funct_1 @ sk_B_1) | (r2_hidden @ (sk_C_1 @ sk_B_1) @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['16', '21', '22'])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X15 : $i]:
% 0.20/0.51         (((k1_funct_1 @ X15 @ (sk_B @ X15))
% 0.20/0.51            = (k1_funct_1 @ X15 @ (sk_C_1 @ X15)))
% 0.20/0.51          | (v2_funct_1 @ X15)
% 0.20/0.51          | ~ (v1_funct_1 @ X15)
% 0.20/0.51          | ~ (v1_relat_1 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      ((![X30 : $i, X31 : $i]:
% 0.20/0.51          (((X31) = (X30))
% 0.20/0.51           | ((k1_funct_1 @ sk_B_1 @ X31) != (k1_funct_1 @ sk_B_1 @ X30))
% 0.20/0.51           | ~ (r2_hidden @ X30 @ sk_A)
% 0.20/0.51           | ~ (r2_hidden @ X31 @ sk_A)))
% 0.20/0.51         <= ((![X30 : $i, X31 : $i]:
% 0.20/0.51                (((X31) = (X30))
% 0.20/0.51                 | ((k1_funct_1 @ sk_B_1 @ X31) != (k1_funct_1 @ sk_B_1 @ X30))
% 0.20/0.51                 | ~ (r2_hidden @ X30 @ sk_A)
% 0.20/0.51                 | ~ (r2_hidden @ X31 @ sk_A))))),
% 0.20/0.51      inference('split', [status(esa)], ['2'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.20/0.51             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.20/0.51           | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.51           | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.51           | (v2_funct_1 @ sk_B_1)
% 0.20/0.51           | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.51           | ~ (r2_hidden @ (sk_C_1 @ sk_B_1) @ sk_A)
% 0.20/0.51           | ((X0) = (sk_C_1 @ sk_B_1))))
% 0.20/0.51         <= ((![X30 : $i, X31 : $i]:
% 0.20/0.51                (((X31) = (X30))
% 0.20/0.51                 | ((k1_funct_1 @ sk_B_1 @ X31) != (k1_funct_1 @ sk_B_1 @ X30))
% 0.20/0.51                 | ~ (r2_hidden @ X30 @ sk_A)
% 0.20/0.51                 | ~ (r2_hidden @ X31 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf('27', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('28', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.20/0.51             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.20/0.51           | (v2_funct_1 @ sk_B_1)
% 0.20/0.51           | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.51           | ~ (r2_hidden @ (sk_C_1 @ sk_B_1) @ sk_A)
% 0.20/0.51           | ((X0) = (sk_C_1 @ sk_B_1))))
% 0.20/0.51         <= ((![X30 : $i, X31 : $i]:
% 0.20/0.51                (((X31) = (X30))
% 0.20/0.51                 | ((k1_funct_1 @ sk_B_1 @ X31) != (k1_funct_1 @ sk_B_1 @ X30))
% 0.20/0.51                 | ~ (r2_hidden @ X30 @ sk_A)
% 0.20/0.51                 | ~ (r2_hidden @ X31 @ sk_A))))),
% 0.20/0.51      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          ((v2_funct_1 @ sk_B_1)
% 0.20/0.51           | ((X0) = (sk_C_1 @ sk_B_1))
% 0.20/0.51           | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.51           | (v2_funct_1 @ sk_B_1)
% 0.20/0.51           | ((k1_funct_1 @ sk_B_1 @ X0)
% 0.20/0.51               != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 0.20/0.51         <= ((![X30 : $i, X31 : $i]:
% 0.20/0.51                (((X31) = (X30))
% 0.20/0.51                 | ((k1_funct_1 @ sk_B_1 @ X31) != (k1_funct_1 @ sk_B_1 @ X30))
% 0.20/0.51                 | ~ (r2_hidden @ X30 @ sk_A)
% 0.20/0.51                 | ~ (r2_hidden @ X31 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['23', '29'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.20/0.51             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.20/0.51           | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.51           | ((X0) = (sk_C_1 @ sk_B_1))
% 0.20/0.51           | (v2_funct_1 @ sk_B_1)))
% 0.20/0.51         <= ((![X30 : $i, X31 : $i]:
% 0.20/0.51                (((X31) = (X30))
% 0.20/0.51                 | ((k1_funct_1 @ sk_B_1 @ X31) != (k1_funct_1 @ sk_B_1 @ X30))
% 0.20/0.51                 | ~ (r2_hidden @ X30 @ sk_A)
% 0.20/0.51                 | ~ (r2_hidden @ X31 @ sk_A))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      ((((v2_funct_1 @ sk_B_1)
% 0.20/0.51         | ((sk_B @ sk_B_1) = (sk_C_1 @ sk_B_1))
% 0.20/0.51         | ~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_A)))
% 0.20/0.51         <= ((![X30 : $i, X31 : $i]:
% 0.20/0.51                (((X31) = (X30))
% 0.20/0.51                 | ((k1_funct_1 @ sk_B_1 @ X31) != (k1_funct_1 @ sk_B_1 @ X30))
% 0.20/0.51                 | ~ (r2_hidden @ X30 @ sk_A)
% 0.20/0.51                 | ~ (r2_hidden @ X31 @ sk_A))))),
% 0.20/0.51      inference('eq_res', [status(thm)], ['31'])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X15 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_B @ X15) @ (k1_relat_1 @ X15))
% 0.20/0.51          | (v2_funct_1 @ X15)
% 0.20/0.51          | ~ (v1_funct_1 @ X15)
% 0.20/0.51          | ~ (v1_relat_1 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ sk_B_1)
% 0.20/0.51        | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.51        | (v2_funct_1 @ sk_B_1)
% 0.20/0.51        | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.51  thf('36', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('37', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (((v2_funct_1 @ sk_B_1) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      (((((sk_B @ sk_B_1) = (sk_C_1 @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.20/0.51         <= ((![X30 : $i, X31 : $i]:
% 0.20/0.51                (((X31) = (X30))
% 0.20/0.51                 | ((k1_funct_1 @ sk_B_1 @ X31) != (k1_funct_1 @ sk_B_1 @ X30))
% 0.20/0.51                 | ~ (r2_hidden @ X30 @ sk_A)
% 0.20/0.51                 | ~ (r2_hidden @ X31 @ sk_A))))),
% 0.20/0.51      inference('clc', [status(thm)], ['32', '38'])).
% 0.20/0.51  thf('40', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      ((((sk_B @ sk_B_1) = (sk_C_1 @ sk_B_1)))
% 0.20/0.51         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.20/0.51             (![X30 : $i, X31 : $i]:
% 0.20/0.51                (((X31) = (X30))
% 0.20/0.51                 | ((k1_funct_1 @ sk_B_1 @ X31) != (k1_funct_1 @ sk_B_1 @ X30))
% 0.20/0.51                 | ~ (r2_hidden @ X30 @ sk_A)
% 0.20/0.51                 | ~ (r2_hidden @ X31 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (![X15 : $i]:
% 0.20/0.51         (((sk_B @ X15) != (sk_C_1 @ X15))
% 0.20/0.51          | (v2_funct_1 @ X15)
% 0.20/0.51          | ~ (v1_funct_1 @ X15)
% 0.20/0.51          | ~ (v1_relat_1 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1))
% 0.20/0.51         | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.51         | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.51         | (v2_funct_1 @ sk_B_1)))
% 0.20/0.51         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.20/0.51             (![X30 : $i, X31 : $i]:
% 0.20/0.51                (((X31) = (X30))
% 0.20/0.51                 | ((k1_funct_1 @ sk_B_1 @ X31) != (k1_funct_1 @ sk_B_1 @ X30))
% 0.20/0.51                 | ~ (r2_hidden @ X30 @ sk_A)
% 0.20/0.51                 | ~ (r2_hidden @ X31 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.51  thf('44', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('45', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.20/0.51         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.20/0.51             (![X30 : $i, X31 : $i]:
% 0.20/0.51                (((X31) = (X30))
% 0.20/0.51                 | ((k1_funct_1 @ sk_B_1 @ X31) != (k1_funct_1 @ sk_B_1 @ X30))
% 0.20/0.51                 | ~ (r2_hidden @ X30 @ sk_A)
% 0.20/0.51                 | ~ (r2_hidden @ X31 @ sk_A))))),
% 0.20/0.51      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (((v2_funct_1 @ sk_B_1))
% 0.20/0.51         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.20/0.51             (![X30 : $i, X31 : $i]:
% 0.20/0.51                (((X31) = (X30))
% 0.20/0.51                 | ((k1_funct_1 @ sk_B_1 @ X31) != (k1_funct_1 @ sk_B_1 @ X30))
% 0.20/0.51                 | ~ (r2_hidden @ X30 @ sk_A)
% 0.20/0.51                 | ~ (r2_hidden @ X31 @ sk_A))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['46'])).
% 0.20/0.51  thf('48', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (~
% 0.20/0.51       (![X30 : $i, X31 : $i]:
% 0.20/0.51          (((X31) = (X30))
% 0.20/0.51           | ((k1_funct_1 @ sk_B_1 @ X31) != (k1_funct_1 @ sk_B_1 @ X30))
% 0.20/0.51           | ~ (r2_hidden @ X30 @ sk_A)
% 0.20/0.51           | ~ (r2_hidden @ X31 @ sk_A))) | 
% 0.20/0.51       ((v2_funct_1 @ sk_B_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.51  thf('50', plain, (((r2_hidden @ sk_C_2 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('51', plain, (((r2_hidden @ sk_C_2 @ sk_A))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['3', '49', '50'])).
% 0.20/0.51  thf('52', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['1', '51'])).
% 0.20/0.51  thf('53', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['1', '51'])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t32_funct_2, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.51       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.20/0.51         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.51           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.20/0.51             ( C ) ) ) ) ))).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X26 @ X27)
% 0.20/0.51          | ((X28) = (k1_xboole_0))
% 0.20/0.51          | ~ (v1_funct_1 @ X29)
% 0.20/0.51          | ~ (v1_funct_2 @ X29 @ X27 @ X28)
% 0.20/0.51          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.20/0.51          | ((k1_funct_1 @ (k2_funct_1 @ X29) @ (k1_funct_1 @ X29 @ X26))
% 0.20/0.51              = (X26))
% 0.20/0.51          | ~ (v2_funct_1 @ X29))),
% 0.20/0.51      inference('cnf', [status(esa)], [t32_funct_2])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v2_funct_1 @ sk_B_1)
% 0.20/0.51          | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.20/0.51              = (X0))
% 0.20/0.51          | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.51          | ((sk_A) = (k1_xboole_0))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.51  thf('57', plain, (((v2_funct_1 @ sk_B_1)) <= (((v2_funct_1 @ sk_B_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['2'])).
% 0.20/0.51  thf('58', plain, (((v2_funct_1 @ sk_B_1))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['3', '49'])).
% 0.20/0.51  thf('59', plain, ((v2_funct_1 @ sk_B_1)),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['57', '58'])).
% 0.20/0.51  thf('60', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('61', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('62', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.20/0.51            = (X0))
% 0.20/0.51          | ((sk_A) = (k1_xboole_0))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['56', '59', '60', '61'])).
% 0.20/0.51  thf('63', plain,
% 0.20/0.51      ((((sk_A) = (k1_xboole_0))
% 0.20/0.51        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_2))
% 0.20/0.51            = (sk_C_2)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['53', '62'])).
% 0.20/0.51  thf('64', plain, (((r2_hidden @ sk_D @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('65', plain,
% 0.20/0.51      (((r2_hidden @ sk_D @ sk_A)) <= (((r2_hidden @ sk_D @ sk_A)))),
% 0.20/0.51      inference('split', [status(esa)], ['64'])).
% 0.20/0.51  thf('66', plain, (((r2_hidden @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.20/0.51      inference('split', [status(esa)], ['64'])).
% 0.20/0.51  thf('67', plain, (((r2_hidden @ sk_D @ sk_A))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['3', '49', '66'])).
% 0.20/0.51  thf('68', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['65', '67'])).
% 0.20/0.51  thf('69', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.20/0.51            = (X0))
% 0.20/0.51          | ((sk_A) = (k1_xboole_0))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.51      inference('demod', [status(thm)], ['56', '59', '60', '61'])).
% 0.20/0.51  thf('70', plain,
% 0.20/0.51      ((((sk_A) = (k1_xboole_0))
% 0.20/0.51        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.20/0.51            = (sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.51  thf('71', plain,
% 0.20/0.51      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.20/0.51        | ~ (v2_funct_1 @ sk_B_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('72', plain,
% 0.20/0.51      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D)))
% 0.20/0.51         <= ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))))),
% 0.20/0.51      inference('split', [status(esa)], ['71'])).
% 0.20/0.51  thf('73', plain,
% 0.20/0.51      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))) | 
% 0.20/0.51       ~ ((v2_funct_1 @ sk_B_1))),
% 0.20/0.51      inference('split', [status(esa)], ['71'])).
% 0.20/0.51  thf('74', plain,
% 0.20/0.51      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['3', '49', '73'])).
% 0.20/0.51  thf('75', plain,
% 0.20/0.51      (((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['72', '74'])).
% 0.20/0.51  thf('76', plain,
% 0.20/0.51      ((((sk_A) = (k1_xboole_0))
% 0.20/0.51        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_2))
% 0.20/0.51            = (sk_D)))),
% 0.20/0.51      inference('demod', [status(thm)], ['70', '75'])).
% 0.20/0.51  thf('77', plain,
% 0.20/0.51      ((((sk_C_2) = (sk_D))
% 0.20/0.51        | ((sk_A) = (k1_xboole_0))
% 0.20/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['63', '76'])).
% 0.20/0.51  thf('78', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_2) = (sk_D)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['77'])).
% 0.20/0.51  thf('79', plain, ((((sk_C_2) != (sk_D)) | ~ (v2_funct_1 @ sk_B_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('80', plain, ((((sk_C_2) != (sk_D))) <= (~ (((sk_C_2) = (sk_D))))),
% 0.20/0.51      inference('split', [status(esa)], ['79'])).
% 0.20/0.51  thf('81', plain, (~ (((sk_C_2) = (sk_D))) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.20/0.51      inference('split', [status(esa)], ['79'])).
% 0.20/0.51  thf('82', plain, (~ (((sk_C_2) = (sk_D)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['3', '49', '81'])).
% 0.20/0.51  thf('83', plain, (((sk_C_2) != (sk_D))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['80', '82'])).
% 0.20/0.51  thf('84', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['78', '83'])).
% 0.20/0.51  thf('85', plain, ((r2_hidden @ sk_C_2 @ k1_xboole_0)),
% 0.20/0.51      inference('demod', [status(thm)], ['52', '84'])).
% 0.20/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.51  thf('86', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.51  thf('87', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.51          | (r2_hidden @ X0 @ X2)
% 0.20/0.51          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.51  thf('88', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['86', '87'])).
% 0.20/0.51  thf('89', plain, (![X0 : $i]: (r2_hidden @ sk_C_2 @ X0)),
% 0.20/0.51      inference('sup-', [status(thm)], ['85', '88'])).
% 0.20/0.51  thf('90', plain, ((r1_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.51  thf(d10_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.51  thf('91', plain,
% 0.20/0.51      (![X4 : $i, X6 : $i]:
% 0.20/0.51         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.51  thf('92', plain,
% 0.20/0.51      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_B_1))
% 0.20/0.51        | ((sk_A) = (k1_relat_1 @ sk_B_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['90', '91'])).
% 0.20/0.51  thf('93', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['78', '83'])).
% 0.20/0.51  thf('94', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.51  thf('95', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['78', '83'])).
% 0.20/0.51  thf('96', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_B_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 0.20/0.51  thf(t56_funct_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.51       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) ) =>
% 0.20/0.51         ( ( ( A ) =
% 0.20/0.51             ( k1_funct_1 @ ( k2_funct_1 @ B ) @ ( k1_funct_1 @ B @ A ) ) ) & 
% 0.20/0.51           ( ( A ) =
% 0.20/0.51             ( k1_funct_1 @ ( k5_relat_1 @ B @ ( k2_funct_1 @ B ) ) @ A ) ) ) ) ))).
% 0.20/0.51  thf('97', plain,
% 0.20/0.51      (![X18 : $i, X19 : $i]:
% 0.20/0.51         (~ (v2_funct_1 @ X18)
% 0.20/0.51          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X18))
% 0.20/0.51          | ((X19)
% 0.20/0.51              = (k1_funct_1 @ (k2_funct_1 @ X18) @ (k1_funct_1 @ X18 @ X19)))
% 0.20/0.51          | ~ (v1_funct_1 @ X18)
% 0.20/0.51          | ~ (v1_relat_1 @ X18))),
% 0.20/0.51      inference('cnf', [status(esa)], [t56_funct_1])).
% 0.20/0.51  thf('98', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.20/0.51          | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.51          | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.51          | ((X0)
% 0.20/0.51              = (k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.20/0.51                 (k1_funct_1 @ sk_B_1 @ X0)))
% 0.20/0.51          | ~ (v2_funct_1 @ sk_B_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['96', '97'])).
% 0.20/0.51  thf('99', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('100', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('101', plain, ((v2_funct_1 @ sk_B_1)),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['57', '58'])).
% 0.20/0.51  thf('102', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.20/0.51          | ((X0)
% 0.20/0.51              = (k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.20/0.51                 (k1_funct_1 @ sk_B_1 @ X0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 0.20/0.51  thf('103', plain,
% 0.20/0.51      (((sk_C_2)
% 0.20/0.51         = (k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_2)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['89', '102'])).
% 0.20/0.51  thf('104', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['65', '67'])).
% 0.20/0.51  thf('105', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['78', '83'])).
% 0.20/0.51  thf('106', plain, ((r2_hidden @ sk_D @ k1_xboole_0)),
% 0.20/0.51      inference('demod', [status(thm)], ['104', '105'])).
% 0.20/0.51  thf('107', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['86', '87'])).
% 0.20/0.51  thf('108', plain, (![X0 : $i]: (r2_hidden @ sk_D @ X0)),
% 0.20/0.51      inference('sup-', [status(thm)], ['106', '107'])).
% 0.20/0.51  thf('109', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.20/0.51          | ((X0)
% 0.20/0.51              = (k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ 
% 0.20/0.51                 (k1_funct_1 @ sk_B_1 @ X0))))),
% 0.20/0.51      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 0.20/0.51  thf('110', plain,
% 0.20/0.51      (((sk_D)
% 0.20/0.51         = (k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_D)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['108', '109'])).
% 0.20/0.51  thf('111', plain,
% 0.20/0.51      (((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['72', '74'])).
% 0.20/0.51  thf('112', plain,
% 0.20/0.51      (((sk_D)
% 0.20/0.51         = (k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_2)))),
% 0.20/0.51      inference('demod', [status(thm)], ['110', '111'])).
% 0.20/0.51  thf('113', plain, (((sk_D) = (sk_C_2))),
% 0.20/0.51      inference('sup+', [status(thm)], ['103', '112'])).
% 0.20/0.51  thf('114', plain, (((sk_C_2) != (sk_D))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['80', '82'])).
% 0.20/0.51  thf('115', plain, ($false),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['113', '114'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
