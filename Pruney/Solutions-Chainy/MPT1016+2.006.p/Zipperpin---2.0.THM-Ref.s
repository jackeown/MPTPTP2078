%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sdiOVCXAFx

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  133 (2186 expanded)
%              Number of leaves         :   29 ( 618 expanded)
%              Depth                    :   32
%              Number of atoms          : 1130 (35609 expanded)
%              Number of equality atoms :   99 (2314 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X21 = X20 )
      | ( ( k1_funct_1 @ sk_B_1 @ X21 )
       != ( k1_funct_1 @ sk_B_1 @ X20 ) )
      | ~ ( r2_hidden @ X20 @ sk_A )
      | ~ ( r2_hidden @ X21 @ sk_A )
      | ( v2_funct_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ! [X20: $i,X21: $i] :
        ( ( X21 = X20 )
        | ( ( k1_funct_1 @ sk_B_1 @ X21 )
         != ( k1_funct_1 @ sk_B_1 @ X20 ) )
        | ~ ( r2_hidden @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ sk_A ) ) ),
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
    ! [X7: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X7 ) @ ( k1_relat_1 @ X7 ) )
      | ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['9','12'])).

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
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('18',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X7: $i] :
      ( ( ( k1_funct_1 @ X7 @ ( sk_B @ X7 ) )
        = ( k1_funct_1 @ X7 @ ( sk_C_1 @ X7 ) ) )
      | ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('21',plain,
    ( ! [X20: $i,X21: $i] :
        ( ( X21 = X20 )
        | ( ( k1_funct_1 @ sk_B_1 @ X21 )
         != ( k1_funct_1 @ sk_B_1 @ X20 ) )
        | ~ ( r2_hidden @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ sk_A ) )
   <= ! [X20: $i,X21: $i] :
        ( ( X21 = X20 )
        | ( ( k1_funct_1 @ sk_B_1 @ X21 )
         != ( k1_funct_1 @ sk_B_1 @ X20 ) )
        | ~ ( r2_hidden @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('22',plain,
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
   <= ! [X20: $i,X21: $i] :
        ( ( X21 = X20 )
        | ( ( k1_funct_1 @ sk_B_1 @ X21 )
         != ( k1_funct_1 @ sk_B_1 @ X20 ) )
        | ~ ( r2_hidden @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('24',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ( v2_funct_1 @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) @ sk_A )
        | ( X0
          = ( sk_C_1 @ sk_B_1 ) ) )
   <= ! [X20: $i,X21: $i] :
        ( ( X21 = X20 )
        | ( ( k1_funct_1 @ sk_B_1 @ X21 )
         != ( k1_funct_1 @ sk_B_1 @ X20 ) )
        | ~ ( r2_hidden @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( v2_funct_1 @ sk_B_1 )
        | ( X0
          = ( sk_C_1 @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( v2_funct_1 @ sk_B_1 )
        | ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
   <= ! [X20: $i,X21: $i] :
        ( ( X21 = X20 )
        | ( ( k1_funct_1 @ sk_B_1 @ X21 )
         != ( k1_funct_1 @ sk_B_1 @ X20 ) )
        | ~ ( r2_hidden @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( X0
          = ( sk_C_1 @ sk_B_1 ) )
        | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X20: $i,X21: $i] :
        ( ( X21 = X20 )
        | ( ( k1_funct_1 @ sk_B_1 @ X21 )
         != ( k1_funct_1 @ sk_B_1 @ X20 ) )
        | ~ ( r2_hidden @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( ( v2_funct_1 @ sk_B_1 )
      | ( ( sk_B @ sk_B_1 )
        = ( sk_C_1 @ sk_B_1 ) )
      | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) )
   <= ! [X20: $i,X21: $i] :
        ( ( X21 = X20 )
        | ( ( k1_funct_1 @ sk_B_1 @ X21 )
         != ( k1_funct_1 @ sk_B_1 @ X20 ) )
        | ~ ( r2_hidden @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['27'])).

thf('29',plain,(
    ! [X7: $i] :
      ( ( r2_hidden @ ( sk_B @ X7 ) @ ( k1_relat_1 @ X7 ) )
      | ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('33',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( ( ( sk_B @ sk_B_1 )
        = ( sk_C_1 @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X20: $i,X21: $i] :
        ( ( X21 = X20 )
        | ( ( k1_funct_1 @ sk_B_1 @ X21 )
         != ( k1_funct_1 @ sk_B_1 @ X20 ) )
        | ~ ( r2_hidden @ X20 @ sk_A )
        | ~ ( r2_hidden @ X21 @ sk_A ) ) ),
    inference(clc,[status(thm)],['28','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,
    ( ( ( sk_B @ sk_B_1 )
      = ( sk_C_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X20: $i,X21: $i] :
          ( ( X21 = X20 )
          | ( ( k1_funct_1 @ sk_B_1 @ X21 )
           != ( k1_funct_1 @ sk_B_1 @ X20 ) )
          | ~ ( r2_hidden @ X20 @ sk_A )
          | ~ ( r2_hidden @ X21 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X7: $i] :
      ( ( ( sk_B @ X7 )
       != ( sk_C_1 @ X7 ) )
      | ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('40',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X20: $i,X21: $i] :
          ( ( X21 = X20 )
          | ( ( k1_funct_1 @ sk_B_1 @ X21 )
           != ( k1_funct_1 @ sk_B_1 @ X20 ) )
          | ~ ( r2_hidden @ X20 @ sk_A )
          | ~ ( r2_hidden @ X21 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('42',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X20: $i,X21: $i] :
          ( ( X21 = X20 )
          | ( ( k1_funct_1 @ sk_B_1 @ X21 )
           != ( k1_funct_1 @ sk_B_1 @ X20 ) )
          | ~ ( r2_hidden @ X20 @ sk_A )
          | ~ ( r2_hidden @ X21 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X20: $i,X21: $i] :
          ( ( X21 = X20 )
          | ( ( k1_funct_1 @ sk_B_1 @ X21 )
           != ( k1_funct_1 @ sk_B_1 @ X20 ) )
          | ~ ( r2_hidden @ X20 @ sk_A )
          | ~ ( r2_hidden @ X21 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['36'])).

thf('46',plain,
    ( ~ ! [X20: $i,X21: $i] :
          ( ( X21 = X20 )
          | ( ( k1_funct_1 @ sk_B_1 @ X21 )
           != ( k1_funct_1 @ sk_B_1 @ X20 ) )
          | ~ ( r2_hidden @ X20 @ sk_A )
          | ~ ( r2_hidden @ X21 @ sk_A ) )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','46','47'])).

thf('49',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['1','48'])).

thf('50',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
   <= ( r2_hidden @ sk_C_2 @ sk_A ) ),
    inference(split,[status(esa)],['36'])).

thf('51',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['36'])).

thf('52',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','46','51'])).

thf('53',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference(simpl_trail,[status(thm)],['50','52'])).

thf('54',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference(simpl_trail,[status(thm)],['50','52'])).

thf('55',plain,(
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

thf('56',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ( X18 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ X19 ) @ ( k1_funct_1 @ X19 @ X16 ) )
        = X16 )
      | ~ ( v2_funct_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t32_funct_2])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X21 = X20 )
      | ( ( k1_funct_1 @ sk_B_1 @ X21 )
       != ( k1_funct_1 @ sk_B_1 @ X20 ) )
      | ~ ( r2_hidden @ X20 @ sk_A )
      | ~ ( r2_hidden @ X21 @ sk_A )
      | ( v2_funct_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['3','46'])).

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
    inference(demod,[status(thm)],['57','61','62','63'])).

thf('65',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_2 ) )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['54','64'])).

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
    inference('sat_resolution*',[status(thm)],['3','46','68'])).

thf('70',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['67','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','61','62','63'])).

thf('72',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['1','48'])).

thf('74',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_2 ) )
      = sk_D ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_C_2 = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','74'])).

thf('76',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( sk_C_2 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( sk_C_2 != sk_D )
   <= ( sk_C_2 != sk_D ) ),
    inference(split,[status(esa)],['77'])).

thf('79',plain,
    ( ( sk_C_2 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['77'])).

thf('80',plain,(
    sk_C_2 != sk_D ),
    inference('sat_resolution*',[status(thm)],['3','46','79'])).

thf('81',plain,(
    sk_C_2 != sk_D ),
    inference(simpl_trail,[status(thm)],['78','80'])).

thf('82',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['76','81'])).

thf('83',plain,(
    r2_hidden @ sk_C_2 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['53','82'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('84',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_C_2 @ X0 ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X7 ) )
      | ( ( k1_funct_1 @ X7 @ X8 )
       != ( k1_funct_1 @ X7 @ X9 ) )
      | ( X8 = X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_C_2 = X1 )
      | ( ( k1_funct_1 @ X0 @ sk_C_2 )
       != ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
     != ( k1_funct_1 @ sk_B_1 @ sk_C_2 ) )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ~ ( r2_hidden @ sk_D @ ( k1_relat_1 @ sk_B_1 ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','89'])).

thf('91',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['59','60'])).

thf('92',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['67','69'])).

thf('93',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['76','81'])).

thf('94',plain,(
    r2_hidden @ sk_D @ k1_xboole_0 ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('96',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_D @ X0 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('99',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
     != ( k1_funct_1 @ sk_B_1 @ sk_C_2 ) )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['90','91','96','97','98'])).

thf('100',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    sk_C_2 != sk_D ),
    inference(simpl_trail,[status(thm)],['78','80'])).

thf('102',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['100','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sdiOVCXAFx
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:19:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 93 iterations in 0.042s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.50  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.50  thf(t77_funct_2, conjecture,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.50       ( ( v2_funct_1 @ B ) <=>
% 0.21/0.50         ( ![C:$i,D:$i]:
% 0.21/0.50           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.21/0.50               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.21/0.50             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i]:
% 0.21/0.50        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.50            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.50          ( ( v2_funct_1 @ B ) <=>
% 0.21/0.50            ( ![C:$i,D:$i]:
% 0.21/0.50              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.21/0.50                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.21/0.50                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t77_funct_2])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.21/0.50        | ~ (v2_funct_1 @ sk_B_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D)))
% 0.21/0.50         <= ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X20 : $i, X21 : $i]:
% 0.21/0.50         (((X21) = (X20))
% 0.21/0.50          | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.21/0.50          | ~ (r2_hidden @ X20 @ sk_A)
% 0.21/0.50          | ~ (r2_hidden @ X21 @ sk_A)
% 0.21/0.50          | (v2_funct_1 @ sk_B_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (((v2_funct_1 @ sk_B_1)) | 
% 0.21/0.50       (![X20 : $i, X21 : $i]:
% 0.21/0.50          (((X21) = (X20))
% 0.21/0.50           | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.21/0.50           | ~ (r2_hidden @ X20 @ sk_A)
% 0.21/0.50           | ~ (r2_hidden @ X21 @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf(d8_funct_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.50       ( ( v2_funct_1 @ A ) <=>
% 0.21/0.50         ( ![B:$i,C:$i]:
% 0.21/0.50           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.50               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.50               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.21/0.50             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X7 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_C_1 @ X7) @ (k1_relat_1 @ X7))
% 0.21/0.50          | (v2_funct_1 @ X7)
% 0.21/0.50          | ~ (v1_funct_1 @ X7)
% 0.21/0.50          | ~ (v1_relat_1 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc2_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.50         ((v4_relat_1 @ X13 @ X14)
% 0.21/0.50          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.50  thf('7', plain, ((v4_relat_1 @ sk_B_1 @ sk_A)),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.50  thf(d18_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i]:
% 0.21/0.50         (~ (v4_relat_1 @ X5 @ X6)
% 0.21/0.50          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.21/0.50          | ~ (v1_relat_1 @ X5))),
% 0.21/0.50      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_B_1) | (r1_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(cc1_relset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.50       ( v1_relat_1 @ C ) ))).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.50         ((v1_relat_1 @ X10)
% 0.21/0.50          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.21/0.50      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.50  thf('12', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain, ((r1_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['9', '12'])).
% 0.21/0.50  thf(d3_tarski, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.50          | (r2_hidden @ X0 @ X2)
% 0.21/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_B_1)
% 0.21/0.50        | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.50        | (v2_funct_1 @ sk_B_1)
% 0.21/0.50        | (r2_hidden @ (sk_C_1 @ sk_B_1) @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '15'])).
% 0.21/0.50  thf('17', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('18', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (((v2_funct_1 @ sk_B_1) | (r2_hidden @ (sk_C_1 @ sk_B_1) @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X7 : $i]:
% 0.21/0.50         (((k1_funct_1 @ X7 @ (sk_B @ X7)) = (k1_funct_1 @ X7 @ (sk_C_1 @ X7)))
% 0.21/0.50          | (v2_funct_1 @ X7)
% 0.21/0.50          | ~ (v1_funct_1 @ X7)
% 0.21/0.50          | ~ (v1_relat_1 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      ((![X20 : $i, X21 : $i]:
% 0.21/0.50          (((X21) = (X20))
% 0.21/0.50           | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.21/0.50           | ~ (r2_hidden @ X20 @ sk_A)
% 0.21/0.50           | ~ (r2_hidden @ X21 @ sk_A)))
% 0.21/0.50         <= ((![X20 : $i, X21 : $i]:
% 0.21/0.50                (((X21) = (X20))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.21/0.50                 | ~ (r2_hidden @ X20 @ sk_A)
% 0.21/0.50                 | ~ (r2_hidden @ X21 @ sk_A))))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.21/0.50             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.21/0.50           | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.50           | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.50           | (v2_funct_1 @ sk_B_1)
% 0.21/0.50           | ~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.50           | ~ (r2_hidden @ (sk_C_1 @ sk_B_1) @ sk_A)
% 0.21/0.50           | ((X0) = (sk_C_1 @ sk_B_1))))
% 0.21/0.50         <= ((![X20 : $i, X21 : $i]:
% 0.21/0.50                (((X21) = (X20))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.21/0.50                 | ~ (r2_hidden @ X20 @ sk_A)
% 0.21/0.50                 | ~ (r2_hidden @ X21 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.50  thf('23', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('24', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.21/0.50             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.21/0.50           | (v2_funct_1 @ sk_B_1)
% 0.21/0.50           | ~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.50           | ~ (r2_hidden @ (sk_C_1 @ sk_B_1) @ sk_A)
% 0.21/0.50           | ((X0) = (sk_C_1 @ sk_B_1))))
% 0.21/0.50         <= ((![X20 : $i, X21 : $i]:
% 0.21/0.50                (((X21) = (X20))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.21/0.50                 | ~ (r2_hidden @ X20 @ sk_A)
% 0.21/0.50                 | ~ (r2_hidden @ X21 @ sk_A))))),
% 0.21/0.50      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          ((v2_funct_1 @ sk_B_1)
% 0.21/0.50           | ((X0) = (sk_C_1 @ sk_B_1))
% 0.21/0.50           | ~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.50           | (v2_funct_1 @ sk_B_1)
% 0.21/0.50           | ((k1_funct_1 @ sk_B_1 @ X0)
% 0.21/0.50               != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 0.21/0.50         <= ((![X20 : $i, X21 : $i]:
% 0.21/0.50                (((X21) = (X20))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.21/0.50                 | ~ (r2_hidden @ X20 @ sk_A)
% 0.21/0.50                 | ~ (r2_hidden @ X21 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['19', '25'])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.21/0.50             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.21/0.50           | ~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.50           | ((X0) = (sk_C_1 @ sk_B_1))
% 0.21/0.50           | (v2_funct_1 @ sk_B_1)))
% 0.21/0.50         <= ((![X20 : $i, X21 : $i]:
% 0.21/0.50                (((X21) = (X20))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.21/0.50                 | ~ (r2_hidden @ X20 @ sk_A)
% 0.21/0.50                 | ~ (r2_hidden @ X21 @ sk_A))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      ((((v2_funct_1 @ sk_B_1)
% 0.21/0.50         | ((sk_B @ sk_B_1) = (sk_C_1 @ sk_B_1))
% 0.21/0.50         | ~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_A)))
% 0.21/0.50         <= ((![X20 : $i, X21 : $i]:
% 0.21/0.50                (((X21) = (X20))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.21/0.50                 | ~ (r2_hidden @ X20 @ sk_A)
% 0.21/0.50                 | ~ (r2_hidden @ X21 @ sk_A))))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['27'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X7 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_B @ X7) @ (k1_relat_1 @ X7))
% 0.21/0.50          | (v2_funct_1 @ X7)
% 0.21/0.50          | ~ (v1_funct_1 @ X7)
% 0.21/0.50          | ~ (v1_relat_1 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      ((~ (v1_relat_1 @ sk_B_1)
% 0.21/0.50        | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.50        | (v2_funct_1 @ sk_B_1)
% 0.21/0.50        | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('32', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('33', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (((v2_funct_1 @ sk_B_1) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (((((sk_B @ sk_B_1) = (sk_C_1 @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.21/0.50         <= ((![X20 : $i, X21 : $i]:
% 0.21/0.50                (((X21) = (X20))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.21/0.50                 | ~ (r2_hidden @ X20 @ sk_A)
% 0.21/0.50                 | ~ (r2_hidden @ X21 @ sk_A))))),
% 0.21/0.50      inference('clc', [status(thm)], ['28', '34'])).
% 0.21/0.50  thf('36', plain, (((r2_hidden @ sk_C_2 @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('37', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.21/0.50      inference('split', [status(esa)], ['36'])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      ((((sk_B @ sk_B_1) = (sk_C_1 @ sk_B_1)))
% 0.21/0.50         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.21/0.50             (![X20 : $i, X21 : $i]:
% 0.21/0.50                (((X21) = (X20))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.21/0.50                 | ~ (r2_hidden @ X20 @ sk_A)
% 0.21/0.50                 | ~ (r2_hidden @ X21 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['35', '37'])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (![X7 : $i]:
% 0.21/0.50         (((sk_B @ X7) != (sk_C_1 @ X7))
% 0.21/0.50          | (v2_funct_1 @ X7)
% 0.21/0.50          | ~ (v1_funct_1 @ X7)
% 0.21/0.50          | ~ (v1_relat_1 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1))
% 0.21/0.50         | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.50         | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.50         | (v2_funct_1 @ sk_B_1)))
% 0.21/0.50         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.21/0.50             (![X20 : $i, X21 : $i]:
% 0.21/0.50                (((X21) = (X20))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.21/0.50                 | ~ (r2_hidden @ X20 @ sk_A)
% 0.21/0.50                 | ~ (r2_hidden @ X21 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.50  thf('41', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('42', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.21/0.50         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.21/0.50             (![X20 : $i, X21 : $i]:
% 0.21/0.50                (((X21) = (X20))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.21/0.50                 | ~ (r2_hidden @ X20 @ sk_A)
% 0.21/0.50                 | ~ (r2_hidden @ X21 @ sk_A))))),
% 0.21/0.50      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      (((v2_funct_1 @ sk_B_1))
% 0.21/0.50         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.21/0.50             (![X20 : $i, X21 : $i]:
% 0.21/0.50                (((X21) = (X20))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.21/0.50                 | ~ (r2_hidden @ X20 @ sk_A)
% 0.21/0.50                 | ~ (r2_hidden @ X21 @ sk_A))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.50  thf('45', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.21/0.50      inference('split', [status(esa)], ['36'])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (~
% 0.21/0.50       (![X20 : $i, X21 : $i]:
% 0.21/0.50          (((X21) = (X20))
% 0.21/0.50           | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.21/0.50           | ~ (r2_hidden @ X20 @ sk_A)
% 0.21/0.50           | ~ (r2_hidden @ X21 @ sk_A))) | 
% 0.21/0.50       ((v2_funct_1 @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))) | 
% 0.21/0.50       ~ ((v2_funct_1 @ sk_B_1))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D)))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['3', '46', '47'])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['1', '48'])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      (((r2_hidden @ sk_C_2 @ sk_A)) <= (((r2_hidden @ sk_C_2 @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['36'])).
% 0.21/0.50  thf('51', plain, (((r2_hidden @ sk_C_2 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.21/0.50      inference('split', [status(esa)], ['36'])).
% 0.21/0.50  thf('52', plain, (((r2_hidden @ sk_C_2 @ sk_A))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['3', '46', '51'])).
% 0.21/0.50  thf('53', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['50', '52'])).
% 0.21/0.50  thf('54', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['50', '52'])).
% 0.21/0.50  thf('55', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t32_funct_2, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.50         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.50       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.21/0.50         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.21/0.50             ( C ) ) ) ) ))).
% 0.21/0.50  thf('56', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X16 @ X17)
% 0.21/0.50          | ((X18) = (k1_xboole_0))
% 0.21/0.50          | ~ (v1_funct_1 @ X19)
% 0.21/0.50          | ~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.21/0.50          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.21/0.50          | ((k1_funct_1 @ (k2_funct_1 @ X19) @ (k1_funct_1 @ X19 @ X16))
% 0.21/0.50              = (X16))
% 0.21/0.50          | ~ (v2_funct_1 @ X19))),
% 0.21/0.50      inference('cnf', [status(esa)], [t32_funct_2])).
% 0.21/0.50  thf('57', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v2_funct_1 @ sk_B_1)
% 0.21/0.50          | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.21/0.50              = (X0))
% 0.21/0.50          | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.21/0.50          | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.50          | ((sk_A) = (k1_xboole_0))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.50  thf('58', plain,
% 0.21/0.50      (![X20 : $i, X21 : $i]:
% 0.21/0.50         (((X21) = (X20))
% 0.21/0.50          | ((k1_funct_1 @ sk_B_1 @ X21) != (k1_funct_1 @ sk_B_1 @ X20))
% 0.21/0.50          | ~ (r2_hidden @ X20 @ sk_A)
% 0.21/0.50          | ~ (r2_hidden @ X21 @ sk_A)
% 0.21/0.50          | (v2_funct_1 @ sk_B_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('59', plain, (((v2_funct_1 @ sk_B_1)) <= (((v2_funct_1 @ sk_B_1)))),
% 0.21/0.50      inference('split', [status(esa)], ['58'])).
% 0.21/0.50  thf('60', plain, (((v2_funct_1 @ sk_B_1))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['3', '46'])).
% 0.21/0.50  thf('61', plain, ((v2_funct_1 @ sk_B_1)),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['59', '60'])).
% 0.21/0.50  thf('62', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('63', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('64', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.21/0.50            = (X0))
% 0.21/0.50          | ((sk_A) = (k1_xboole_0))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['57', '61', '62', '63'])).
% 0.21/0.50  thf('65', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0))
% 0.21/0.50        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_2))
% 0.21/0.50            = (sk_C_2)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['54', '64'])).
% 0.21/0.50  thf('66', plain, (((r2_hidden @ sk_D @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('67', plain,
% 0.21/0.50      (((r2_hidden @ sk_D @ sk_A)) <= (((r2_hidden @ sk_D @ sk_A)))),
% 0.21/0.50      inference('split', [status(esa)], ['66'])).
% 0.21/0.50  thf('68', plain, (((r2_hidden @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.21/0.50      inference('split', [status(esa)], ['66'])).
% 0.21/0.50  thf('69', plain, (((r2_hidden @ sk_D @ sk_A))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['3', '46', '68'])).
% 0.21/0.50  thf('70', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['67', '69'])).
% 0.21/0.50  thf('71', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.21/0.50            = (X0))
% 0.21/0.50          | ((sk_A) = (k1_xboole_0))
% 0.21/0.50          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['57', '61', '62', '63'])).
% 0.21/0.50  thf('72', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0))
% 0.21/0.50        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.21/0.50            = (sk_D)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.50  thf('73', plain,
% 0.21/0.50      (((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['1', '48'])).
% 0.21/0.50  thf('74', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0))
% 0.21/0.50        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_2))
% 0.21/0.50            = (sk_D)))),
% 0.21/0.50      inference('demod', [status(thm)], ['72', '73'])).
% 0.21/0.50  thf('75', plain,
% 0.21/0.50      ((((sk_C_2) = (sk_D))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['65', '74'])).
% 0.21/0.50  thf('76', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_2) = (sk_D)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['75'])).
% 0.21/0.50  thf('77', plain, ((((sk_C_2) != (sk_D)) | ~ (v2_funct_1 @ sk_B_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('78', plain, ((((sk_C_2) != (sk_D))) <= (~ (((sk_C_2) = (sk_D))))),
% 0.21/0.50      inference('split', [status(esa)], ['77'])).
% 0.21/0.50  thf('79', plain, (~ (((sk_C_2) = (sk_D))) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.21/0.50      inference('split', [status(esa)], ['77'])).
% 0.21/0.50  thf('80', plain, (~ (((sk_C_2) = (sk_D)))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['3', '46', '79'])).
% 0.21/0.50  thf('81', plain, (((sk_C_2) != (sk_D))),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['78', '80'])).
% 0.21/0.50  thf('82', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['76', '81'])).
% 0.21/0.50  thf('83', plain, ((r2_hidden @ sk_C_2 @ k1_xboole_0)),
% 0.21/0.50      inference('demod', [status(thm)], ['53', '82'])).
% 0.21/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.50  thf('84', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.21/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.50  thf('85', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.50          | (r2_hidden @ X0 @ X2)
% 0.21/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.50  thf('86', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.50  thf('87', plain, (![X0 : $i]: (r2_hidden @ sk_C_2 @ X0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['83', '86'])).
% 0.21/0.50  thf('88', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.50         (~ (v2_funct_1 @ X7)
% 0.21/0.50          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X7))
% 0.21/0.50          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X7))
% 0.21/0.50          | ((k1_funct_1 @ X7 @ X8) != (k1_funct_1 @ X7 @ X9))
% 0.21/0.50          | ((X8) = (X9))
% 0.21/0.50          | ~ (v1_funct_1 @ X7)
% 0.21/0.50          | ~ (v1_relat_1 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.50  thf('89', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ((sk_C_2) = (X1))
% 0.21/0.50          | ((k1_funct_1 @ X0 @ sk_C_2) != (k1_funct_1 @ X0 @ X1))
% 0.21/0.50          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.21/0.50          | ~ (v2_funct_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['87', '88'])).
% 0.21/0.50  thf('90', plain,
% 0.21/0.50      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) != (k1_funct_1 @ sk_B_1 @ sk_C_2))
% 0.21/0.50        | ~ (v2_funct_1 @ sk_B_1)
% 0.21/0.50        | ~ (r2_hidden @ sk_D @ (k1_relat_1 @ sk_B_1))
% 0.21/0.50        | ((sk_C_2) = (sk_D))
% 0.21/0.50        | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.50        | ~ (v1_relat_1 @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['49', '89'])).
% 0.21/0.50  thf('91', plain, ((v2_funct_1 @ sk_B_1)),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['59', '60'])).
% 0.21/0.50  thf('92', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['67', '69'])).
% 0.21/0.50  thf('93', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['76', '81'])).
% 0.21/0.50  thf('94', plain, ((r2_hidden @ sk_D @ k1_xboole_0)),
% 0.21/0.50      inference('demod', [status(thm)], ['92', '93'])).
% 0.21/0.50  thf('95', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.50  thf('96', plain, (![X0 : $i]: (r2_hidden @ sk_D @ X0)),
% 0.21/0.50      inference('sup-', [status(thm)], ['94', '95'])).
% 0.21/0.50  thf('97', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('98', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('99', plain,
% 0.21/0.50      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) != (k1_funct_1 @ sk_B_1 @ sk_C_2))
% 0.21/0.50        | ((sk_C_2) = (sk_D)))),
% 0.21/0.50      inference('demod', [status(thm)], ['90', '91', '96', '97', '98'])).
% 0.21/0.50  thf('100', plain, (((sk_C_2) = (sk_D))),
% 0.21/0.50      inference('simplify', [status(thm)], ['99'])).
% 0.21/0.50  thf('101', plain, (((sk_C_2) != (sk_D))),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['78', '80'])).
% 0.21/0.50  thf('102', plain, ($false),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['100', '101'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
