%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bTLLqH65UD

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  146 (5291 expanded)
%              Number of leaves         :   30 (1471 expanded)
%              Depth                    :   33
%              Number of atoms          : 1240 (88381 expanded)
%              Number of equality atoms :  112 (5913 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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
    ! [X27: $i,X28: $i] :
      ( ( X28 = X27 )
      | ( ( k1_funct_1 @ sk_B_1 @ X28 )
       != ( k1_funct_1 @ sk_B_1 @ X27 ) )
      | ~ ( r2_hidden @ X27 @ sk_A )
      | ~ ( r2_hidden @ X28 @ sk_A )
      | ( v2_funct_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
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
    ! [X11: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X11 ) @ ( k1_relat_1 @ X11 ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('5',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('19',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['16','19','20'])).

thf('22',plain,(
    ! [X11: $i] :
      ( ( ( k1_funct_1 @ X11 @ ( sk_B @ X11 ) )
        = ( k1_funct_1 @ X11 @ ( sk_C_1 @ X11 ) ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('23',plain,
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
    inference(split,[status(esa)],['2'])).

thf('24',plain,
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
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('26',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
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
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
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
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,
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
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
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
    inference(eq_res,[status(thm)],['29'])).

thf('31',plain,(
    ! [X11: $i] :
      ( ( r2_hidden @ ( sk_B @ X11 ) @ ( k1_relat_1 @ X11 ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('35',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( ( ( sk_B @ sk_B_1 )
        = ( sk_C_1 @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X27: $i,X28: $i] :
        ( ( X28 = X27 )
        | ( ( k1_funct_1 @ sk_B_1 @ X28 )
         != ( k1_funct_1 @ sk_B_1 @ X27 ) )
        | ~ ( r2_hidden @ X27 @ sk_A )
        | ~ ( r2_hidden @ X28 @ sk_A ) ) ),
    inference(clc,[status(thm)],['30','36'])).

thf('38',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( ( sk_B @ sk_B_1 )
      = ( sk_C_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X27: $i,X28: $i] :
          ( ( X28 = X27 )
          | ( ( k1_funct_1 @ sk_B_1 @ X28 )
           != ( k1_funct_1 @ sk_B_1 @ X27 ) )
          | ~ ( r2_hidden @ X27 @ sk_A )
          | ~ ( r2_hidden @ X28 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X11: $i] :
      ( ( ( sk_B @ X11 )
       != ( sk_C_1 @ X11 ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('42',plain,
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
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('44',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
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
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X27: $i,X28: $i] :
          ( ( X28 = X27 )
          | ( ( k1_funct_1 @ sk_B_1 @ X28 )
           != ( k1_funct_1 @ sk_B_1 @ X27 ) )
          | ~ ( r2_hidden @ X27 @ sk_A )
          | ~ ( r2_hidden @ X28 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['38'])).

thf('48',plain,
    ( ~ ! [X27: $i,X28: $i] :
          ( ( X28 = X27 )
          | ( ( k1_funct_1 @ sk_B_1 @ X28 )
           != ( k1_funct_1 @ sk_B_1 @ X27 ) )
          | ~ ( r2_hidden @ X27 @ sk_A )
          | ~ ( r2_hidden @ X28 @ sk_A ) )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['3','48','49'])).

thf('51',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['1','50'])).

thf('52',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('53',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('54',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
   <= ( r2_hidden @ sk_C_2 @ sk_A ) ),
    inference(split,[status(esa)],['38'])).

thf('56',plain,
    ( ( r2_hidden @ sk_C_2 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['38'])).

thf('57',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','48','56'])).

thf('58',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference(simpl_trail,[status(thm)],['55','57'])).

thf('59',plain,(
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

thf('60',plain,(
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

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('66',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['3','48'])).

thf('67',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_2 ) )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['58','68'])).

thf('70',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
   <= ( r2_hidden @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['70'])).

thf('72',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['70'])).

thf('73',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','48','72'])).

thf('74',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['71','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('76',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['1','50'])).

thf('78',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_1 ) @ ( k1_funct_1 @ sk_B_1 @ sk_C_2 ) )
      = sk_D ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_C_2 = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','78'])).

thf('80',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ( sk_C_2 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( sk_C_2 != sk_D )
   <= ( sk_C_2 != sk_D ) ),
    inference(split,[status(esa)],['81'])).

thf('83',plain,
    ( ( sk_C_2 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['81'])).

thf('84',plain,(
    sk_C_2 != sk_D ),
    inference('sat_resolution*',[status(thm)],['3','48','83'])).

thf('85',plain,(
    sk_C_2 != sk_D ),
    inference(simpl_trail,[status(thm)],['82','84'])).

thf('86',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['80','85'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('87',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('88',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['80','85'])).

thf('89',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['54','86','87','88'])).

thf('90',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X11 ) )
      | ( ( k1_funct_1 @ X11 @ X12 )
       != ( k1_funct_1 @ X11 @ X13 ) )
      | ( X12 = X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('93',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['54','86','87','88'])).

thf('95',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['65','66'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( sk_D = X0 )
      | ~ ( r2_hidden @ sk_D @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','96'])).

thf('98',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['71','73'])).

thf('99',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['80','85'])).

thf('100',plain,(
    r2_hidden @ sk_D @ k1_xboole_0 ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_D @ X0 ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_2 )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( sk_D = X0 ) ) ),
    inference(demod,[status(thm)],['97','104'])).

thf('106',plain,
    ( ( sk_D = sk_C_2 )
    | ~ ( r2_hidden @ sk_C_2 @ k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['105'])).

thf('107',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference(simpl_trail,[status(thm)],['55','57'])).

thf('108',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['80','85'])).

thf('109',plain,(
    r2_hidden @ sk_C_2 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('111',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_C_2 @ X0 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    sk_D = sk_C_2 ),
    inference(demod,[status(thm)],['106','111'])).

thf('113',plain,(
    sk_C_2 != sk_D ),
    inference(simpl_trail,[status(thm)],['82','84'])).

thf('114',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['112','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bTLLqH65UD
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:14:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 172 iterations in 0.065s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.53  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.53  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.22/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.53  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.22/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.53  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.22/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.53  thf(t77_funct_2, conjecture,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.53         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.53       ( ( v2_funct_1 @ B ) <=>
% 0.22/0.53         ( ![C:$i,D:$i]:
% 0.22/0.53           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.22/0.53               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.22/0.53             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i,B:$i]:
% 0.22/0.53        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.53            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.53          ( ( v2_funct_1 @ B ) <=>
% 0.22/0.53            ( ![C:$i,D:$i]:
% 0.22/0.53              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.22/0.53                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.22/0.53                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t77_funct_2])).
% 0.22/0.53  thf('0', plain,
% 0.22/0.53      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.22/0.53        | ~ (v2_funct_1 @ sk_B_1))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D)))
% 0.22/0.53         <= ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))))),
% 0.22/0.53      inference('split', [status(esa)], ['0'])).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      (![X27 : $i, X28 : $i]:
% 0.22/0.53         (((X28) = (X27))
% 0.22/0.53          | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.53          | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.53          | ~ (r2_hidden @ X28 @ sk_A)
% 0.22/0.53          | (v2_funct_1 @ sk_B_1))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('3', plain,
% 0.22/0.53      (((v2_funct_1 @ sk_B_1)) | 
% 0.22/0.53       (![X27 : $i, X28 : $i]:
% 0.22/0.53          (((X28) = (X27))
% 0.22/0.53           | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.53           | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.53           | ~ (r2_hidden @ X28 @ sk_A)))),
% 0.22/0.53      inference('split', [status(esa)], ['2'])).
% 0.22/0.53  thf(d8_funct_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.53       ( ( v2_funct_1 @ A ) <=>
% 0.22/0.53         ( ![B:$i,C:$i]:
% 0.22/0.53           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.22/0.53               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.22/0.53               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.22/0.53             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.22/0.53  thf('4', plain,
% 0.22/0.53      (![X11 : $i]:
% 0.22/0.53         ((r2_hidden @ (sk_C_1 @ X11) @ (k1_relat_1 @ X11))
% 0.22/0.53          | (v2_funct_1 @ X11)
% 0.22/0.53          | ~ (v1_funct_1 @ X11)
% 0.22/0.53          | ~ (v1_relat_1 @ X11))),
% 0.22/0.53      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(dt_k1_relset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.53       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.53  thf('6', plain,
% 0.22/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.53         ((m1_subset_1 @ (k1_relset_1 @ X17 @ X18 @ X19) @ (k1_zfmisc_1 @ X17))
% 0.22/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.22/0.53      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.22/0.53  thf('7', plain,
% 0.22/0.53      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B_1) @ 
% 0.22/0.53        (k1_zfmisc_1 @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.53  thf('8', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.53         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.22/0.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.22/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.53  thf('10', plain,
% 0.22/0.53      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.53  thf('11', plain,
% 0.22/0.53      ((m1_subset_1 @ (k1_relat_1 @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['7', '10'])).
% 0.22/0.53  thf(t3_subset, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.53  thf('12', plain,
% 0.22/0.53      (![X8 : $i, X9 : $i]:
% 0.22/0.53         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.53  thf('13', plain, ((r1_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.22/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.53  thf(d3_tarski, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.53  thf('14', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.53          | (r2_hidden @ X0 @ X2)
% 0.22/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.53  thf('15', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.53  thf('16', plain,
% 0.22/0.53      ((~ (v1_relat_1 @ sk_B_1)
% 0.22/0.53        | ~ (v1_funct_1 @ sk_B_1)
% 0.22/0.53        | (v2_funct_1 @ sk_B_1)
% 0.22/0.53        | (r2_hidden @ (sk_C_1 @ sk_B_1) @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['4', '15'])).
% 0.22/0.53  thf('17', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(cc1_relset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.53       ( v1_relat_1 @ C ) ))).
% 0.22/0.53  thf('18', plain,
% 0.22/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.53         ((v1_relat_1 @ X14)
% 0.22/0.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.22/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.53  thf('19', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.53  thf('20', plain, ((v1_funct_1 @ sk_B_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('21', plain,
% 0.22/0.53      (((v2_funct_1 @ sk_B_1) | (r2_hidden @ (sk_C_1 @ sk_B_1) @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['16', '19', '20'])).
% 0.22/0.53  thf('22', plain,
% 0.22/0.53      (![X11 : $i]:
% 0.22/0.53         (((k1_funct_1 @ X11 @ (sk_B @ X11))
% 0.22/0.53            = (k1_funct_1 @ X11 @ (sk_C_1 @ X11)))
% 0.22/0.53          | (v2_funct_1 @ X11)
% 0.22/0.53          | ~ (v1_funct_1 @ X11)
% 0.22/0.53          | ~ (v1_relat_1 @ X11))),
% 0.22/0.53      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.22/0.53  thf('23', plain,
% 0.22/0.53      ((![X27 : $i, X28 : $i]:
% 0.22/0.53          (((X28) = (X27))
% 0.22/0.53           | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.53           | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.53           | ~ (r2_hidden @ X28 @ sk_A)))
% 0.22/0.53         <= ((![X27 : $i, X28 : $i]:
% 0.22/0.53                (((X28) = (X27))
% 0.22/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.22/0.53      inference('split', [status(esa)], ['2'])).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      ((![X0 : $i]:
% 0.22/0.53          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.22/0.53             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.22/0.53           | ~ (v1_relat_1 @ sk_B_1)
% 0.22/0.53           | ~ (v1_funct_1 @ sk_B_1)
% 0.22/0.53           | (v2_funct_1 @ sk_B_1)
% 0.22/0.53           | ~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.53           | ~ (r2_hidden @ (sk_C_1 @ sk_B_1) @ sk_A)
% 0.22/0.53           | ((X0) = (sk_C_1 @ sk_B_1))))
% 0.22/0.53         <= ((![X27 : $i, X28 : $i]:
% 0.22/0.53                (((X28) = (X27))
% 0.22/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.53  thf('25', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.53  thf('26', plain, ((v1_funct_1 @ sk_B_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('27', plain,
% 0.22/0.53      ((![X0 : $i]:
% 0.22/0.53          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.22/0.53             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.22/0.53           | (v2_funct_1 @ sk_B_1)
% 0.22/0.53           | ~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.53           | ~ (r2_hidden @ (sk_C_1 @ sk_B_1) @ sk_A)
% 0.22/0.53           | ((X0) = (sk_C_1 @ sk_B_1))))
% 0.22/0.53         <= ((![X27 : $i, X28 : $i]:
% 0.22/0.53                (((X28) = (X27))
% 0.22/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.22/0.53      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.22/0.53  thf('28', plain,
% 0.22/0.53      ((![X0 : $i]:
% 0.22/0.53          ((v2_funct_1 @ sk_B_1)
% 0.22/0.53           | ((X0) = (sk_C_1 @ sk_B_1))
% 0.22/0.53           | ~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.53           | (v2_funct_1 @ sk_B_1)
% 0.22/0.53           | ((k1_funct_1 @ sk_B_1 @ X0)
% 0.22/0.53               != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 0.22/0.53         <= ((![X27 : $i, X28 : $i]:
% 0.22/0.53                (((X28) = (X27))
% 0.22/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['21', '27'])).
% 0.22/0.53  thf('29', plain,
% 0.22/0.53      ((![X0 : $i]:
% 0.22/0.53          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.22/0.53             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.22/0.53           | ~ (r2_hidden @ X0 @ sk_A)
% 0.22/0.53           | ((X0) = (sk_C_1 @ sk_B_1))
% 0.22/0.53           | (v2_funct_1 @ sk_B_1)))
% 0.22/0.53         <= ((![X27 : $i, X28 : $i]:
% 0.22/0.53                (((X28) = (X27))
% 0.22/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.22/0.53      inference('simplify', [status(thm)], ['28'])).
% 0.22/0.53  thf('30', plain,
% 0.22/0.53      ((((v2_funct_1 @ sk_B_1)
% 0.22/0.53         | ((sk_B @ sk_B_1) = (sk_C_1 @ sk_B_1))
% 0.22/0.53         | ~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_A)))
% 0.22/0.53         <= ((![X27 : $i, X28 : $i]:
% 0.22/0.53                (((X28) = (X27))
% 0.22/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.22/0.53      inference('eq_res', [status(thm)], ['29'])).
% 0.22/0.53  thf('31', plain,
% 0.22/0.53      (![X11 : $i]:
% 0.22/0.53         ((r2_hidden @ (sk_B @ X11) @ (k1_relat_1 @ X11))
% 0.22/0.53          | (v2_funct_1 @ X11)
% 0.22/0.53          | ~ (v1_funct_1 @ X11)
% 0.22/0.53          | ~ (v1_relat_1 @ X11))),
% 0.22/0.53      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.22/0.53  thf('32', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_1)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.53  thf('33', plain,
% 0.22/0.53      ((~ (v1_relat_1 @ sk_B_1)
% 0.22/0.53        | ~ (v1_funct_1 @ sk_B_1)
% 0.22/0.53        | (v2_funct_1 @ sk_B_1)
% 0.22/0.53        | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.53  thf('34', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.53  thf('35', plain, ((v1_funct_1 @ sk_B_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('36', plain,
% 0.22/0.53      (((v2_funct_1 @ sk_B_1) | (r2_hidden @ (sk_B @ sk_B_1) @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.22/0.53  thf('37', plain,
% 0.22/0.53      (((((sk_B @ sk_B_1) = (sk_C_1 @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.22/0.53         <= ((![X27 : $i, X28 : $i]:
% 0.22/0.53                (((X28) = (X27))
% 0.22/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.22/0.53      inference('clc', [status(thm)], ['30', '36'])).
% 0.22/0.53  thf('38', plain, (((r2_hidden @ sk_C_2 @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('39', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.22/0.53      inference('split', [status(esa)], ['38'])).
% 0.22/0.53  thf('40', plain,
% 0.22/0.53      ((((sk_B @ sk_B_1) = (sk_C_1 @ sk_B_1)))
% 0.22/0.53         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.22/0.53             (![X27 : $i, X28 : $i]:
% 0.22/0.53                (((X28) = (X27))
% 0.22/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['37', '39'])).
% 0.22/0.53  thf('41', plain,
% 0.22/0.53      (![X11 : $i]:
% 0.22/0.53         (((sk_B @ X11) != (sk_C_1 @ X11))
% 0.22/0.53          | (v2_funct_1 @ X11)
% 0.22/0.53          | ~ (v1_funct_1 @ X11)
% 0.22/0.53          | ~ (v1_relat_1 @ X11))),
% 0.22/0.53      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.22/0.53  thf('42', plain,
% 0.22/0.53      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1))
% 0.22/0.53         | ~ (v1_relat_1 @ sk_B_1)
% 0.22/0.53         | ~ (v1_funct_1 @ sk_B_1)
% 0.22/0.53         | (v2_funct_1 @ sk_B_1)))
% 0.22/0.53         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.22/0.53             (![X27 : $i, X28 : $i]:
% 0.22/0.53                (((X28) = (X27))
% 0.22/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.22/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.53  thf('43', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.53  thf('44', plain, ((v1_funct_1 @ sk_B_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('45', plain,
% 0.22/0.53      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.22/0.53         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.22/0.53             (![X27 : $i, X28 : $i]:
% 0.22/0.53                (((X28) = (X27))
% 0.22/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.22/0.53      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.22/0.53  thf('46', plain,
% 0.22/0.53      (((v2_funct_1 @ sk_B_1))
% 0.22/0.53         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.22/0.53             (![X27 : $i, X28 : $i]:
% 0.22/0.53                (((X28) = (X27))
% 0.22/0.53                 | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.53                 | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.53                 | ~ (r2_hidden @ X28 @ sk_A))))),
% 0.22/0.53      inference('simplify', [status(thm)], ['45'])).
% 0.22/0.53  thf('47', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.22/0.53      inference('split', [status(esa)], ['38'])).
% 0.22/0.53  thf('48', plain,
% 0.22/0.53      (~
% 0.22/0.53       (![X27 : $i, X28 : $i]:
% 0.22/0.53          (((X28) = (X27))
% 0.22/0.53           | ((k1_funct_1 @ sk_B_1 @ X28) != (k1_funct_1 @ sk_B_1 @ X27))
% 0.22/0.53           | ~ (r2_hidden @ X27 @ sk_A)
% 0.22/0.53           | ~ (r2_hidden @ X28 @ sk_A))) | 
% 0.22/0.53       ((v2_funct_1 @ sk_B_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.53  thf('49', plain,
% 0.22/0.53      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))) | 
% 0.22/0.53       ~ ((v2_funct_1 @ sk_B_1))),
% 0.22/0.53      inference('split', [status(esa)], ['0'])).
% 0.22/0.53  thf('50', plain,
% 0.22/0.53      ((((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D)))),
% 0.22/0.53      inference('sat_resolution*', [status(thm)], ['3', '48', '49'])).
% 0.22/0.53  thf('51', plain,
% 0.22/0.53      (((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['1', '50'])).
% 0.22/0.53  thf('52', plain, ((r1_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.22/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.53  thf(d10_xboole_0, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.53  thf('53', plain,
% 0.22/0.53      (![X4 : $i, X6 : $i]:
% 0.22/0.53         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.22/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.53  thf('54', plain,
% 0.22/0.53      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_B_1))
% 0.22/0.53        | ((sk_A) = (k1_relat_1 @ sk_B_1)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.53  thf('55', plain,
% 0.22/0.53      (((r2_hidden @ sk_C_2 @ sk_A)) <= (((r2_hidden @ sk_C_2 @ sk_A)))),
% 0.22/0.53      inference('split', [status(esa)], ['38'])).
% 0.22/0.53  thf('56', plain, (((r2_hidden @ sk_C_2 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.22/0.53      inference('split', [status(esa)], ['38'])).
% 0.22/0.53  thf('57', plain, (((r2_hidden @ sk_C_2 @ sk_A))),
% 0.22/0.53      inference('sat_resolution*', [status(thm)], ['3', '48', '56'])).
% 0.22/0.53  thf('58', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['55', '57'])).
% 0.22/0.53  thf('59', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(t32_funct_2, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.53       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.22/0.53         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.53           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.22/0.53             ( C ) ) ) ) ))).
% 0.22/0.53  thf('60', plain,
% 0.22/0.53      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X23 @ X24)
% 0.22/0.53          | ((X25) = (k1_xboole_0))
% 0.22/0.53          | ~ (v1_funct_1 @ X26)
% 0.22/0.53          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.22/0.53          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.22/0.53          | ((k1_funct_1 @ (k2_funct_1 @ X26) @ (k1_funct_1 @ X26 @ X23))
% 0.22/0.53              = (X23))
% 0.22/0.53          | ~ (v2_funct_1 @ X26))),
% 0.22/0.53      inference('cnf', [status(esa)], [t32_funct_2])).
% 0.22/0.53  thf('61', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (v2_funct_1 @ sk_B_1)
% 0.22/0.53          | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.22/0.53              = (X0))
% 0.22/0.53          | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.22/0.53          | ~ (v1_funct_1 @ sk_B_1)
% 0.22/0.53          | ((sk_A) = (k1_xboole_0))
% 0.22/0.53          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.53  thf('62', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('63', plain, ((v1_funct_1 @ sk_B_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('64', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (v2_funct_1 @ sk_B_1)
% 0.22/0.53          | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.22/0.53              = (X0))
% 0.22/0.53          | ((sk_A) = (k1_xboole_0))
% 0.22/0.53          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.22/0.53  thf('65', plain, (((v2_funct_1 @ sk_B_1)) <= (((v2_funct_1 @ sk_B_1)))),
% 0.22/0.53      inference('split', [status(esa)], ['2'])).
% 0.22/0.53  thf('66', plain, (((v2_funct_1 @ sk_B_1))),
% 0.22/0.53      inference('sat_resolution*', [status(thm)], ['3', '48'])).
% 0.22/0.53  thf('67', plain, ((v2_funct_1 @ sk_B_1)),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['65', '66'])).
% 0.22/0.53  thf('68', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.22/0.53            = (X0))
% 0.22/0.53          | ((sk_A) = (k1_xboole_0))
% 0.22/0.53          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['64', '67'])).
% 0.22/0.53  thf('69', plain,
% 0.22/0.53      ((((sk_A) = (k1_xboole_0))
% 0.22/0.53        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_2))
% 0.22/0.53            = (sk_C_2)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['58', '68'])).
% 0.22/0.53  thf('70', plain, (((r2_hidden @ sk_D @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('71', plain,
% 0.22/0.53      (((r2_hidden @ sk_D @ sk_A)) <= (((r2_hidden @ sk_D @ sk_A)))),
% 0.22/0.53      inference('split', [status(esa)], ['70'])).
% 0.22/0.53  thf('72', plain, (((r2_hidden @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.22/0.53      inference('split', [status(esa)], ['70'])).
% 0.22/0.53  thf('73', plain, (((r2_hidden @ sk_D @ sk_A))),
% 0.22/0.53      inference('sat_resolution*', [status(thm)], ['3', '48', '72'])).
% 0.22/0.53  thf('74', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['71', '73'])).
% 0.22/0.53  thf('75', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ X0))
% 0.22/0.53            = (X0))
% 0.22/0.53          | ((sk_A) = (k1_xboole_0))
% 0.22/0.53          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.22/0.53      inference('demod', [status(thm)], ['64', '67'])).
% 0.22/0.53  thf('76', plain,
% 0.22/0.53      ((((sk_A) = (k1_xboole_0))
% 0.22/0.53        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.22/0.53            = (sk_D)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['74', '75'])).
% 0.22/0.53  thf('77', plain,
% 0.22/0.53      (((k1_funct_1 @ sk_B_1 @ sk_C_2) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['1', '50'])).
% 0.22/0.53  thf('78', plain,
% 0.22/0.53      ((((sk_A) = (k1_xboole_0))
% 0.22/0.53        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_1) @ (k1_funct_1 @ sk_B_1 @ sk_C_2))
% 0.22/0.53            = (sk_D)))),
% 0.22/0.53      inference('demod', [status(thm)], ['76', '77'])).
% 0.22/0.53  thf('79', plain,
% 0.22/0.53      ((((sk_C_2) = (sk_D))
% 0.22/0.53        | ((sk_A) = (k1_xboole_0))
% 0.22/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.53      inference('sup+', [status(thm)], ['69', '78'])).
% 0.22/0.53  thf('80', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_2) = (sk_D)))),
% 0.22/0.53      inference('simplify', [status(thm)], ['79'])).
% 0.22/0.53  thf('81', plain, ((((sk_C_2) != (sk_D)) | ~ (v2_funct_1 @ sk_B_1))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('82', plain, ((((sk_C_2) != (sk_D))) <= (~ (((sk_C_2) = (sk_D))))),
% 0.22/0.53      inference('split', [status(esa)], ['81'])).
% 0.22/0.53  thf('83', plain, (~ (((sk_C_2) = (sk_D))) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.22/0.53      inference('split', [status(esa)], ['81'])).
% 0.22/0.53  thf('84', plain, (~ (((sk_C_2) = (sk_D)))),
% 0.22/0.53      inference('sat_resolution*', [status(thm)], ['3', '48', '83'])).
% 0.22/0.53  thf('85', plain, (((sk_C_2) != (sk_D))),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['82', '84'])).
% 0.22/0.53  thf('86', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['80', '85'])).
% 0.22/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.53  thf('87', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.22/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.53  thf('88', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['80', '85'])).
% 0.22/0.53  thf('89', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_B_1))),
% 0.22/0.53      inference('demod', [status(thm)], ['54', '86', '87', '88'])).
% 0.22/0.53  thf('90', plain,
% 0.22/0.53      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.53         (~ (v2_funct_1 @ X11)
% 0.22/0.53          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X11))
% 0.22/0.53          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X11))
% 0.22/0.53          | ((k1_funct_1 @ X11 @ X12) != (k1_funct_1 @ X11 @ X13))
% 0.22/0.53          | ((X12) = (X13))
% 0.22/0.53          | ~ (v1_funct_1 @ X11)
% 0.22/0.53          | ~ (v1_relat_1 @ X11))),
% 0.22/0.53      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.22/0.53  thf('91', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.22/0.53          | ~ (v1_relat_1 @ sk_B_1)
% 0.22/0.53          | ~ (v1_funct_1 @ sk_B_1)
% 0.22/0.53          | ((X0) = (X1))
% 0.22/0.53          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.22/0.53          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1))
% 0.22/0.53          | ~ (v2_funct_1 @ sk_B_1))),
% 0.22/0.53      inference('sup-', [status(thm)], ['89', '90'])).
% 0.22/0.53  thf('92', plain, ((v1_relat_1 @ sk_B_1)),
% 0.22/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.53  thf('93', plain, ((v1_funct_1 @ sk_B_1)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('94', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_B_1))),
% 0.22/0.53      inference('demod', [status(thm)], ['54', '86', '87', '88'])).
% 0.22/0.53  thf('95', plain, ((v2_funct_1 @ sk_B_1)),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['65', '66'])).
% 0.22/0.53  thf('96', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.22/0.53          | ((X0) = (X1))
% 0.22/0.53          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.22/0.53          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.22/0.53      inference('demod', [status(thm)], ['91', '92', '93', '94', '95'])).
% 0.22/0.53  thf('97', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (((k1_funct_1 @ sk_B_1 @ sk_C_2) != (k1_funct_1 @ sk_B_1 @ X0))
% 0.22/0.53          | ~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.22/0.53          | ((sk_D) = (X0))
% 0.22/0.53          | ~ (r2_hidden @ sk_D @ k1_xboole_0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['51', '96'])).
% 0.22/0.53  thf('98', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['71', '73'])).
% 0.22/0.53  thf('99', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['80', '85'])).
% 0.22/0.53  thf('100', plain, ((r2_hidden @ sk_D @ k1_xboole_0)),
% 0.22/0.53      inference('demod', [status(thm)], ['98', '99'])).
% 0.22/0.53  thf('101', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.22/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.53  thf('102', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.53          | (r2_hidden @ X0 @ X2)
% 0.22/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.53  thf('103', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['101', '102'])).
% 0.22/0.53  thf('104', plain, (![X0 : $i]: (r2_hidden @ sk_D @ X0)),
% 0.22/0.53      inference('sup-', [status(thm)], ['100', '103'])).
% 0.22/0.53  thf('105', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (((k1_funct_1 @ sk_B_1 @ sk_C_2) != (k1_funct_1 @ sk_B_1 @ X0))
% 0.22/0.53          | ~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.22/0.53          | ((sk_D) = (X0)))),
% 0.22/0.53      inference('demod', [status(thm)], ['97', '104'])).
% 0.22/0.53  thf('106', plain,
% 0.22/0.53      ((((sk_D) = (sk_C_2)) | ~ (r2_hidden @ sk_C_2 @ k1_xboole_0))),
% 0.22/0.53      inference('eq_res', [status(thm)], ['105'])).
% 0.22/0.53  thf('107', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['55', '57'])).
% 0.22/0.53  thf('108', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['80', '85'])).
% 0.22/0.53  thf('109', plain, ((r2_hidden @ sk_C_2 @ k1_xboole_0)),
% 0.22/0.53      inference('demod', [status(thm)], ['107', '108'])).
% 0.22/0.53  thf('110', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]:
% 0.22/0.53         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['101', '102'])).
% 0.22/0.53  thf('111', plain, (![X0 : $i]: (r2_hidden @ sk_C_2 @ X0)),
% 0.22/0.53      inference('sup-', [status(thm)], ['109', '110'])).
% 0.22/0.53  thf('112', plain, (((sk_D) = (sk_C_2))),
% 0.22/0.53      inference('demod', [status(thm)], ['106', '111'])).
% 0.22/0.53  thf('113', plain, (((sk_C_2) != (sk_D))),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['82', '84'])).
% 0.22/0.53  thf('114', plain, ($false),
% 0.22/0.53      inference('simplify_reflect-', [status(thm)], ['112', '113'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
