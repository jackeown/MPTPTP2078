%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fLaakCP8Cn

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 962 expanded)
%              Number of leaves         :   32 ( 282 expanded)
%              Depth                    :   28
%              Number of atoms          : 1065 (15125 expanded)
%              Number of equality atoms :   90 ( 972 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
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
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25 = X24 )
      | ( ( k1_funct_1 @ sk_B_2 @ X25 )
       != ( k1_funct_1 @ sk_B_2 @ X24 ) )
      | ~ ( r2_hidden @ X24 @ sk_A )
      | ~ ( r2_hidden @ X25 @ sk_A )
      | ( v2_funct_1 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_funct_1 @ sk_B_2 )
    | ! [X24: $i,X25: $i] :
        ( ( X25 = X24 )
        | ( ( k1_funct_1 @ sk_B_2 @ X25 )
         != ( k1_funct_1 @ sk_B_2 @ X24 ) )
        | ~ ( r2_hidden @ X24 @ sk_A )
        | ~ ( r2_hidden @ X25 @ sk_A ) ) ),
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
    ! [X11: $i] :
      ( ( r2_hidden @ ( sk_B_1 @ X11 ) @ ( k1_relat_1 @ X11 ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B_2 ) @ sk_A ),
    inference(demod,[status(thm)],['11','14'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_B_2 )
    | ( v2_funct_1 @ sk_B_2 )
    | ( r2_hidden @ ( sk_B_1 @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('22',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v2_funct_1 @ sk_B_2 )
    | ( r2_hidden @ ( sk_B_1 @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X11: $i] :
      ( ( r2_hidden @ ( sk_C @ X11 ) @ ( k1_relat_1 @ X11 ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_B_2 )
    | ( v2_funct_1 @ sk_B_2 )
    | ( r2_hidden @ ( sk_C @ sk_B_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('28',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v2_funct_1 @ sk_B_2 )
    | ( r2_hidden @ ( sk_C @ sk_B_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X11: $i] :
      ( ( ( k1_funct_1 @ X11 @ ( sk_B_1 @ X11 ) )
        = ( k1_funct_1 @ X11 @ ( sk_C @ X11 ) ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('31',plain,
    ( ! [X24: $i,X25: $i] :
        ( ( X25 = X24 )
        | ( ( k1_funct_1 @ sk_B_2 @ X25 )
         != ( k1_funct_1 @ sk_B_2 @ X24 ) )
        | ~ ( r2_hidden @ X24 @ sk_A )
        | ~ ( r2_hidden @ X25 @ sk_A ) )
   <= ! [X24: $i,X25: $i] :
        ( ( X25 = X24 )
        | ( ( k1_funct_1 @ sk_B_2 @ X25 )
         != ( k1_funct_1 @ sk_B_2 @ X24 ) )
        | ~ ( r2_hidden @ X24 @ sk_A )
        | ~ ( r2_hidden @ X25 @ sk_A ) ) ),
    inference(split,[status(esa)],['4'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) )
         != ( k1_funct_1 @ sk_B_2 @ X0 ) )
        | ~ ( v1_relat_1 @ sk_B_2 )
        | ~ ( v1_funct_1 @ sk_B_2 )
        | ( v2_funct_1 @ sk_B_2 )
        | ~ ( r2_hidden @ ( sk_C @ sk_B_2 ) @ sk_A )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( ( sk_C @ sk_B_2 )
          = X0 ) )
   <= ! [X24: $i,X25: $i] :
        ( ( X25 = X24 )
        | ( ( k1_funct_1 @ sk_B_2 @ X25 )
         != ( k1_funct_1 @ sk_B_2 @ X24 ) )
        | ~ ( r2_hidden @ X24 @ sk_A )
        | ~ ( r2_hidden @ X25 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('34',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) )
         != ( k1_funct_1 @ sk_B_2 @ X0 ) )
        | ( v2_funct_1 @ sk_B_2 )
        | ~ ( r2_hidden @ ( sk_C @ sk_B_2 ) @ sk_A )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( ( sk_C @ sk_B_2 )
          = X0 ) )
   <= ! [X24: $i,X25: $i] :
        ( ( X25 = X24 )
        | ( ( k1_funct_1 @ sk_B_2 @ X25 )
         != ( k1_funct_1 @ sk_B_2 @ X24 ) )
        | ~ ( r2_hidden @ X24 @ sk_A )
        | ~ ( r2_hidden @ X25 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( v2_funct_1 @ sk_B_2 )
        | ( ( sk_C @ sk_B_2 )
          = X0 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( v2_funct_1 @ sk_B_2 )
        | ( ( k1_funct_1 @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) )
         != ( k1_funct_1 @ sk_B_2 @ X0 ) ) )
   <= ! [X24: $i,X25: $i] :
        ( ( X25 = X24 )
        | ( ( k1_funct_1 @ sk_B_2 @ X25 )
         != ( k1_funct_1 @ sk_B_2 @ X24 ) )
        | ~ ( r2_hidden @ X24 @ sk_A )
        | ~ ( r2_hidden @ X25 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_2 @ ( sk_B_1 @ sk_B_2 ) )
         != ( k1_funct_1 @ sk_B_2 @ X0 ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( ( sk_C @ sk_B_2 )
          = X0 )
        | ( v2_funct_1 @ sk_B_2 ) )
   <= ! [X24: $i,X25: $i] :
        ( ( X25 = X24 )
        | ( ( k1_funct_1 @ sk_B_2 @ X25 )
         != ( k1_funct_1 @ sk_B_2 @ X24 ) )
        | ~ ( r2_hidden @ X24 @ sk_A )
        | ~ ( r2_hidden @ X25 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( v2_funct_1 @ sk_B_2 )
      | ( ( sk_C @ sk_B_2 )
        = ( sk_B_1 @ sk_B_2 ) )
      | ~ ( r2_hidden @ ( sk_B_1 @ sk_B_2 ) @ sk_A ) )
   <= ! [X24: $i,X25: $i] :
        ( ( X25 = X24 )
        | ( ( k1_funct_1 @ sk_B_2 @ X25 )
         != ( k1_funct_1 @ sk_B_2 @ X24 ) )
        | ~ ( r2_hidden @ X24 @ sk_A )
        | ~ ( r2_hidden @ X25 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['37'])).

thf('39',plain,
    ( ( ( v2_funct_1 @ sk_B_2 )
      | ( ( sk_C @ sk_B_2 )
        = ( sk_B_1 @ sk_B_2 ) )
      | ( v2_funct_1 @ sk_B_2 ) )
   <= ! [X24: $i,X25: $i] :
        ( ( X25 = X24 )
        | ( ( k1_funct_1 @ sk_B_2 @ X25 )
         != ( k1_funct_1 @ sk_B_2 @ X24 ) )
        | ~ ( r2_hidden @ X24 @ sk_A )
        | ~ ( r2_hidden @ X25 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','38'])).

thf('40',plain,
    ( ( ( ( sk_C @ sk_B_2 )
        = ( sk_B_1 @ sk_B_2 ) )
      | ( v2_funct_1 @ sk_B_2 ) )
   <= ! [X24: $i,X25: $i] :
        ( ( X25 = X24 )
        | ( ( k1_funct_1 @ sk_B_2 @ X25 )
         != ( k1_funct_1 @ sk_B_2 @ X24 ) )
        | ~ ( r2_hidden @ X24 @ sk_A )
        | ~ ( r2_hidden @ X25 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ~ ( v2_funct_1 @ sk_B_2 )
   <= ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,
    ( ( ( sk_C @ sk_B_2 )
      = ( sk_B_1 @ sk_B_2 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_2 )
      & ! [X24: $i,X25: $i] :
          ( ( X25 = X24 )
          | ( ( k1_funct_1 @ sk_B_2 @ X25 )
           != ( k1_funct_1 @ sk_B_2 @ X24 ) )
          | ~ ( r2_hidden @ X24 @ sk_A )
          | ~ ( r2_hidden @ X25 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X11: $i] :
      ( ( ( sk_B_1 @ X11 )
       != ( sk_C @ X11 ) )
      | ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('44',plain,
    ( ( ( ( sk_B_1 @ sk_B_2 )
       != ( sk_B_1 @ sk_B_2 ) )
      | ~ ( v1_relat_1 @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_B_2 )
      | ( v2_funct_1 @ sk_B_2 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_2 )
      & ! [X24: $i,X25: $i] :
          ( ( X25 = X24 )
          | ( ( k1_funct_1 @ sk_B_2 @ X25 )
           != ( k1_funct_1 @ sk_B_2 @ X24 ) )
          | ~ ( r2_hidden @ X24 @ sk_A )
          | ~ ( r2_hidden @ X25 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('46',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( ( sk_B_1 @ sk_B_2 )
       != ( sk_B_1 @ sk_B_2 ) )
      | ( v2_funct_1 @ sk_B_2 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_2 )
      & ! [X24: $i,X25: $i] :
          ( ( X25 = X24 )
          | ( ( k1_funct_1 @ sk_B_2 @ X25 )
           != ( k1_funct_1 @ sk_B_2 @ X24 ) )
          | ~ ( r2_hidden @ X24 @ sk_A )
          | ~ ( r2_hidden @ X25 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( v2_funct_1 @ sk_B_2 )
   <= ( ~ ( v2_funct_1 @ sk_B_2 )
      & ! [X24: $i,X25: $i] :
          ( ( X25 = X24 )
          | ( ( k1_funct_1 @ sk_B_2 @ X25 )
           != ( k1_funct_1 @ sk_B_2 @ X24 ) )
          | ~ ( r2_hidden @ X24 @ sk_A )
          | ~ ( r2_hidden @ X25 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ~ ( v2_funct_1 @ sk_B_2 )
   <= ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,
    ( ~ ! [X24: $i,X25: $i] :
          ( ( X25 = X24 )
          | ( ( k1_funct_1 @ sk_B_2 @ X25 )
           != ( k1_funct_1 @ sk_B_2 @ X24 ) )
          | ~ ( r2_hidden @ X24 @ sk_A )
          | ~ ( r2_hidden @ X25 @ sk_A ) )
    | ( v2_funct_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','50','51'])).

thf('53',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['3','52'])).

thf('54',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','50','51'])).

thf('56',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['54','55'])).

thf('57',plain,(
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

thf('58',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ( X22 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ X23 ) @ ( k1_funct_1 @ X23 @ X20 ) )
        = X20 )
      | ~ ( v2_funct_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t32_funct_2])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ sk_B_2 )
      | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_2 ) @ ( k1_funct_1 @ sk_B_2 @ X0 ) )
        = X0 )
      | ~ ( v1_funct_2 @ sk_B_2 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B_2 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25 = X24 )
      | ( ( k1_funct_1 @ sk_B_2 @ X25 )
       != ( k1_funct_1 @ sk_B_2 @ X24 ) )
      | ~ ( r2_hidden @ X24 @ sk_A )
      | ~ ( r2_hidden @ X25 @ sk_A )
      | ( v2_funct_1 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v2_funct_1 @ sk_B_2 )
   <= ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['60'])).

thf('62',plain,(
    v2_funct_1 @ sk_B_2 ),
    inference('sat_resolution*',[status(thm)],['5','50'])).

thf('63',plain,(
    v2_funct_1 @ sk_B_2 ),
    inference(simpl_trail,[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_2 @ sk_B_2 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_2 ) @ ( k1_funct_1 @ sk_B_2 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','63','64','65'])).

thf('67',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_2 ) @ ( k1_funct_1 @ sk_B_2 @ sk_C_1 ) )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['56','66'])).

thf('68',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
   <= ( r2_hidden @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['68'])).

thf('70',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['68'])).

thf('71',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['5','50','70'])).

thf('72',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['69','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_2 ) @ ( k1_funct_1 @ sk_B_2 @ X0 ) )
        = X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','63','64','65'])).

thf('74',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_2 ) @ ( k1_funct_1 @ sk_B_2 @ sk_D ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k1_funct_1 @ sk_B_2 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_2 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( k1_funct_1 @ sk_B_2 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_2 @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B_2 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_2 @ sk_D ) ) ),
    inference(split,[status(esa)],['75'])).

thf('77',plain,
    ( ( ( k1_funct_1 @ sk_B_2 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_2 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['75'])).

thf('78',plain,
    ( ( k1_funct_1 @ sk_B_2 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_2 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['5','50','77'])).

thf('79',plain,
    ( ( k1_funct_1 @ sk_B_2 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_2 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['76','78'])).

thf('80',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k2_funct_1 @ sk_B_2 ) @ ( k1_funct_1 @ sk_B_2 @ sk_C_1 ) )
      = sk_D ) ),
    inference(demod,[status(thm)],['74','79'])).

thf('81',plain,
    ( ( sk_C_1 = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','80'])).

thf('82',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( sk_C_1 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( sk_C_1 != sk_D )
   <= ( sk_C_1 != sk_D ) ),
    inference(split,[status(esa)],['83'])).

thf('85',plain,
    ( ( sk_C_1 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_2 ) ),
    inference(split,[status(esa)],['83'])).

thf('86',plain,(
    sk_C_1 != sk_D ),
    inference('sat_resolution*',[status(thm)],['5','50','85'])).

thf('87',plain,(
    sk_C_1 != sk_D ),
    inference(simpl_trail,[status(thm)],['84','86'])).

thf('88',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['82','87'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['53','88','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fLaakCP8Cn
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 19:01:36 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 91 iterations in 0.040s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.21/0.51  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(t77_funct_2, conjecture,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.51       ( ( v2_funct_1 @ B ) <=>
% 0.21/0.51         ( ![C:$i,D:$i]:
% 0.21/0.51           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.21/0.51               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.21/0.51             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i]:
% 0.21/0.51        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.51            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.51          ( ( v2_funct_1 @ B ) <=>
% 0.21/0.51            ( ![C:$i,D:$i]:
% 0.21/0.51              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.21/0.51                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.21/0.51                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t77_funct_2])).
% 0.21/0.51  thf('0', plain, (((r2_hidden @ sk_C_1 @ sk_A) | ~ (v2_funct_1 @ sk_B_2))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (((r2_hidden @ sk_C_1 @ sk_A)) <= (((r2_hidden @ sk_C_1 @ sk_A)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf(d1_xboole_0, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      ((~ (v1_xboole_0 @ sk_A)) <= (((r2_hidden @ sk_C_1 @ sk_A)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X24 : $i, X25 : $i]:
% 0.21/0.51         (((X25) = (X24))
% 0.21/0.51          | ((k1_funct_1 @ sk_B_2 @ X25) != (k1_funct_1 @ sk_B_2 @ X24))
% 0.21/0.51          | ~ (r2_hidden @ X24 @ sk_A)
% 0.21/0.51          | ~ (r2_hidden @ X25 @ sk_A)
% 0.21/0.51          | (v2_funct_1 @ sk_B_2))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (((v2_funct_1 @ sk_B_2)) | 
% 0.21/0.51       (![X24 : $i, X25 : $i]:
% 0.21/0.51          (((X25) = (X24))
% 0.21/0.51           | ((k1_funct_1 @ sk_B_2 @ X25) != (k1_funct_1 @ sk_B_2 @ X24))
% 0.21/0.51           | ~ (r2_hidden @ X24 @ sk_A)
% 0.21/0.51           | ~ (r2_hidden @ X25 @ sk_A)))),
% 0.21/0.51      inference('split', [status(esa)], ['4'])).
% 0.21/0.51  thf(d8_funct_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.51       ( ( v2_funct_1 @ A ) <=>
% 0.21/0.51         ( ![B:$i,C:$i]:
% 0.21/0.51           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.51               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.51               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.21/0.51             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X11 : $i]:
% 0.21/0.51         ((r2_hidden @ (sk_B_1 @ X11) @ (k1_relat_1 @ X11))
% 0.21/0.51          | (v2_funct_1 @ X11)
% 0.21/0.51          | ~ (v1_funct_1 @ X11)
% 0.21/0.51          | ~ (v1_relat_1 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc2_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.51         ((v4_relat_1 @ X17 @ X18)
% 0.21/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.51  thf('9', plain, ((v4_relat_1 @ sk_B_2 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf(d18_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ B ) =>
% 0.21/0.51       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X9 : $i, X10 : $i]:
% 0.21/0.51         (~ (v4_relat_1 @ X9 @ X10)
% 0.21/0.51          | (r1_tarski @ (k1_relat_1 @ X9) @ X10)
% 0.21/0.51          | ~ (v1_relat_1 @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ sk_B_2) | (r1_tarski @ (k1_relat_1 @ sk_B_2) @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc1_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( v1_relat_1 @ C ) ))).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.51         ((v1_relat_1 @ X14)
% 0.21/0.51          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.51  thf('14', plain, ((v1_relat_1 @ sk_B_2)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('15', plain, ((r1_tarski @ (k1_relat_1 @ sk_B_2) @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['11', '14'])).
% 0.21/0.51  thf(t3_subset, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X6 : $i, X8 : $i]:
% 0.21/0.51         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      ((m1_subset_1 @ (k1_relat_1 @ sk_B_2) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.51  thf(l3_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X3 @ X4)
% 0.21/0.51          | (r2_hidden @ X3 @ X5)
% 0.21/0.51          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.21/0.51      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_2)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ sk_B_2)
% 0.21/0.51        | ~ (v1_funct_1 @ sk_B_2)
% 0.21/0.51        | (v2_funct_1 @ sk_B_2)
% 0.21/0.51        | (r2_hidden @ (sk_B_1 @ sk_B_2) @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['6', '19'])).
% 0.21/0.51  thf('21', plain, ((v1_relat_1 @ sk_B_2)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('22', plain, ((v1_funct_1 @ sk_B_2)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (((v2_funct_1 @ sk_B_2) | (r2_hidden @ (sk_B_1 @ sk_B_2) @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X11 : $i]:
% 0.21/0.51         ((r2_hidden @ (sk_C @ X11) @ (k1_relat_1 @ X11))
% 0.21/0.51          | (v2_funct_1 @ X11)
% 0.21/0.51          | ~ (v1_funct_1 @ X11)
% 0.21/0.51          | ~ (v1_relat_1 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B_2)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ sk_B_2)
% 0.21/0.51        | ~ (v1_funct_1 @ sk_B_2)
% 0.21/0.51        | (v2_funct_1 @ sk_B_2)
% 0.21/0.51        | (r2_hidden @ (sk_C @ sk_B_2) @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf('27', plain, ((v1_relat_1 @ sk_B_2)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('28', plain, ((v1_funct_1 @ sk_B_2)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (((v2_funct_1 @ sk_B_2) | (r2_hidden @ (sk_C @ sk_B_2) @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X11 : $i]:
% 0.21/0.51         (((k1_funct_1 @ X11 @ (sk_B_1 @ X11))
% 0.21/0.51            = (k1_funct_1 @ X11 @ (sk_C @ X11)))
% 0.21/0.51          | (v2_funct_1 @ X11)
% 0.21/0.51          | ~ (v1_funct_1 @ X11)
% 0.21/0.51          | ~ (v1_relat_1 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      ((![X24 : $i, X25 : $i]:
% 0.21/0.51          (((X25) = (X24))
% 0.21/0.51           | ((k1_funct_1 @ sk_B_2 @ X25) != (k1_funct_1 @ sk_B_2 @ X24))
% 0.21/0.51           | ~ (r2_hidden @ X24 @ sk_A)
% 0.21/0.51           | ~ (r2_hidden @ X25 @ sk_A)))
% 0.21/0.51         <= ((![X24 : $i, X25 : $i]:
% 0.21/0.51                (((X25) = (X24))
% 0.21/0.51                 | ((k1_funct_1 @ sk_B_2 @ X25) != (k1_funct_1 @ sk_B_2 @ X24))
% 0.21/0.51                 | ~ (r2_hidden @ X24 @ sk_A)
% 0.21/0.51                 | ~ (r2_hidden @ X25 @ sk_A))))),
% 0.21/0.51      inference('split', [status(esa)], ['4'])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          (((k1_funct_1 @ sk_B_2 @ (sk_B_1 @ sk_B_2))
% 0.21/0.51             != (k1_funct_1 @ sk_B_2 @ X0))
% 0.21/0.51           | ~ (v1_relat_1 @ sk_B_2)
% 0.21/0.51           | ~ (v1_funct_1 @ sk_B_2)
% 0.21/0.51           | (v2_funct_1 @ sk_B_2)
% 0.21/0.51           | ~ (r2_hidden @ (sk_C @ sk_B_2) @ sk_A)
% 0.21/0.51           | ~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.51           | ((sk_C @ sk_B_2) = (X0))))
% 0.21/0.51         <= ((![X24 : $i, X25 : $i]:
% 0.21/0.51                (((X25) = (X24))
% 0.21/0.51                 | ((k1_funct_1 @ sk_B_2 @ X25) != (k1_funct_1 @ sk_B_2 @ X24))
% 0.21/0.51                 | ~ (r2_hidden @ X24 @ sk_A)
% 0.21/0.51                 | ~ (r2_hidden @ X25 @ sk_A))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.51  thf('33', plain, ((v1_relat_1 @ sk_B_2)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('34', plain, ((v1_funct_1 @ sk_B_2)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          (((k1_funct_1 @ sk_B_2 @ (sk_B_1 @ sk_B_2))
% 0.21/0.51             != (k1_funct_1 @ sk_B_2 @ X0))
% 0.21/0.51           | (v2_funct_1 @ sk_B_2)
% 0.21/0.51           | ~ (r2_hidden @ (sk_C @ sk_B_2) @ sk_A)
% 0.21/0.51           | ~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.51           | ((sk_C @ sk_B_2) = (X0))))
% 0.21/0.51         <= ((![X24 : $i, X25 : $i]:
% 0.21/0.51                (((X25) = (X24))
% 0.21/0.51                 | ((k1_funct_1 @ sk_B_2 @ X25) != (k1_funct_1 @ sk_B_2 @ X24))
% 0.21/0.51                 | ~ (r2_hidden @ X24 @ sk_A)
% 0.21/0.51                 | ~ (r2_hidden @ X25 @ sk_A))))),
% 0.21/0.51      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          ((v2_funct_1 @ sk_B_2)
% 0.21/0.51           | ((sk_C @ sk_B_2) = (X0))
% 0.21/0.51           | ~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.51           | (v2_funct_1 @ sk_B_2)
% 0.21/0.51           | ((k1_funct_1 @ sk_B_2 @ (sk_B_1 @ sk_B_2))
% 0.21/0.51               != (k1_funct_1 @ sk_B_2 @ X0))))
% 0.21/0.51         <= ((![X24 : $i, X25 : $i]:
% 0.21/0.51                (((X25) = (X24))
% 0.21/0.51                 | ((k1_funct_1 @ sk_B_2 @ X25) != (k1_funct_1 @ sk_B_2 @ X24))
% 0.21/0.51                 | ~ (r2_hidden @ X24 @ sk_A)
% 0.21/0.51                 | ~ (r2_hidden @ X25 @ sk_A))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['29', '35'])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      ((![X0 : $i]:
% 0.21/0.51          (((k1_funct_1 @ sk_B_2 @ (sk_B_1 @ sk_B_2))
% 0.21/0.51             != (k1_funct_1 @ sk_B_2 @ X0))
% 0.21/0.51           | ~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.51           | ((sk_C @ sk_B_2) = (X0))
% 0.21/0.51           | (v2_funct_1 @ sk_B_2)))
% 0.21/0.51         <= ((![X24 : $i, X25 : $i]:
% 0.21/0.51                (((X25) = (X24))
% 0.21/0.51                 | ((k1_funct_1 @ sk_B_2 @ X25) != (k1_funct_1 @ sk_B_2 @ X24))
% 0.21/0.51                 | ~ (r2_hidden @ X24 @ sk_A)
% 0.21/0.51                 | ~ (r2_hidden @ X25 @ sk_A))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      ((((v2_funct_1 @ sk_B_2)
% 0.21/0.51         | ((sk_C @ sk_B_2) = (sk_B_1 @ sk_B_2))
% 0.21/0.51         | ~ (r2_hidden @ (sk_B_1 @ sk_B_2) @ sk_A)))
% 0.21/0.51         <= ((![X24 : $i, X25 : $i]:
% 0.21/0.51                (((X25) = (X24))
% 0.21/0.51                 | ((k1_funct_1 @ sk_B_2 @ X25) != (k1_funct_1 @ sk_B_2 @ X24))
% 0.21/0.51                 | ~ (r2_hidden @ X24 @ sk_A)
% 0.21/0.51                 | ~ (r2_hidden @ X25 @ sk_A))))),
% 0.21/0.51      inference('eq_res', [status(thm)], ['37'])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      ((((v2_funct_1 @ sk_B_2)
% 0.21/0.51         | ((sk_C @ sk_B_2) = (sk_B_1 @ sk_B_2))
% 0.21/0.51         | (v2_funct_1 @ sk_B_2)))
% 0.21/0.51         <= ((![X24 : $i, X25 : $i]:
% 0.21/0.51                (((X25) = (X24))
% 0.21/0.51                 | ((k1_funct_1 @ sk_B_2 @ X25) != (k1_funct_1 @ sk_B_2 @ X24))
% 0.21/0.51                 | ~ (r2_hidden @ X24 @ sk_A)
% 0.21/0.51                 | ~ (r2_hidden @ X25 @ sk_A))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['23', '38'])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      (((((sk_C @ sk_B_2) = (sk_B_1 @ sk_B_2)) | (v2_funct_1 @ sk_B_2)))
% 0.21/0.51         <= ((![X24 : $i, X25 : $i]:
% 0.21/0.51                (((X25) = (X24))
% 0.21/0.51                 | ((k1_funct_1 @ sk_B_2 @ X25) != (k1_funct_1 @ sk_B_2 @ X24))
% 0.21/0.51                 | ~ (r2_hidden @ X24 @ sk_A)
% 0.21/0.51                 | ~ (r2_hidden @ X25 @ sk_A))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['39'])).
% 0.21/0.51  thf('41', plain, ((~ (v2_funct_1 @ sk_B_2)) <= (~ ((v2_funct_1 @ sk_B_2)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      ((((sk_C @ sk_B_2) = (sk_B_1 @ sk_B_2)))
% 0.21/0.51         <= (~ ((v2_funct_1 @ sk_B_2)) & 
% 0.21/0.51             (![X24 : $i, X25 : $i]:
% 0.21/0.51                (((X25) = (X24))
% 0.21/0.51                 | ((k1_funct_1 @ sk_B_2 @ X25) != (k1_funct_1 @ sk_B_2 @ X24))
% 0.21/0.51                 | ~ (r2_hidden @ X24 @ sk_A)
% 0.21/0.51                 | ~ (r2_hidden @ X25 @ sk_A))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (![X11 : $i]:
% 0.21/0.51         (((sk_B_1 @ X11) != (sk_C @ X11))
% 0.21/0.51          | (v2_funct_1 @ X11)
% 0.21/0.51          | ~ (v1_funct_1 @ X11)
% 0.21/0.51          | ~ (v1_relat_1 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (((((sk_B_1 @ sk_B_2) != (sk_B_1 @ sk_B_2))
% 0.21/0.51         | ~ (v1_relat_1 @ sk_B_2)
% 0.21/0.51         | ~ (v1_funct_1 @ sk_B_2)
% 0.21/0.51         | (v2_funct_1 @ sk_B_2)))
% 0.21/0.51         <= (~ ((v2_funct_1 @ sk_B_2)) & 
% 0.21/0.51             (![X24 : $i, X25 : $i]:
% 0.21/0.51                (((X25) = (X24))
% 0.21/0.51                 | ((k1_funct_1 @ sk_B_2 @ X25) != (k1_funct_1 @ sk_B_2 @ X24))
% 0.21/0.51                 | ~ (r2_hidden @ X24 @ sk_A)
% 0.21/0.51                 | ~ (r2_hidden @ X25 @ sk_A))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.51  thf('45', plain, ((v1_relat_1 @ sk_B_2)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('46', plain, ((v1_funct_1 @ sk_B_2)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (((((sk_B_1 @ sk_B_2) != (sk_B_1 @ sk_B_2)) | (v2_funct_1 @ sk_B_2)))
% 0.21/0.51         <= (~ ((v2_funct_1 @ sk_B_2)) & 
% 0.21/0.51             (![X24 : $i, X25 : $i]:
% 0.21/0.51                (((X25) = (X24))
% 0.21/0.51                 | ((k1_funct_1 @ sk_B_2 @ X25) != (k1_funct_1 @ sk_B_2 @ X24))
% 0.21/0.51                 | ~ (r2_hidden @ X24 @ sk_A)
% 0.21/0.51                 | ~ (r2_hidden @ X25 @ sk_A))))),
% 0.21/0.51      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (((v2_funct_1 @ sk_B_2))
% 0.21/0.51         <= (~ ((v2_funct_1 @ sk_B_2)) & 
% 0.21/0.51             (![X24 : $i, X25 : $i]:
% 0.21/0.51                (((X25) = (X24))
% 0.21/0.51                 | ((k1_funct_1 @ sk_B_2 @ X25) != (k1_funct_1 @ sk_B_2 @ X24))
% 0.21/0.51                 | ~ (r2_hidden @ X24 @ sk_A)
% 0.21/0.51                 | ~ (r2_hidden @ X25 @ sk_A))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.51  thf('49', plain, ((~ (v2_funct_1 @ sk_B_2)) <= (~ ((v2_funct_1 @ sk_B_2)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (~
% 0.21/0.51       (![X24 : $i, X25 : $i]:
% 0.21/0.51          (((X25) = (X24))
% 0.21/0.51           | ((k1_funct_1 @ sk_B_2 @ X25) != (k1_funct_1 @ sk_B_2 @ X24))
% 0.21/0.51           | ~ (r2_hidden @ X24 @ sk_A)
% 0.21/0.51           | ~ (r2_hidden @ X25 @ sk_A))) | 
% 0.21/0.51       ((v2_funct_1 @ sk_B_2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.51  thf('51', plain, (((r2_hidden @ sk_C_1 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_2))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('52', plain, (((r2_hidden @ sk_C_1 @ sk_A))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['5', '50', '51'])).
% 0.21/0.51  thf('53', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['3', '52'])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (((r2_hidden @ sk_C_1 @ sk_A)) <= (((r2_hidden @ sk_C_1 @ sk_A)))),
% 0.21/0.51      inference('split', [status(esa)], ['0'])).
% 0.21/0.51  thf('55', plain, (((r2_hidden @ sk_C_1 @ sk_A))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['5', '50', '51'])).
% 0.21/0.51  thf('56', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['54', '55'])).
% 0.21/0.51  thf('57', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t32_funct_2, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.51       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.21/0.51         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.51           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.21/0.51             ( C ) ) ) ) ))).
% 0.21/0.51  thf('58', plain,
% 0.21/0.51      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X20 @ X21)
% 0.21/0.51          | ((X22) = (k1_xboole_0))
% 0.21/0.51          | ~ (v1_funct_1 @ X23)
% 0.21/0.51          | ~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.21/0.51          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.21/0.51          | ((k1_funct_1 @ (k2_funct_1 @ X23) @ (k1_funct_1 @ X23 @ X20))
% 0.21/0.51              = (X20))
% 0.21/0.51          | ~ (v2_funct_1 @ X23))),
% 0.21/0.51      inference('cnf', [status(esa)], [t32_funct_2])).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v2_funct_1 @ sk_B_2)
% 0.21/0.51          | ((k1_funct_1 @ (k2_funct_1 @ sk_B_2) @ (k1_funct_1 @ sk_B_2 @ X0))
% 0.21/0.51              = (X0))
% 0.21/0.51          | ~ (v1_funct_2 @ sk_B_2 @ sk_A @ sk_A)
% 0.21/0.51          | ~ (v1_funct_1 @ sk_B_2)
% 0.21/0.51          | ((sk_A) = (k1_xboole_0))
% 0.21/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.51  thf('60', plain,
% 0.21/0.51      (![X24 : $i, X25 : $i]:
% 0.21/0.51         (((X25) = (X24))
% 0.21/0.51          | ((k1_funct_1 @ sk_B_2 @ X25) != (k1_funct_1 @ sk_B_2 @ X24))
% 0.21/0.51          | ~ (r2_hidden @ X24 @ sk_A)
% 0.21/0.51          | ~ (r2_hidden @ X25 @ sk_A)
% 0.21/0.51          | (v2_funct_1 @ sk_B_2))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('61', plain, (((v2_funct_1 @ sk_B_2)) <= (((v2_funct_1 @ sk_B_2)))),
% 0.21/0.51      inference('split', [status(esa)], ['60'])).
% 0.21/0.51  thf('62', plain, (((v2_funct_1 @ sk_B_2))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['5', '50'])).
% 0.21/0.51  thf('63', plain, ((v2_funct_1 @ sk_B_2)),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['61', '62'])).
% 0.21/0.51  thf('64', plain, ((v1_funct_2 @ sk_B_2 @ sk_A @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('65', plain, ((v1_funct_1 @ sk_B_2)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('66', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k1_funct_1 @ (k2_funct_1 @ sk_B_2) @ (k1_funct_1 @ sk_B_2 @ X0))
% 0.21/0.51            = (X0))
% 0.21/0.51          | ((sk_A) = (k1_xboole_0))
% 0.21/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['59', '63', '64', '65'])).
% 0.21/0.51  thf('67', plain,
% 0.21/0.51      ((((sk_A) = (k1_xboole_0))
% 0.21/0.51        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_2) @ (k1_funct_1 @ sk_B_2 @ sk_C_1))
% 0.21/0.51            = (sk_C_1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['56', '66'])).
% 0.21/0.51  thf('68', plain, (((r2_hidden @ sk_D @ sk_A) | ~ (v2_funct_1 @ sk_B_2))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('69', plain,
% 0.21/0.51      (((r2_hidden @ sk_D @ sk_A)) <= (((r2_hidden @ sk_D @ sk_A)))),
% 0.21/0.51      inference('split', [status(esa)], ['68'])).
% 0.21/0.51  thf('70', plain, (((r2_hidden @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_B_2))),
% 0.21/0.51      inference('split', [status(esa)], ['68'])).
% 0.21/0.51  thf('71', plain, (((r2_hidden @ sk_D @ sk_A))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['5', '50', '70'])).
% 0.21/0.51  thf('72', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['69', '71'])).
% 0.21/0.51  thf('73', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k1_funct_1 @ (k2_funct_1 @ sk_B_2) @ (k1_funct_1 @ sk_B_2 @ X0))
% 0.21/0.51            = (X0))
% 0.21/0.51          | ((sk_A) = (k1_xboole_0))
% 0.21/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['59', '63', '64', '65'])).
% 0.21/0.51  thf('74', plain,
% 0.21/0.51      ((((sk_A) = (k1_xboole_0))
% 0.21/0.51        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_2) @ (k1_funct_1 @ sk_B_2 @ sk_D))
% 0.21/0.51            = (sk_D)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.51  thf('75', plain,
% 0.21/0.51      ((((k1_funct_1 @ sk_B_2 @ sk_C_1) = (k1_funct_1 @ sk_B_2 @ sk_D))
% 0.21/0.51        | ~ (v2_funct_1 @ sk_B_2))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('76', plain,
% 0.21/0.51      ((((k1_funct_1 @ sk_B_2 @ sk_C_1) = (k1_funct_1 @ sk_B_2 @ sk_D)))
% 0.21/0.51         <= ((((k1_funct_1 @ sk_B_2 @ sk_C_1) = (k1_funct_1 @ sk_B_2 @ sk_D))))),
% 0.21/0.51      inference('split', [status(esa)], ['75'])).
% 0.21/0.51  thf('77', plain,
% 0.21/0.51      ((((k1_funct_1 @ sk_B_2 @ sk_C_1) = (k1_funct_1 @ sk_B_2 @ sk_D))) | 
% 0.21/0.51       ~ ((v2_funct_1 @ sk_B_2))),
% 0.21/0.51      inference('split', [status(esa)], ['75'])).
% 0.21/0.51  thf('78', plain,
% 0.21/0.51      ((((k1_funct_1 @ sk_B_2 @ sk_C_1) = (k1_funct_1 @ sk_B_2 @ sk_D)))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['5', '50', '77'])).
% 0.21/0.51  thf('79', plain,
% 0.21/0.51      (((k1_funct_1 @ sk_B_2 @ sk_C_1) = (k1_funct_1 @ sk_B_2 @ sk_D))),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['76', '78'])).
% 0.21/0.51  thf('80', plain,
% 0.21/0.51      ((((sk_A) = (k1_xboole_0))
% 0.21/0.51        | ((k1_funct_1 @ (k2_funct_1 @ sk_B_2) @ (k1_funct_1 @ sk_B_2 @ sk_C_1))
% 0.21/0.51            = (sk_D)))),
% 0.21/0.51      inference('demod', [status(thm)], ['74', '79'])).
% 0.21/0.51  thf('81', plain,
% 0.21/0.51      ((((sk_C_1) = (sk_D))
% 0.21/0.51        | ((sk_A) = (k1_xboole_0))
% 0.21/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['67', '80'])).
% 0.21/0.51  thf('82', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_C_1) = (sk_D)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['81'])).
% 0.21/0.51  thf('83', plain, ((((sk_C_1) != (sk_D)) | ~ (v2_funct_1 @ sk_B_2))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('84', plain, ((((sk_C_1) != (sk_D))) <= (~ (((sk_C_1) = (sk_D))))),
% 0.21/0.51      inference('split', [status(esa)], ['83'])).
% 0.21/0.51  thf('85', plain, (~ (((sk_C_1) = (sk_D))) | ~ ((v2_funct_1 @ sk_B_2))),
% 0.21/0.51      inference('split', [status(esa)], ['83'])).
% 0.21/0.51  thf('86', plain, (~ (((sk_C_1) = (sk_D)))),
% 0.21/0.51      inference('sat_resolution*', [status(thm)], ['5', '50', '85'])).
% 0.21/0.51  thf('87', plain, (((sk_C_1) != (sk_D))),
% 0.21/0.51      inference('simpl_trail', [status(thm)], ['84', '86'])).
% 0.21/0.51  thf('88', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['82', '87'])).
% 0.21/0.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.51  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.51  thf('90', plain, ($false),
% 0.21/0.51      inference('demod', [status(thm)], ['53', '88', '89'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
