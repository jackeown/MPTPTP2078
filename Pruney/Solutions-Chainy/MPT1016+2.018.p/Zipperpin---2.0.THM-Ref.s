%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RKchcWcT45

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:53 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 684 expanded)
%              Number of leaves         :   22 ( 202 expanded)
%              Depth                    :   21
%              Number of atoms          :  966 (12201 expanded)
%              Number of equality atoms :   89 ( 869 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12 = X11 )
      | ( ( k1_funct_1 @ sk_B_1 @ X12 )
       != ( k1_funct_1 @ sk_B_1 @ X11 ) )
      | ~ ( r2_hidden @ X11 @ sk_A )
      | ~ ( r2_hidden @ X12 @ sk_A )
      | ( v2_funct_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X9 @ X10 )
        = X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X9 @ X9 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('11',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['6','7','8','11'])).

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

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
       != ( k1_funct_1 @ X0 @ X2 ) )
      | ( X1 = X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('17',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['6','7','8','11'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['14','17','18','19'])).

thf('21',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ( ( k1_funct_1 @ sk_B_1 @ X1 )
         != ( k1_funct_1 @ sk_B_1 @ X0 ) )
        | ( X1 = X0 )
        | ~ ( r2_hidden @ X1 @ sk_A ) )
   <= ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','20'])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
         != ( k1_funct_1 @ sk_B_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_D @ sk_A )
        | ( sk_D = X0 )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( ( v2_funct_1 @ sk_B_1 )
      & ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
        = ( k1_funct_1 @ sk_B_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['1','21'])).

thf('23',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ! [X11: $i,X12: $i] :
        ( ( X12 = X11 )
        | ( ( k1_funct_1 @ sk_B_1 @ X12 )
         != ( k1_funct_1 @ sk_B_1 @ X11 ) )
        | ~ ( r2_hidden @ X11 @ sk_A )
        | ~ ( r2_hidden @ X12 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('24',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['6','7','8','11'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('28',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_C @ X0 ) ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('31',plain,
    ( ! [X11: $i,X12: $i] :
        ( ( X12 = X11 )
        | ( ( k1_funct_1 @ sk_B_1 @ X12 )
         != ( k1_funct_1 @ sk_B_1 @ X11 ) )
        | ~ ( r2_hidden @ X11 @ sk_A )
        | ~ ( r2_hidden @ X12 @ sk_A ) )
   <= ! [X11: $i,X12: $i] :
        ( ( X12 = X11 )
        | ( ( k1_funct_1 @ sk_B_1 @ X12 )
         != ( k1_funct_1 @ sk_B_1 @ X11 ) )
        | ~ ( r2_hidden @ X11 @ sk_A )
        | ~ ( r2_hidden @ X12 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('32',plain,
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
   <= ! [X11: $i,X12: $i] :
        ( ( X12 = X11 )
        | ( ( k1_funct_1 @ sk_B_1 @ X12 )
         != ( k1_funct_1 @ sk_B_1 @ X11 ) )
        | ~ ( r2_hidden @ X11 @ sk_A )
        | ~ ( r2_hidden @ X12 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('34',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ( v2_funct_1 @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_1 ) ) )
   <= ! [X11: $i,X12: $i] :
        ( ( X12 = X11 )
        | ( ( k1_funct_1 @ sk_B_1 @ X12 )
         != ( k1_funct_1 @ sk_B_1 @ X11 ) )
        | ~ ( r2_hidden @ X11 @ sk_A )
        | ~ ( r2_hidden @ X12 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( v2_funct_1 @ sk_B_1 )
        | ( X0
          = ( sk_C @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( v2_funct_1 @ sk_B_1 )
        | ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
   <= ! [X11: $i,X12: $i] :
        ( ( X12 = X11 )
        | ( ( k1_funct_1 @ sk_B_1 @ X12 )
         != ( k1_funct_1 @ sk_B_1 @ X11 ) )
        | ~ ( r2_hidden @ X11 @ sk_A )
        | ~ ( r2_hidden @ X12 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_1 ) )
        | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X11: $i,X12: $i] :
        ( ( X12 = X11 )
        | ( ( k1_funct_1 @ sk_B_1 @ X12 )
         != ( k1_funct_1 @ sk_B_1 @ X11 ) )
        | ~ ( r2_hidden @ X11 @ sk_A )
        | ~ ( r2_hidden @ X12 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( ( v2_funct_1 @ sk_B_1 )
      | ( ( sk_B @ sk_B_1 )
        = ( sk_C @ sk_B_1 ) )
      | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) )
   <= ! [X11: $i,X12: $i] :
        ( ( X12 = X11 )
        | ( ( k1_funct_1 @ sk_B_1 @ X12 )
         != ( k1_funct_1 @ sk_B_1 @ X11 ) )
        | ~ ( r2_hidden @ X11 @ sk_A )
        | ~ ( r2_hidden @ X12 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['37'])).

thf('39',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['6','7','8','11'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('41',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('43',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( ( ( sk_B @ sk_B_1 )
        = ( sk_C @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X11: $i,X12: $i] :
        ( ( X12 = X11 )
        | ( ( k1_funct_1 @ sk_B_1 @ X12 )
         != ( k1_funct_1 @ sk_B_1 @ X11 ) )
        | ~ ( r2_hidden @ X11 @ sk_A )
        | ~ ( r2_hidden @ X12 @ sk_A ) ) ),
    inference(clc,[status(thm)],['38','44'])).

thf('46',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( ( sk_B @ sk_B_1 )
      = ( sk_C @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X11: $i,X12: $i] :
          ( ( X12 = X11 )
          | ( ( k1_funct_1 @ sk_B_1 @ X12 )
           != ( k1_funct_1 @ sk_B_1 @ X11 ) )
          | ~ ( r2_hidden @ X11 @ sk_A )
          | ~ ( r2_hidden @ X12 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != ( sk_C @ X0 ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('50',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X11: $i,X12: $i] :
          ( ( X12 = X11 )
          | ( ( k1_funct_1 @ sk_B_1 @ X12 )
           != ( k1_funct_1 @ sk_B_1 @ X11 ) )
          | ~ ( r2_hidden @ X11 @ sk_A )
          | ~ ( r2_hidden @ X12 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('52',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X11: $i,X12: $i] :
          ( ( X12 = X11 )
          | ( ( k1_funct_1 @ sk_B_1 @ X12 )
           != ( k1_funct_1 @ sk_B_1 @ X11 ) )
          | ~ ( r2_hidden @ X11 @ sk_A )
          | ~ ( r2_hidden @ X12 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X11: $i,X12: $i] :
          ( ( X12 = X11 )
          | ( ( k1_funct_1 @ sk_B_1 @ X12 )
           != ( k1_funct_1 @ sk_B_1 @ X11 ) )
          | ~ ( r2_hidden @ X11 @ sk_A )
          | ~ ( r2_hidden @ X12 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['46'])).

thf('56',plain,
    ( ~ ! [X11: $i,X12: $i] :
          ( ( X12 = X11 )
          | ( ( k1_funct_1 @ sk_B_1 @ X12 )
           != ( k1_funct_1 @ sk_B_1 @ X11 ) )
          | ~ ( r2_hidden @ X11 @ sk_A )
          | ~ ( r2_hidden @ X12 @ sk_A ) )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['23','56'])).

thf('58',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('59',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['23','56','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ sk_D @ sk_A )
      | ( sk_D = X0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['22','57','59'])).

thf('61',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
   <= ( r2_hidden @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['61'])).

thf('63',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['61'])).

thf('64',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['23','56','63'])).

thf('65',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['62','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ( sk_D = X0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','65'])).

thf('67',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_A )
    | ( sk_D = sk_C_1 ) ),
    inference(eq_res,[status(thm)],['66'])).

thf('68',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('69',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['46'])).

thf('70',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['23','56','69'])).

thf('71',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['68','70'])).

thf('72',plain,(
    sk_D = sk_C_1 ),
    inference(demod,[status(thm)],['67','71'])).

thf('73',plain,
    ( ( sk_C_1 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( sk_C_1 != sk_D )
   <= ( sk_C_1 != sk_D ) ),
    inference(split,[status(esa)],['73'])).

thf('75',plain,
    ( ( sk_C_1 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['73'])).

thf('76',plain,(
    sk_C_1 != sk_D ),
    inference('sat_resolution*',[status(thm)],['23','56','75'])).

thf('77',plain,(
    sk_C_1 != sk_D ),
    inference(simpl_trail,[status(thm)],['74','76'])).

thf('78',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['72','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RKchcWcT45
% 0.16/0.36  % Computer   : n010.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 16:08:30 EST 2020
% 0.23/0.37  % CPUTime    : 
% 0.23/0.37  % Running portfolio for 600 s
% 0.23/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.23/0.37  % Number of cores: 8
% 0.23/0.37  % Python version: Python 3.6.8
% 0.23/0.37  % Running in FO mode
% 0.23/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.51  % Solved by: fo/fo7.sh
% 0.23/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.51  % done 60 iterations in 0.031s
% 0.23/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.51  % SZS output start Refutation
% 0.23/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.23/0.51  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.23/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.23/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.23/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.23/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.51  thf(sk_C_type, type, sk_C: $i > $i).
% 0.23/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.51  thf(t77_funct_2, conjecture,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.23/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.23/0.51       ( ( v2_funct_1 @ B ) <=>
% 0.23/0.51         ( ![C:$i,D:$i]:
% 0.23/0.51           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.23/0.51               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.23/0.51             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.23/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.51    (~( ![A:$i,B:$i]:
% 0.23/0.51        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.23/0.51            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.23/0.51          ( ( v2_funct_1 @ B ) <=>
% 0.23/0.51            ( ![C:$i,D:$i]:
% 0.23/0.51              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.23/0.51                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.23/0.51                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.23/0.51    inference('cnf.neg', [status(esa)], [t77_funct_2])).
% 0.23/0.51  thf('0', plain,
% 0.23/0.51      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.23/0.51        | ~ (v2_funct_1 @ sk_B_1))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('1', plain,
% 0.23/0.51      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D)))
% 0.23/0.51         <= ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))))),
% 0.23/0.51      inference('split', [status(esa)], ['0'])).
% 0.23/0.51  thf('2', plain,
% 0.23/0.51      (![X11 : $i, X12 : $i]:
% 0.23/0.51         (((X12) = (X11))
% 0.23/0.51          | ((k1_funct_1 @ sk_B_1 @ X12) != (k1_funct_1 @ sk_B_1 @ X11))
% 0.23/0.51          | ~ (r2_hidden @ X11 @ sk_A)
% 0.23/0.51          | ~ (r2_hidden @ X12 @ sk_A)
% 0.23/0.51          | (v2_funct_1 @ sk_B_1))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('3', plain, (((v2_funct_1 @ sk_B_1)) <= (((v2_funct_1 @ sk_B_1)))),
% 0.23/0.51      inference('split', [status(esa)], ['2'])).
% 0.23/0.51  thf('4', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(t67_funct_2, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.23/0.51         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.23/0.51       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.23/0.51  thf('5', plain,
% 0.23/0.51      (![X9 : $i, X10 : $i]:
% 0.23/0.51         (((k1_relset_1 @ X9 @ X9 @ X10) = (X9))
% 0.23/0.51          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X9)))
% 0.23/0.51          | ~ (v1_funct_2 @ X10 @ X9 @ X9)
% 0.23/0.51          | ~ (v1_funct_1 @ X10))),
% 0.23/0.51      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.23/0.51  thf('6', plain,
% 0.23/0.51      ((~ (v1_funct_1 @ sk_B_1)
% 0.23/0.51        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.23/0.51        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (sk_A)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.51  thf('7', plain, ((v1_funct_1 @ sk_B_1)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('8', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('9', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(redefinition_k1_relset_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.23/0.51  thf('10', plain,
% 0.23/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.23/0.51         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 0.23/0.51          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.23/0.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.23/0.51  thf('11', plain,
% 0.23/0.51      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 0.23/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.23/0.51  thf('12', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.23/0.51      inference('demod', [status(thm)], ['6', '7', '8', '11'])).
% 0.23/0.51  thf(d8_funct_1, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.23/0.51       ( ( v2_funct_1 @ A ) <=>
% 0.23/0.51         ( ![B:$i,C:$i]:
% 0.23/0.51           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.23/0.51               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.23/0.51               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.23/0.51             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.23/0.51  thf('13', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.51         (~ (v2_funct_1 @ X0)
% 0.23/0.51          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.23/0.51          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.23/0.51          | ((k1_funct_1 @ X0 @ X1) != (k1_funct_1 @ X0 @ X2))
% 0.23/0.51          | ((X1) = (X2))
% 0.23/0.51          | ~ (v1_funct_1 @ X0)
% 0.23/0.51          | ~ (v1_relat_1 @ X0))),
% 0.23/0.51      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.23/0.51  thf('14', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (~ (r2_hidden @ X0 @ sk_A)
% 0.23/0.51          | ~ (v1_relat_1 @ sk_B_1)
% 0.23/0.51          | ~ (v1_funct_1 @ sk_B_1)
% 0.23/0.51          | ((X0) = (X1))
% 0.23/0.51          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.23/0.51          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1))
% 0.23/0.51          | ~ (v2_funct_1 @ sk_B_1))),
% 0.23/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.23/0.51  thf('15', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(cc1_relset_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.51       ( v1_relat_1 @ C ) ))).
% 0.23/0.51  thf('16', plain,
% 0.23/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.51         ((v1_relat_1 @ X3)
% 0.23/0.51          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.23/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.23/0.51  thf('17', plain, ((v1_relat_1 @ sk_B_1)),
% 0.23/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.51  thf('18', plain, ((v1_funct_1 @ sk_B_1)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('19', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.23/0.51      inference('demod', [status(thm)], ['6', '7', '8', '11'])).
% 0.23/0.51  thf('20', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]:
% 0.23/0.51         (~ (r2_hidden @ X0 @ sk_A)
% 0.23/0.51          | ((X0) = (X1))
% 0.23/0.51          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.23/0.51          | ~ (r2_hidden @ X1 @ sk_A)
% 0.23/0.51          | ~ (v2_funct_1 @ sk_B_1))),
% 0.23/0.51      inference('demod', [status(thm)], ['14', '17', '18', '19'])).
% 0.23/0.51  thf('21', plain,
% 0.23/0.51      ((![X0 : $i, X1 : $i]:
% 0.23/0.51          (~ (r2_hidden @ X0 @ sk_A)
% 0.23/0.51           | ((k1_funct_1 @ sk_B_1 @ X1) != (k1_funct_1 @ sk_B_1 @ X0))
% 0.23/0.51           | ((X1) = (X0))
% 0.23/0.51           | ~ (r2_hidden @ X1 @ sk_A)))
% 0.23/0.51         <= (((v2_funct_1 @ sk_B_1)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['3', '20'])).
% 0.23/0.51  thf('22', plain,
% 0.23/0.51      ((![X0 : $i]:
% 0.23/0.51          (((k1_funct_1 @ sk_B_1 @ sk_C_1) != (k1_funct_1 @ sk_B_1 @ X0))
% 0.23/0.51           | ~ (r2_hidden @ sk_D @ sk_A)
% 0.23/0.51           | ((sk_D) = (X0))
% 0.23/0.51           | ~ (r2_hidden @ X0 @ sk_A)))
% 0.23/0.51         <= (((v2_funct_1 @ sk_B_1)) & 
% 0.23/0.51             (((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))))),
% 0.23/0.51      inference('sup-', [status(thm)], ['1', '21'])).
% 0.23/0.51  thf('23', plain,
% 0.23/0.51      (((v2_funct_1 @ sk_B_1)) | 
% 0.23/0.51       (![X11 : $i, X12 : $i]:
% 0.23/0.51          (((X12) = (X11))
% 0.23/0.51           | ((k1_funct_1 @ sk_B_1 @ X12) != (k1_funct_1 @ sk_B_1 @ X11))
% 0.23/0.51           | ~ (r2_hidden @ X11 @ sk_A)
% 0.23/0.51           | ~ (r2_hidden @ X12 @ sk_A)))),
% 0.23/0.51      inference('split', [status(esa)], ['2'])).
% 0.23/0.51  thf('24', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.23/0.51      inference('demod', [status(thm)], ['6', '7', '8', '11'])).
% 0.23/0.51  thf('25', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((r2_hidden @ (sk_C @ X0) @ (k1_relat_1 @ X0))
% 0.23/0.51          | (v2_funct_1 @ X0)
% 0.23/0.51          | ~ (v1_funct_1 @ X0)
% 0.23/0.51          | ~ (v1_relat_1 @ X0))),
% 0.23/0.51      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.23/0.51  thf('26', plain,
% 0.23/0.51      (((r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.23/0.51        | ~ (v1_relat_1 @ sk_B_1)
% 0.23/0.51        | ~ (v1_funct_1 @ sk_B_1)
% 0.23/0.51        | (v2_funct_1 @ sk_B_1))),
% 0.23/0.51      inference('sup+', [status(thm)], ['24', '25'])).
% 0.23/0.51  thf('27', plain, ((v1_relat_1 @ sk_B_1)),
% 0.23/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.51  thf('28', plain, ((v1_funct_1 @ sk_B_1)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('29', plain,
% 0.23/0.51      (((r2_hidden @ (sk_C @ sk_B_1) @ sk_A) | (v2_funct_1 @ sk_B_1))),
% 0.23/0.51      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.23/0.51  thf('30', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (((k1_funct_1 @ X0 @ (sk_B @ X0)) = (k1_funct_1 @ X0 @ (sk_C @ X0)))
% 0.23/0.51          | (v2_funct_1 @ X0)
% 0.23/0.51          | ~ (v1_funct_1 @ X0)
% 0.23/0.51          | ~ (v1_relat_1 @ X0))),
% 0.23/0.51      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.23/0.51  thf('31', plain,
% 0.23/0.51      ((![X11 : $i, X12 : $i]:
% 0.23/0.51          (((X12) = (X11))
% 0.23/0.51           | ((k1_funct_1 @ sk_B_1 @ X12) != (k1_funct_1 @ sk_B_1 @ X11))
% 0.23/0.51           | ~ (r2_hidden @ X11 @ sk_A)
% 0.23/0.51           | ~ (r2_hidden @ X12 @ sk_A)))
% 0.23/0.51         <= ((![X11 : $i, X12 : $i]:
% 0.23/0.51                (((X12) = (X11))
% 0.23/0.51                 | ((k1_funct_1 @ sk_B_1 @ X12) != (k1_funct_1 @ sk_B_1 @ X11))
% 0.23/0.51                 | ~ (r2_hidden @ X11 @ sk_A)
% 0.23/0.51                 | ~ (r2_hidden @ X12 @ sk_A))))),
% 0.23/0.51      inference('split', [status(esa)], ['2'])).
% 0.23/0.51  thf('32', plain,
% 0.23/0.51      ((![X0 : $i]:
% 0.23/0.51          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.23/0.51             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.23/0.51           | ~ (v1_relat_1 @ sk_B_1)
% 0.23/0.51           | ~ (v1_funct_1 @ sk_B_1)
% 0.23/0.51           | (v2_funct_1 @ sk_B_1)
% 0.23/0.51           | ~ (r2_hidden @ X0 @ sk_A)
% 0.23/0.51           | ~ (r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.23/0.51           | ((X0) = (sk_C @ sk_B_1))))
% 0.23/0.51         <= ((![X11 : $i, X12 : $i]:
% 0.23/0.51                (((X12) = (X11))
% 0.23/0.51                 | ((k1_funct_1 @ sk_B_1 @ X12) != (k1_funct_1 @ sk_B_1 @ X11))
% 0.23/0.51                 | ~ (r2_hidden @ X11 @ sk_A)
% 0.23/0.51                 | ~ (r2_hidden @ X12 @ sk_A))))),
% 0.23/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.23/0.51  thf('33', plain, ((v1_relat_1 @ sk_B_1)),
% 0.23/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.51  thf('34', plain, ((v1_funct_1 @ sk_B_1)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('35', plain,
% 0.23/0.51      ((![X0 : $i]:
% 0.23/0.51          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.23/0.51             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.23/0.51           | (v2_funct_1 @ sk_B_1)
% 0.23/0.51           | ~ (r2_hidden @ X0 @ sk_A)
% 0.23/0.51           | ~ (r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.23/0.51           | ((X0) = (sk_C @ sk_B_1))))
% 0.23/0.51         <= ((![X11 : $i, X12 : $i]:
% 0.23/0.51                (((X12) = (X11))
% 0.23/0.51                 | ((k1_funct_1 @ sk_B_1 @ X12) != (k1_funct_1 @ sk_B_1 @ X11))
% 0.23/0.51                 | ~ (r2_hidden @ X11 @ sk_A)
% 0.23/0.51                 | ~ (r2_hidden @ X12 @ sk_A))))),
% 0.23/0.51      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.23/0.51  thf('36', plain,
% 0.23/0.51      ((![X0 : $i]:
% 0.23/0.51          ((v2_funct_1 @ sk_B_1)
% 0.23/0.51           | ((X0) = (sk_C @ sk_B_1))
% 0.23/0.51           | ~ (r2_hidden @ X0 @ sk_A)
% 0.23/0.51           | (v2_funct_1 @ sk_B_1)
% 0.23/0.51           | ((k1_funct_1 @ sk_B_1 @ X0)
% 0.23/0.51               != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 0.23/0.51         <= ((![X11 : $i, X12 : $i]:
% 0.23/0.51                (((X12) = (X11))
% 0.23/0.51                 | ((k1_funct_1 @ sk_B_1 @ X12) != (k1_funct_1 @ sk_B_1 @ X11))
% 0.23/0.51                 | ~ (r2_hidden @ X11 @ sk_A)
% 0.23/0.51                 | ~ (r2_hidden @ X12 @ sk_A))))),
% 0.23/0.51      inference('sup-', [status(thm)], ['29', '35'])).
% 0.23/0.51  thf('37', plain,
% 0.23/0.51      ((![X0 : $i]:
% 0.23/0.51          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.23/0.51             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.23/0.51           | ~ (r2_hidden @ X0 @ sk_A)
% 0.23/0.51           | ((X0) = (sk_C @ sk_B_1))
% 0.23/0.51           | (v2_funct_1 @ sk_B_1)))
% 0.23/0.51         <= ((![X11 : $i, X12 : $i]:
% 0.23/0.51                (((X12) = (X11))
% 0.23/0.51                 | ((k1_funct_1 @ sk_B_1 @ X12) != (k1_funct_1 @ sk_B_1 @ X11))
% 0.23/0.51                 | ~ (r2_hidden @ X11 @ sk_A)
% 0.23/0.51                 | ~ (r2_hidden @ X12 @ sk_A))))),
% 0.23/0.51      inference('simplify', [status(thm)], ['36'])).
% 0.23/0.51  thf('38', plain,
% 0.23/0.51      ((((v2_funct_1 @ sk_B_1)
% 0.23/0.51         | ((sk_B @ sk_B_1) = (sk_C @ sk_B_1))
% 0.23/0.51         | ~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_A)))
% 0.23/0.51         <= ((![X11 : $i, X12 : $i]:
% 0.23/0.51                (((X12) = (X11))
% 0.23/0.51                 | ((k1_funct_1 @ sk_B_1 @ X12) != (k1_funct_1 @ sk_B_1 @ X11))
% 0.23/0.51                 | ~ (r2_hidden @ X11 @ sk_A)
% 0.23/0.51                 | ~ (r2_hidden @ X12 @ sk_A))))),
% 0.23/0.51      inference('eq_res', [status(thm)], ['37'])).
% 0.23/0.51  thf('39', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.23/0.51      inference('demod', [status(thm)], ['6', '7', '8', '11'])).
% 0.23/0.51  thf('40', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((r2_hidden @ (sk_B @ X0) @ (k1_relat_1 @ X0))
% 0.23/0.51          | (v2_funct_1 @ X0)
% 0.23/0.51          | ~ (v1_funct_1 @ X0)
% 0.23/0.51          | ~ (v1_relat_1 @ X0))),
% 0.23/0.51      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.23/0.51  thf('41', plain,
% 0.23/0.51      (((r2_hidden @ (sk_B @ sk_B_1) @ sk_A)
% 0.23/0.51        | ~ (v1_relat_1 @ sk_B_1)
% 0.23/0.51        | ~ (v1_funct_1 @ sk_B_1)
% 0.23/0.51        | (v2_funct_1 @ sk_B_1))),
% 0.23/0.51      inference('sup+', [status(thm)], ['39', '40'])).
% 0.23/0.51  thf('42', plain, ((v1_relat_1 @ sk_B_1)),
% 0.23/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.51  thf('43', plain, ((v1_funct_1 @ sk_B_1)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('44', plain,
% 0.23/0.51      (((r2_hidden @ (sk_B @ sk_B_1) @ sk_A) | (v2_funct_1 @ sk_B_1))),
% 0.23/0.51      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.23/0.51  thf('45', plain,
% 0.23/0.51      (((((sk_B @ sk_B_1) = (sk_C @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.23/0.51         <= ((![X11 : $i, X12 : $i]:
% 0.23/0.51                (((X12) = (X11))
% 0.23/0.51                 | ((k1_funct_1 @ sk_B_1 @ X12) != (k1_funct_1 @ sk_B_1 @ X11))
% 0.23/0.51                 | ~ (r2_hidden @ X11 @ sk_A)
% 0.23/0.51                 | ~ (r2_hidden @ X12 @ sk_A))))),
% 0.23/0.51      inference('clc', [status(thm)], ['38', '44'])).
% 0.23/0.51  thf('46', plain, (((r2_hidden @ sk_C_1 @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('47', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.23/0.51      inference('split', [status(esa)], ['46'])).
% 0.23/0.51  thf('48', plain,
% 0.23/0.51      ((((sk_B @ sk_B_1) = (sk_C @ sk_B_1)))
% 0.23/0.51         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.23/0.51             (![X11 : $i, X12 : $i]:
% 0.23/0.51                (((X12) = (X11))
% 0.23/0.51                 | ((k1_funct_1 @ sk_B_1 @ X12) != (k1_funct_1 @ sk_B_1 @ X11))
% 0.23/0.51                 | ~ (r2_hidden @ X11 @ sk_A)
% 0.23/0.51                 | ~ (r2_hidden @ X12 @ sk_A))))),
% 0.23/0.51      inference('sup-', [status(thm)], ['45', '47'])).
% 0.23/0.51  thf('49', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (((sk_B @ X0) != (sk_C @ X0))
% 0.23/0.51          | (v2_funct_1 @ X0)
% 0.23/0.51          | ~ (v1_funct_1 @ X0)
% 0.23/0.51          | ~ (v1_relat_1 @ X0))),
% 0.23/0.51      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.23/0.51  thf('50', plain,
% 0.23/0.51      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1))
% 0.23/0.51         | ~ (v1_relat_1 @ sk_B_1)
% 0.23/0.51         | ~ (v1_funct_1 @ sk_B_1)
% 0.23/0.51         | (v2_funct_1 @ sk_B_1)))
% 0.23/0.51         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.23/0.51             (![X11 : $i, X12 : $i]:
% 0.23/0.51                (((X12) = (X11))
% 0.23/0.51                 | ((k1_funct_1 @ sk_B_1 @ X12) != (k1_funct_1 @ sk_B_1 @ X11))
% 0.23/0.51                 | ~ (r2_hidden @ X11 @ sk_A)
% 0.23/0.51                 | ~ (r2_hidden @ X12 @ sk_A))))),
% 0.23/0.51      inference('sup-', [status(thm)], ['48', '49'])).
% 0.23/0.51  thf('51', plain, ((v1_relat_1 @ sk_B_1)),
% 0.23/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.51  thf('52', plain, ((v1_funct_1 @ sk_B_1)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('53', plain,
% 0.23/0.51      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.23/0.51         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.23/0.51             (![X11 : $i, X12 : $i]:
% 0.23/0.51                (((X12) = (X11))
% 0.23/0.51                 | ((k1_funct_1 @ sk_B_1 @ X12) != (k1_funct_1 @ sk_B_1 @ X11))
% 0.23/0.51                 | ~ (r2_hidden @ X11 @ sk_A)
% 0.23/0.51                 | ~ (r2_hidden @ X12 @ sk_A))))),
% 0.23/0.51      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.23/0.51  thf('54', plain,
% 0.23/0.51      (((v2_funct_1 @ sk_B_1))
% 0.23/0.51         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.23/0.51             (![X11 : $i, X12 : $i]:
% 0.23/0.51                (((X12) = (X11))
% 0.23/0.51                 | ((k1_funct_1 @ sk_B_1 @ X12) != (k1_funct_1 @ sk_B_1 @ X11))
% 0.23/0.51                 | ~ (r2_hidden @ X11 @ sk_A)
% 0.23/0.51                 | ~ (r2_hidden @ X12 @ sk_A))))),
% 0.23/0.51      inference('simplify', [status(thm)], ['53'])).
% 0.23/0.51  thf('55', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.23/0.51      inference('split', [status(esa)], ['46'])).
% 0.23/0.51  thf('56', plain,
% 0.23/0.51      (~
% 0.23/0.51       (![X11 : $i, X12 : $i]:
% 0.23/0.51          (((X12) = (X11))
% 0.23/0.51           | ((k1_funct_1 @ sk_B_1 @ X12) != (k1_funct_1 @ sk_B_1 @ X11))
% 0.23/0.51           | ~ (r2_hidden @ X11 @ sk_A)
% 0.23/0.51           | ~ (r2_hidden @ X12 @ sk_A))) | 
% 0.23/0.51       ((v2_funct_1 @ sk_B_1))),
% 0.23/0.51      inference('sup-', [status(thm)], ['54', '55'])).
% 0.23/0.51  thf('57', plain, (((v2_funct_1 @ sk_B_1))),
% 0.23/0.51      inference('sat_resolution*', [status(thm)], ['23', '56'])).
% 0.23/0.51  thf('58', plain,
% 0.23/0.51      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))) | 
% 0.23/0.51       ~ ((v2_funct_1 @ sk_B_1))),
% 0.23/0.51      inference('split', [status(esa)], ['0'])).
% 0.23/0.51  thf('59', plain,
% 0.23/0.51      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D)))),
% 0.23/0.51      inference('sat_resolution*', [status(thm)], ['23', '56', '58'])).
% 0.23/0.51  thf('60', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (((k1_funct_1 @ sk_B_1 @ sk_C_1) != (k1_funct_1 @ sk_B_1 @ X0))
% 0.23/0.51          | ~ (r2_hidden @ sk_D @ sk_A)
% 0.23/0.51          | ((sk_D) = (X0))
% 0.23/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.23/0.51      inference('simpl_trail', [status(thm)], ['22', '57', '59'])).
% 0.23/0.51  thf('61', plain, (((r2_hidden @ sk_D @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('62', plain,
% 0.23/0.51      (((r2_hidden @ sk_D @ sk_A)) <= (((r2_hidden @ sk_D @ sk_A)))),
% 0.23/0.51      inference('split', [status(esa)], ['61'])).
% 0.23/0.51  thf('63', plain, (((r2_hidden @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.23/0.51      inference('split', [status(esa)], ['61'])).
% 0.23/0.51  thf('64', plain, (((r2_hidden @ sk_D @ sk_A))),
% 0.23/0.51      inference('sat_resolution*', [status(thm)], ['23', '56', '63'])).
% 0.23/0.51  thf('65', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.23/0.51      inference('simpl_trail', [status(thm)], ['62', '64'])).
% 0.23/0.51  thf('66', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (((k1_funct_1 @ sk_B_1 @ sk_C_1) != (k1_funct_1 @ sk_B_1 @ X0))
% 0.23/0.51          | ((sk_D) = (X0))
% 0.23/0.51          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.23/0.51      inference('demod', [status(thm)], ['60', '65'])).
% 0.23/0.51  thf('67', plain, ((~ (r2_hidden @ sk_C_1 @ sk_A) | ((sk_D) = (sk_C_1)))),
% 0.23/0.51      inference('eq_res', [status(thm)], ['66'])).
% 0.23/0.51  thf('68', plain,
% 0.23/0.51      (((r2_hidden @ sk_C_1 @ sk_A)) <= (((r2_hidden @ sk_C_1 @ sk_A)))),
% 0.23/0.51      inference('split', [status(esa)], ['46'])).
% 0.23/0.51  thf('69', plain, (((r2_hidden @ sk_C_1 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.23/0.51      inference('split', [status(esa)], ['46'])).
% 0.23/0.51  thf('70', plain, (((r2_hidden @ sk_C_1 @ sk_A))),
% 0.23/0.51      inference('sat_resolution*', [status(thm)], ['23', '56', '69'])).
% 0.23/0.51  thf('71', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.23/0.51      inference('simpl_trail', [status(thm)], ['68', '70'])).
% 0.23/0.51  thf('72', plain, (((sk_D) = (sk_C_1))),
% 0.23/0.51      inference('demod', [status(thm)], ['67', '71'])).
% 0.23/0.51  thf('73', plain, ((((sk_C_1) != (sk_D)) | ~ (v2_funct_1 @ sk_B_1))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('74', plain, ((((sk_C_1) != (sk_D))) <= (~ (((sk_C_1) = (sk_D))))),
% 0.23/0.51      inference('split', [status(esa)], ['73'])).
% 0.23/0.51  thf('75', plain, (~ (((sk_C_1) = (sk_D))) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.23/0.51      inference('split', [status(esa)], ['73'])).
% 0.23/0.51  thf('76', plain, (~ (((sk_C_1) = (sk_D)))),
% 0.23/0.51      inference('sat_resolution*', [status(thm)], ['23', '56', '75'])).
% 0.23/0.51  thf('77', plain, (((sk_C_1) != (sk_D))),
% 0.23/0.51      inference('simpl_trail', [status(thm)], ['74', '76'])).
% 0.23/0.51  thf('78', plain, ($false),
% 0.23/0.51      inference('simplify_reflect-', [status(thm)], ['72', '77'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
