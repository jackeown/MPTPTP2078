%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1016+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qpsFNQKZN5

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:53 EST 2020

% Result     : Theorem 0.15s
% Output     : Refutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 684 expanded)
%              Number of leaves         :   22 ( 202 expanded)
%              Depth                    :   21
%              Number of atoms          :  966 (12201 expanded)
%              Number of equality atoms :   89 ( 869 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k1_relat_1 @ X3 ) )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X3 ) )
      | ( ( k1_funct_1 @ X3 @ X4 )
       != ( k1_funct_1 @ X3 @ X5 ) )
      | ( X4 = X5 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
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
    ! [X3: $i] :
      ( ( r2_hidden @ ( sk_C @ X3 ) @ ( k1_relat_1 @ X3 ) )
      | ( v2_funct_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
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
    ! [X3: $i] :
      ( ( ( k1_funct_1 @ X3 @ ( sk_B @ X3 ) )
        = ( k1_funct_1 @ X3 @ ( sk_C @ X3 ) ) )
      | ( v2_funct_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
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
    ! [X3: $i] :
      ( ( r2_hidden @ ( sk_B @ X3 ) @ ( k1_relat_1 @ X3 ) )
      | ( v2_funct_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
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
    ! [X3: $i] :
      ( ( ( sk_B @ X3 )
       != ( sk_C @ X3 ) )
      | ( v2_funct_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
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
