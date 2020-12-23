%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2WhEMqX9Hh

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 747 expanded)
%              Number of leaves         :   23 ( 223 expanded)
%              Depth                    :   21
%              Number of atoms          :  980 (12495 expanded)
%              Number of equality atoms :   89 ( 869 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X12: $i,X13: $i] :
      ( ( X13 = X12 )
      | ( ( k1_funct_1 @ sk_B_1 @ X13 )
       != ( k1_funct_1 @ sk_B_1 @ X12 ) )
      | ~ ( r2_hidden @ X12 @ sk_A )
      | ~ ( r2_hidden @ X13 @ sk_A )
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
    ! [X10: $i,X11: $i] :
      ( ( ( k1_relset_1 @ X10 @ X10 @ X11 )
        = X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X10 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X10 @ X10 )
      | ~ ( v1_funct_1 @ X11 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ~ ( r2_hidden @ X5 @ ( k1_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X4 ) )
      | ( ( k1_funct_1 @ X4 @ X5 )
       != ( k1_funct_1 @ X4 @ X6 ) )
      | ( X5 = X6 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('19',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['6','7','8','11'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ sk_A )
      | ~ ( v2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['14','19','20','21'])).

thf('23',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ( ( k1_funct_1 @ sk_B_1 @ X1 )
         != ( k1_funct_1 @ sk_B_1 @ X0 ) )
        | ( X1 = X0 )
        | ~ ( r2_hidden @ X1 @ sk_A ) )
   <= ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
         != ( k1_funct_1 @ sk_B_1 @ X0 ) )
        | ~ ( r2_hidden @ sk_D @ sk_A )
        | ( sk_D = X0 )
        | ~ ( r2_hidden @ X0 @ sk_A ) )
   <= ( ( v2_funct_1 @ sk_B_1 )
      & ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
        = ( k1_funct_1 @ sk_B_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['1','23'])).

thf('25',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ! [X12: $i,X13: $i] :
        ( ( X13 = X12 )
        | ( ( k1_funct_1 @ sk_B_1 @ X13 )
         != ( k1_funct_1 @ sk_B_1 @ X12 ) )
        | ~ ( r2_hidden @ X12 @ sk_A )
        | ~ ( r2_hidden @ X13 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('26',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['6','7','8','11'])).

thf('27',plain,(
    ! [X4: $i] :
      ( ( r2_hidden @ ( sk_C @ X4 ) @ ( k1_relat_1 @ X4 ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('30',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X4: $i] :
      ( ( ( k1_funct_1 @ X4 @ ( sk_B @ X4 ) )
        = ( k1_funct_1 @ X4 @ ( sk_C @ X4 ) ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('33',plain,
    ( ! [X12: $i,X13: $i] :
        ( ( X13 = X12 )
        | ( ( k1_funct_1 @ sk_B_1 @ X13 )
         != ( k1_funct_1 @ sk_B_1 @ X12 ) )
        | ~ ( r2_hidden @ X12 @ sk_A )
        | ~ ( r2_hidden @ X13 @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( X13 = X12 )
        | ( ( k1_funct_1 @ sk_B_1 @ X13 )
         != ( k1_funct_1 @ sk_B_1 @ X12 ) )
        | ~ ( r2_hidden @ X12 @ sk_A )
        | ~ ( r2_hidden @ X13 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('34',plain,
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
   <= ! [X12: $i,X13: $i] :
        ( ( X13 = X12 )
        | ( ( k1_funct_1 @ sk_B_1 @ X13 )
         != ( k1_funct_1 @ sk_B_1 @ X12 ) )
        | ~ ( r2_hidden @ X12 @ sk_A )
        | ~ ( r2_hidden @ X13 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('36',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ( v2_funct_1 @ sk_B_1 )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ ( sk_C @ sk_B_1 ) @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_1 ) ) )
   <= ! [X12: $i,X13: $i] :
        ( ( X13 = X12 )
        | ( ( k1_funct_1 @ sk_B_1 @ X13 )
         != ( k1_funct_1 @ sk_B_1 @ X12 ) )
        | ~ ( r2_hidden @ X12 @ sk_A )
        | ~ ( r2_hidden @ X13 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( v2_funct_1 @ sk_B_1 )
        | ( X0
          = ( sk_C @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( v2_funct_1 @ sk_B_1 )
        | ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) ) )
   <= ! [X12: $i,X13: $i] :
        ( ( X13 = X12 )
        | ( ( k1_funct_1 @ sk_B_1 @ X13 )
         != ( k1_funct_1 @ sk_B_1 @ X12 ) )
        | ~ ( r2_hidden @ X12 @ sk_A )
        | ~ ( r2_hidden @ X13 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ X0 )
         != ( k1_funct_1 @ sk_B_1 @ ( sk_B @ sk_B_1 ) ) )
        | ~ ( r2_hidden @ X0 @ sk_A )
        | ( X0
          = ( sk_C @ sk_B_1 ) )
        | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X12: $i,X13: $i] :
        ( ( X13 = X12 )
        | ( ( k1_funct_1 @ sk_B_1 @ X13 )
         != ( k1_funct_1 @ sk_B_1 @ X12 ) )
        | ~ ( r2_hidden @ X12 @ sk_A )
        | ~ ( r2_hidden @ X13 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( v2_funct_1 @ sk_B_1 )
      | ( ( sk_B @ sk_B_1 )
        = ( sk_C @ sk_B_1 ) )
      | ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A ) )
   <= ! [X12: $i,X13: $i] :
        ( ( X13 = X12 )
        | ( ( k1_funct_1 @ sk_B_1 @ X13 )
         != ( k1_funct_1 @ sk_B_1 @ X12 ) )
        | ~ ( r2_hidden @ X12 @ sk_A )
        | ~ ( r2_hidden @ X13 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['39'])).

thf('41',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['6','7','8','11'])).

thf('42',plain,(
    ! [X4: $i] :
      ( ( r2_hidden @ ( sk_B @ X4 ) @ ( k1_relat_1 @ X4 ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('43',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('45',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_A )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( ( ( sk_B @ sk_B_1 )
        = ( sk_C @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ! [X12: $i,X13: $i] :
        ( ( X13 = X12 )
        | ( ( k1_funct_1 @ sk_B_1 @ X13 )
         != ( k1_funct_1 @ sk_B_1 @ X12 ) )
        | ~ ( r2_hidden @ X12 @ sk_A )
        | ~ ( r2_hidden @ X13 @ sk_A ) ) ),
    inference(clc,[status(thm)],['40','46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,
    ( ( ( sk_B @ sk_B_1 )
      = ( sk_C @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X12: $i,X13: $i] :
          ( ( X13 = X12 )
          | ( ( k1_funct_1 @ sk_B_1 @ X13 )
           != ( k1_funct_1 @ sk_B_1 @ X12 ) )
          | ~ ( r2_hidden @ X12 @ sk_A )
          | ~ ( r2_hidden @ X13 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X4: $i] :
      ( ( ( sk_B @ X4 )
       != ( sk_C @ X4 ) )
      | ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('52',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X12: $i,X13: $i] :
          ( ( X13 = X12 )
          | ( ( k1_funct_1 @ sk_B_1 @ X13 )
           != ( k1_funct_1 @ sk_B_1 @ X12 ) )
          | ~ ( r2_hidden @ X12 @ sk_A )
          | ~ ( r2_hidden @ X13 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('54',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( ( sk_B @ sk_B_1 )
       != ( sk_B @ sk_B_1 ) )
      | ( v2_funct_1 @ sk_B_1 ) )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X12: $i,X13: $i] :
          ( ( X13 = X12 )
          | ( ( k1_funct_1 @ sk_B_1 @ X13 )
           != ( k1_funct_1 @ sk_B_1 @ X12 ) )
          | ~ ( r2_hidden @ X12 @ sk_A )
          | ~ ( r2_hidden @ X13 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ( v2_funct_1 @ sk_B_1 )
   <= ( ~ ( v2_funct_1 @ sk_B_1 )
      & ! [X12: $i,X13: $i] :
          ( ( X13 = X12 )
          | ( ( k1_funct_1 @ sk_B_1 @ X13 )
           != ( k1_funct_1 @ sk_B_1 @ X12 ) )
          | ~ ( r2_hidden @ X12 @ sk_A )
          | ~ ( r2_hidden @ X13 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ~ ( v2_funct_1 @ sk_B_1 )
   <= ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['48'])).

thf('58',plain,
    ( ~ ! [X12: $i,X13: $i] :
          ( ( X13 = X12 )
          | ( ( k1_funct_1 @ sk_B_1 @ X13 )
           != ( k1_funct_1 @ sk_B_1 @ X12 ) )
          | ~ ( r2_hidden @ X12 @ sk_A )
          | ~ ( r2_hidden @ X13 @ sk_A ) )
    | ( v2_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['25','58'])).

thf('60',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
      = ( k1_funct_1 @ sk_B_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['25','58','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ sk_D @ sk_A )
      | ( sk_D = X0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['24','59','61'])).

thf('63',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
   <= ( r2_hidden @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['63'])).

thf('65',plain,
    ( ( r2_hidden @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['63'])).

thf('66',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['25','58','65'])).

thf('67',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['64','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ( sk_D = X0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['62','67'])).

thf('69',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_A )
    | ( sk_D = sk_C_1 ) ),
    inference(eq_res,[status(thm)],['68'])).

thf('70',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
   <= ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['48'])).

thf('71',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['48'])).

thf('72',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['25','58','71'])).

thf('73',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['70','72'])).

thf('74',plain,(
    sk_D = sk_C_1 ),
    inference(demod,[status(thm)],['69','73'])).

thf('75',plain,
    ( ( sk_C_1 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( sk_C_1 != sk_D )
   <= ( sk_C_1 != sk_D ) ),
    inference(split,[status(esa)],['75'])).

thf('77',plain,
    ( ( sk_C_1 != sk_D )
    | ~ ( v2_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['75'])).

thf('78',plain,(
    sk_C_1 != sk_D ),
    inference('sat_resolution*',[status(thm)],['25','58','77'])).

thf('79',plain,(
    sk_C_1 != sk_D ),
    inference(simpl_trail,[status(thm)],['76','78'])).

thf('80',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['74','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2WhEMqX9Hh
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:37:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 61 iterations in 0.033s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.47  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i > $i).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.47  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.20/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(t77_funct_2, conjecture,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.47         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.47       ( ( v2_funct_1 @ B ) <=>
% 0.20/0.47         ( ![C:$i,D:$i]:
% 0.20/0.47           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.20/0.47               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.20/0.47             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i]:
% 0.20/0.47        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.47            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.47          ( ( v2_funct_1 @ B ) <=>
% 0.20/0.47            ( ![C:$i,D:$i]:
% 0.20/0.47              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.20/0.47                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.20/0.47                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t77_funct_2])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))
% 0.20/0.47        | ~ (v2_funct_1 @ sk_B_1))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D)))
% 0.20/0.47         <= ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X12 : $i, X13 : $i]:
% 0.20/0.47         (((X13) = (X12))
% 0.20/0.47          | ((k1_funct_1 @ sk_B_1 @ X13) != (k1_funct_1 @ sk_B_1 @ X12))
% 0.20/0.47          | ~ (r2_hidden @ X12 @ sk_A)
% 0.20/0.47          | ~ (r2_hidden @ X13 @ sk_A)
% 0.20/0.47          | (v2_funct_1 @ sk_B_1))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('3', plain, (((v2_funct_1 @ sk_B_1)) <= (((v2_funct_1 @ sk_B_1)))),
% 0.20/0.47      inference('split', [status(esa)], ['2'])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t67_funct_2, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.47         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.47       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i]:
% 0.20/0.47         (((k1_relset_1 @ X10 @ X10 @ X11) = (X10))
% 0.20/0.47          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X10)))
% 0.20/0.47          | ~ (v1_funct_2 @ X11 @ X10 @ X10)
% 0.20/0.47          | ~ (v1_funct_1 @ X11))),
% 0.20/0.47      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      ((~ (v1_funct_1 @ sk_B_1)
% 0.20/0.47        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.20/0.47        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('8', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.47       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.47         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.20/0.47          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.20/0.47      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '7', '8', '11'])).
% 0.20/0.47  thf(d8_funct_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.47       ( ( v2_funct_1 @ A ) <=>
% 0.20/0.47         ( ![B:$i,C:$i]:
% 0.20/0.47           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.47               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.47               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.20/0.47             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.47         (~ (v2_funct_1 @ X4)
% 0.20/0.47          | ~ (r2_hidden @ X5 @ (k1_relat_1 @ X4))
% 0.20/0.47          | ~ (r2_hidden @ X6 @ (k1_relat_1 @ X4))
% 0.20/0.47          | ((k1_funct_1 @ X4 @ X5) != (k1_funct_1 @ X4 @ X6))
% 0.20/0.47          | ((X5) = (X6))
% 0.20/0.47          | ~ (v1_funct_1 @ X4)
% 0.20/0.47          | ~ (v1_relat_1 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.47          | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.47          | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.47          | ((X0) = (X1))
% 0.20/0.47          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.20/0.47          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1))
% 0.20/0.47          | ~ (v2_funct_1 @ sk_B_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(cc2_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.47          | (v1_relat_1 @ X0)
% 0.20/0.47          | ~ (v1_relat_1 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf(fc6_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.47  thf('19', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.47      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf('20', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('21', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '7', '8', '11'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.47          | ((X0) = (X1))
% 0.20/0.47          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.20/0.47          | ~ (r2_hidden @ X1 @ sk_A)
% 0.20/0.47          | ~ (v2_funct_1 @ sk_B_1))),
% 0.20/0.47      inference('demod', [status(thm)], ['14', '19', '20', '21'])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      ((![X0 : $i, X1 : $i]:
% 0.20/0.47          (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.47           | ((k1_funct_1 @ sk_B_1 @ X1) != (k1_funct_1 @ sk_B_1 @ X0))
% 0.20/0.47           | ((X1) = (X0))
% 0.20/0.47           | ~ (r2_hidden @ X1 @ sk_A)))
% 0.20/0.47         <= (((v2_funct_1 @ sk_B_1)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '22'])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          (((k1_funct_1 @ sk_B_1 @ sk_C_1) != (k1_funct_1 @ sk_B_1 @ X0))
% 0.20/0.47           | ~ (r2_hidden @ sk_D @ sk_A)
% 0.20/0.47           | ((sk_D) = (X0))
% 0.20/0.47           | ~ (r2_hidden @ X0 @ sk_A)))
% 0.20/0.47         <= (((v2_funct_1 @ sk_B_1)) & 
% 0.20/0.47             (((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '23'])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (((v2_funct_1 @ sk_B_1)) | 
% 0.20/0.47       (![X12 : $i, X13 : $i]:
% 0.20/0.47          (((X13) = (X12))
% 0.20/0.47           | ((k1_funct_1 @ sk_B_1 @ X13) != (k1_funct_1 @ sk_B_1 @ X12))
% 0.20/0.47           | ~ (r2_hidden @ X12 @ sk_A)
% 0.20/0.47           | ~ (r2_hidden @ X13 @ sk_A)))),
% 0.20/0.47      inference('split', [status(esa)], ['2'])).
% 0.20/0.47  thf('26', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '7', '8', '11'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (![X4 : $i]:
% 0.20/0.47         ((r2_hidden @ (sk_C @ X4) @ (k1_relat_1 @ X4))
% 0.20/0.47          | (v2_funct_1 @ X4)
% 0.20/0.47          | ~ (v1_funct_1 @ X4)
% 0.20/0.47          | ~ (v1_relat_1 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (((r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.20/0.47        | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.47        | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.47        | (v2_funct_1 @ sk_B_1))),
% 0.20/0.47      inference('sup+', [status(thm)], ['26', '27'])).
% 0.20/0.47  thf('29', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.47      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf('30', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (((r2_hidden @ (sk_C @ sk_B_1) @ sk_A) | (v2_funct_1 @ sk_B_1))),
% 0.20/0.47      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      (![X4 : $i]:
% 0.20/0.47         (((k1_funct_1 @ X4 @ (sk_B @ X4)) = (k1_funct_1 @ X4 @ (sk_C @ X4)))
% 0.20/0.47          | (v2_funct_1 @ X4)
% 0.20/0.47          | ~ (v1_funct_1 @ X4)
% 0.20/0.47          | ~ (v1_relat_1 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      ((![X12 : $i, X13 : $i]:
% 0.20/0.47          (((X13) = (X12))
% 0.20/0.47           | ((k1_funct_1 @ sk_B_1 @ X13) != (k1_funct_1 @ sk_B_1 @ X12))
% 0.20/0.47           | ~ (r2_hidden @ X12 @ sk_A)
% 0.20/0.47           | ~ (r2_hidden @ X13 @ sk_A)))
% 0.20/0.47         <= ((![X12 : $i, X13 : $i]:
% 0.20/0.47                (((X13) = (X12))
% 0.20/0.47                 | ((k1_funct_1 @ sk_B_1 @ X13) != (k1_funct_1 @ sk_B_1 @ X12))
% 0.20/0.47                 | ~ (r2_hidden @ X12 @ sk_A)
% 0.20/0.47                 | ~ (r2_hidden @ X13 @ sk_A))))),
% 0.20/0.47      inference('split', [status(esa)], ['2'])).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.20/0.47             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.20/0.47           | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.47           | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.47           | (v2_funct_1 @ sk_B_1)
% 0.20/0.47           | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.47           | ~ (r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.20/0.47           | ((X0) = (sk_C @ sk_B_1))))
% 0.20/0.47         <= ((![X12 : $i, X13 : $i]:
% 0.20/0.47                (((X13) = (X12))
% 0.20/0.47                 | ((k1_funct_1 @ sk_B_1 @ X13) != (k1_funct_1 @ sk_B_1 @ X12))
% 0.20/0.47                 | ~ (r2_hidden @ X12 @ sk_A)
% 0.20/0.47                 | ~ (r2_hidden @ X13 @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.47  thf('35', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.47      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf('36', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.20/0.47             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.20/0.47           | (v2_funct_1 @ sk_B_1)
% 0.20/0.47           | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.47           | ~ (r2_hidden @ (sk_C @ sk_B_1) @ sk_A)
% 0.20/0.47           | ((X0) = (sk_C @ sk_B_1))))
% 0.20/0.47         <= ((![X12 : $i, X13 : $i]:
% 0.20/0.47                (((X13) = (X12))
% 0.20/0.47                 | ((k1_funct_1 @ sk_B_1 @ X13) != (k1_funct_1 @ sk_B_1 @ X12))
% 0.20/0.47                 | ~ (r2_hidden @ X12 @ sk_A)
% 0.20/0.47                 | ~ (r2_hidden @ X13 @ sk_A))))),
% 0.20/0.47      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          ((v2_funct_1 @ sk_B_1)
% 0.20/0.47           | ((X0) = (sk_C @ sk_B_1))
% 0.20/0.47           | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.47           | (v2_funct_1 @ sk_B_1)
% 0.20/0.47           | ((k1_funct_1 @ sk_B_1 @ X0)
% 0.20/0.47               != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))))
% 0.20/0.47         <= ((![X12 : $i, X13 : $i]:
% 0.20/0.47                (((X13) = (X12))
% 0.20/0.47                 | ((k1_funct_1 @ sk_B_1 @ X13) != (k1_funct_1 @ sk_B_1 @ X12))
% 0.20/0.47                 | ~ (r2_hidden @ X12 @ sk_A)
% 0.20/0.47                 | ~ (r2_hidden @ X13 @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['31', '37'])).
% 0.20/0.47  thf('39', plain,
% 0.20/0.47      ((![X0 : $i]:
% 0.20/0.47          (((k1_funct_1 @ sk_B_1 @ X0)
% 0.20/0.47             != (k1_funct_1 @ sk_B_1 @ (sk_B @ sk_B_1)))
% 0.20/0.47           | ~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.47           | ((X0) = (sk_C @ sk_B_1))
% 0.20/0.47           | (v2_funct_1 @ sk_B_1)))
% 0.20/0.47         <= ((![X12 : $i, X13 : $i]:
% 0.20/0.47                (((X13) = (X12))
% 0.20/0.47                 | ((k1_funct_1 @ sk_B_1 @ X13) != (k1_funct_1 @ sk_B_1 @ X12))
% 0.20/0.47                 | ~ (r2_hidden @ X12 @ sk_A)
% 0.20/0.47                 | ~ (r2_hidden @ X13 @ sk_A))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['38'])).
% 0.20/0.47  thf('40', plain,
% 0.20/0.47      ((((v2_funct_1 @ sk_B_1)
% 0.20/0.47         | ((sk_B @ sk_B_1) = (sk_C @ sk_B_1))
% 0.20/0.47         | ~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_A)))
% 0.20/0.47         <= ((![X12 : $i, X13 : $i]:
% 0.20/0.47                (((X13) = (X12))
% 0.20/0.47                 | ((k1_funct_1 @ sk_B_1 @ X13) != (k1_funct_1 @ sk_B_1 @ X12))
% 0.20/0.47                 | ~ (r2_hidden @ X12 @ sk_A)
% 0.20/0.47                 | ~ (r2_hidden @ X13 @ sk_A))))),
% 0.20/0.47      inference('eq_res', [status(thm)], ['39'])).
% 0.20/0.47  thf('41', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '7', '8', '11'])).
% 0.20/0.47  thf('42', plain,
% 0.20/0.47      (![X4 : $i]:
% 0.20/0.47         ((r2_hidden @ (sk_B @ X4) @ (k1_relat_1 @ X4))
% 0.20/0.47          | (v2_funct_1 @ X4)
% 0.20/0.47          | ~ (v1_funct_1 @ X4)
% 0.20/0.47          | ~ (v1_relat_1 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.47  thf('43', plain,
% 0.20/0.47      (((r2_hidden @ (sk_B @ sk_B_1) @ sk_A)
% 0.20/0.47        | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.47        | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.47        | (v2_funct_1 @ sk_B_1))),
% 0.20/0.47      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.47  thf('44', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.47      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf('45', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('46', plain,
% 0.20/0.47      (((r2_hidden @ (sk_B @ sk_B_1) @ sk_A) | (v2_funct_1 @ sk_B_1))),
% 0.20/0.47      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.20/0.47  thf('47', plain,
% 0.20/0.47      (((((sk_B @ sk_B_1) = (sk_C @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.20/0.47         <= ((![X12 : $i, X13 : $i]:
% 0.20/0.47                (((X13) = (X12))
% 0.20/0.47                 | ((k1_funct_1 @ sk_B_1 @ X13) != (k1_funct_1 @ sk_B_1 @ X12))
% 0.20/0.47                 | ~ (r2_hidden @ X12 @ sk_A)
% 0.20/0.47                 | ~ (r2_hidden @ X13 @ sk_A))))),
% 0.20/0.47      inference('clc', [status(thm)], ['40', '46'])).
% 0.20/0.47  thf('48', plain, (((r2_hidden @ sk_C_1 @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('49', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.20/0.47      inference('split', [status(esa)], ['48'])).
% 0.20/0.47  thf('50', plain,
% 0.20/0.47      ((((sk_B @ sk_B_1) = (sk_C @ sk_B_1)))
% 0.20/0.47         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.20/0.47             (![X12 : $i, X13 : $i]:
% 0.20/0.47                (((X13) = (X12))
% 0.20/0.47                 | ((k1_funct_1 @ sk_B_1 @ X13) != (k1_funct_1 @ sk_B_1 @ X12))
% 0.20/0.47                 | ~ (r2_hidden @ X12 @ sk_A)
% 0.20/0.47                 | ~ (r2_hidden @ X13 @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['47', '49'])).
% 0.20/0.47  thf('51', plain,
% 0.20/0.47      (![X4 : $i]:
% 0.20/0.47         (((sk_B @ X4) != (sk_C @ X4))
% 0.20/0.47          | (v2_funct_1 @ X4)
% 0.20/0.47          | ~ (v1_funct_1 @ X4)
% 0.20/0.47          | ~ (v1_relat_1 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.20/0.47  thf('52', plain,
% 0.20/0.47      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1))
% 0.20/0.47         | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.47         | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.47         | (v2_funct_1 @ sk_B_1)))
% 0.20/0.47         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.20/0.47             (![X12 : $i, X13 : $i]:
% 0.20/0.47                (((X13) = (X12))
% 0.20/0.47                 | ((k1_funct_1 @ sk_B_1 @ X13) != (k1_funct_1 @ sk_B_1 @ X12))
% 0.20/0.47                 | ~ (r2_hidden @ X12 @ sk_A)
% 0.20/0.47                 | ~ (r2_hidden @ X13 @ sk_A))))),
% 0.20/0.47      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.47  thf('53', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.47      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf('54', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('55', plain,
% 0.20/0.47      (((((sk_B @ sk_B_1) != (sk_B @ sk_B_1)) | (v2_funct_1 @ sk_B_1)))
% 0.20/0.47         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.20/0.47             (![X12 : $i, X13 : $i]:
% 0.20/0.47                (((X13) = (X12))
% 0.20/0.47                 | ((k1_funct_1 @ sk_B_1 @ X13) != (k1_funct_1 @ sk_B_1 @ X12))
% 0.20/0.47                 | ~ (r2_hidden @ X12 @ sk_A)
% 0.20/0.47                 | ~ (r2_hidden @ X13 @ sk_A))))),
% 0.20/0.47      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.20/0.47  thf('56', plain,
% 0.20/0.47      (((v2_funct_1 @ sk_B_1))
% 0.20/0.47         <= (~ ((v2_funct_1 @ sk_B_1)) & 
% 0.20/0.47             (![X12 : $i, X13 : $i]:
% 0.20/0.47                (((X13) = (X12))
% 0.20/0.47                 | ((k1_funct_1 @ sk_B_1 @ X13) != (k1_funct_1 @ sk_B_1 @ X12))
% 0.20/0.47                 | ~ (r2_hidden @ X12 @ sk_A)
% 0.20/0.47                 | ~ (r2_hidden @ X13 @ sk_A))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['55'])).
% 0.20/0.47  thf('57', plain, ((~ (v2_funct_1 @ sk_B_1)) <= (~ ((v2_funct_1 @ sk_B_1)))),
% 0.20/0.47      inference('split', [status(esa)], ['48'])).
% 0.20/0.47  thf('58', plain,
% 0.20/0.47      (~
% 0.20/0.47       (![X12 : $i, X13 : $i]:
% 0.20/0.47          (((X13) = (X12))
% 0.20/0.47           | ((k1_funct_1 @ sk_B_1 @ X13) != (k1_funct_1 @ sk_B_1 @ X12))
% 0.20/0.47           | ~ (r2_hidden @ X12 @ sk_A)
% 0.20/0.47           | ~ (r2_hidden @ X13 @ sk_A))) | 
% 0.20/0.47       ((v2_funct_1 @ sk_B_1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.47  thf('59', plain, (((v2_funct_1 @ sk_B_1))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['25', '58'])).
% 0.20/0.47  thf('60', plain,
% 0.20/0.47      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))) | 
% 0.20/0.47       ~ ((v2_funct_1 @ sk_B_1))),
% 0.20/0.47      inference('split', [status(esa)], ['0'])).
% 0.20/0.47  thf('61', plain,
% 0.20/0.47      ((((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['25', '58', '60'])).
% 0.20/0.47  thf('62', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k1_funct_1 @ sk_B_1 @ sk_C_1) != (k1_funct_1 @ sk_B_1 @ X0))
% 0.20/0.47          | ~ (r2_hidden @ sk_D @ sk_A)
% 0.20/0.47          | ((sk_D) = (X0))
% 0.20/0.47          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['24', '59', '61'])).
% 0.20/0.47  thf('63', plain, (((r2_hidden @ sk_D @ sk_A) | ~ (v2_funct_1 @ sk_B_1))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('64', plain,
% 0.20/0.47      (((r2_hidden @ sk_D @ sk_A)) <= (((r2_hidden @ sk_D @ sk_A)))),
% 0.20/0.47      inference('split', [status(esa)], ['63'])).
% 0.20/0.47  thf('65', plain, (((r2_hidden @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.20/0.47      inference('split', [status(esa)], ['63'])).
% 0.20/0.47  thf('66', plain, (((r2_hidden @ sk_D @ sk_A))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['25', '58', '65'])).
% 0.20/0.47  thf('67', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['64', '66'])).
% 0.20/0.47  thf('68', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k1_funct_1 @ sk_B_1 @ sk_C_1) != (k1_funct_1 @ sk_B_1 @ X0))
% 0.20/0.47          | ((sk_D) = (X0))
% 0.20/0.47          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['62', '67'])).
% 0.20/0.47  thf('69', plain, ((~ (r2_hidden @ sk_C_1 @ sk_A) | ((sk_D) = (sk_C_1)))),
% 0.20/0.47      inference('eq_res', [status(thm)], ['68'])).
% 0.20/0.47  thf('70', plain,
% 0.20/0.47      (((r2_hidden @ sk_C_1 @ sk_A)) <= (((r2_hidden @ sk_C_1 @ sk_A)))),
% 0.20/0.47      inference('split', [status(esa)], ['48'])).
% 0.20/0.47  thf('71', plain, (((r2_hidden @ sk_C_1 @ sk_A)) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.20/0.47      inference('split', [status(esa)], ['48'])).
% 0.20/0.47  thf('72', plain, (((r2_hidden @ sk_C_1 @ sk_A))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['25', '58', '71'])).
% 0.20/0.47  thf('73', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['70', '72'])).
% 0.20/0.47  thf('74', plain, (((sk_D) = (sk_C_1))),
% 0.20/0.47      inference('demod', [status(thm)], ['69', '73'])).
% 0.20/0.47  thf('75', plain, ((((sk_C_1) != (sk_D)) | ~ (v2_funct_1 @ sk_B_1))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('76', plain, ((((sk_C_1) != (sk_D))) <= (~ (((sk_C_1) = (sk_D))))),
% 0.20/0.47      inference('split', [status(esa)], ['75'])).
% 0.20/0.47  thf('77', plain, (~ (((sk_C_1) = (sk_D))) | ~ ((v2_funct_1 @ sk_B_1))),
% 0.20/0.47      inference('split', [status(esa)], ['75'])).
% 0.20/0.47  thf('78', plain, (~ (((sk_C_1) = (sk_D)))),
% 0.20/0.47      inference('sat_resolution*', [status(thm)], ['25', '58', '77'])).
% 0.20/0.47  thf('79', plain, (((sk_C_1) != (sk_D))),
% 0.20/0.47      inference('simpl_trail', [status(thm)], ['76', '78'])).
% 0.20/0.47  thf('80', plain, ($false),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['74', '79'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
