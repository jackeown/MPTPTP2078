%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HEhBbT3SGQ

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:24 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 363 expanded)
%              Number of leaves         :   42 ( 125 expanded)
%              Depth                    :   20
%              Number of atoms          : 1088 (4675 expanded)
%              Number of equality atoms :   75 ( 294 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X11 @ X12 ) @ X11 )
      | ( ( sk_C_1 @ X11 @ X12 )
        = ( k1_funct_1 @ X12 @ ( sk_D @ X11 @ X12 ) ) )
      | ( X11
        = ( k2_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X11 @ X12 ) @ X11 )
      | ( r2_hidden @ ( sk_D @ X11 @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ( X11
        = ( k2_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('2',plain,(
    ! [X12: $i,X14: $i,X16: $i,X17: $i] :
      ( ( X14
       != ( k2_relat_1 @ X12 ) )
      | ( r2_hidden @ X16 @ X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X12 ) )
      | ( X16
       != ( k1_funct_1 @ X12 @ X17 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('3',plain,(
    ! [X12: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X12 @ X17 ) @ ( k2_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t16_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( ( r2_hidden @ E @ A )
                    & ( D
                      = ( k1_funct_1 @ C @ E ) ) ) )
       => ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ! [D: $i] :
              ~ ( ( r2_hidden @ D @ B )
                & ! [E: $i] :
                    ~ ( ( r2_hidden @ E @ A )
                      & ( D
                        = ( k1_funct_1 @ C @ E ) ) ) )
         => ( ( k2_relset_1 @ A @ B @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_2])).

thf('8',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v5_relat_1 @ X20 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('10',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v5_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['12','17'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('23',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(eq_fact,[status(thm)],['24'])).

thf('26',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('29',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['26','29'])).

thf('31',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X37: $i] :
      ( ~ ( r2_hidden @ X37 @ sk_B )
      | ( X37
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_C_1 @ sk_B @ sk_C_2 )
    = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['25','30'])).

thf('35',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X11 @ X12 ) @ X11 )
      | ( ( sk_C_1 @ X11 @ X12 )
       != ( k1_funct_1 @ X12 @ X13 ) )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X12 ) )
      | ( X11
        = ( k2_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ sk_B @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('38',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('39',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('40',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('45',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('50',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X0 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('54',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('56',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('57',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['51','58'])).

thf('60',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('61',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X11 @ X12 ) @ X11 )
      | ( r2_hidden @ ( sk_D @ X11 @ X12 ) @ ( k1_relat_1 @ X12 ) )
      | ( X11
        = ( k2_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('62',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0
        = ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_C_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( k1_xboole_0
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X12: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X12 @ X17 ) @ ( k2_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D @ k1_xboole_0 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D @ k1_xboole_0 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ( k1_xboole_0
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ X0 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k1_funct_1 @ X0 @ ( sk_D @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_C_2 ) )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['59','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('73',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( k1_xboole_0
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['26','29'])).

thf('75',plain,
    ( ( k1_xboole_0 != sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('77',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('78',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('80',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['75','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( sk_C_1 @ sk_B @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['36','37','38','81'])).

thf('83',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['26','29'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( sk_C_1 @ sk_B @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( sk_C_1 @ sk_B @ sk_C_2 )
     != ( sk_C_1 @ sk_B @ sk_C_2 ) )
    | ~ ( r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['33','84'])).

thf('86',plain,(
    r2_hidden @ ( sk_C_1 @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['25','30'])).

thf('87',plain,(
    ! [X37: $i] :
      ( ~ ( r2_hidden @ X37 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X37 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    r2_hidden @ ( sk_E @ ( sk_C_1 @ sk_B @ sk_C_2 ) ) @ sk_A ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ( sk_C_1 @ sk_B @ sk_C_2 )
 != ( sk_C_1 @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['85','88'])).

thf('90',plain,(
    $false ),
    inference(simplify,[status(thm)],['89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HEhBbT3SGQ
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:36:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.62/1.87  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.62/1.87  % Solved by: fo/fo7.sh
% 1.62/1.87  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.62/1.87  % done 1582 iterations in 1.411s
% 1.62/1.87  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.62/1.87  % SZS output start Refutation
% 1.62/1.87  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.62/1.87  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.62/1.87  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.62/1.87  thf(sk_A_type, type, sk_A: $i).
% 1.62/1.87  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.62/1.87  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.62/1.87  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.62/1.87  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.62/1.87  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.62/1.87  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.62/1.87  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.62/1.87  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.62/1.87  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.62/1.87  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.62/1.87  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.62/1.87  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.62/1.87  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.62/1.87  thf(sk_E_type, type, sk_E: $i > $i).
% 1.62/1.87  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.62/1.87  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.62/1.87  thf(sk_B_type, type, sk_B: $i).
% 1.62/1.87  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.62/1.87  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.62/1.87  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.62/1.87  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.62/1.87  thf(d5_funct_1, axiom,
% 1.62/1.87    (![A:$i]:
% 1.62/1.87     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.62/1.87       ( ![B:$i]:
% 1.62/1.87         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.62/1.87           ( ![C:$i]:
% 1.62/1.87             ( ( r2_hidden @ C @ B ) <=>
% 1.62/1.87               ( ?[D:$i]:
% 1.62/1.87                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 1.62/1.87                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 1.62/1.87  thf('0', plain,
% 1.62/1.87      (![X11 : $i, X12 : $i]:
% 1.62/1.87         ((r2_hidden @ (sk_C_1 @ X11 @ X12) @ X11)
% 1.62/1.87          | ((sk_C_1 @ X11 @ X12) = (k1_funct_1 @ X12 @ (sk_D @ X11 @ X12)))
% 1.62/1.87          | ((X11) = (k2_relat_1 @ X12))
% 1.62/1.87          | ~ (v1_funct_1 @ X12)
% 1.62/1.87          | ~ (v1_relat_1 @ X12))),
% 1.62/1.87      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.62/1.87  thf('1', plain,
% 1.62/1.87      (![X11 : $i, X12 : $i]:
% 1.62/1.87         ((r2_hidden @ (sk_C_1 @ X11 @ X12) @ X11)
% 1.62/1.87          | (r2_hidden @ (sk_D @ X11 @ X12) @ (k1_relat_1 @ X12))
% 1.62/1.87          | ((X11) = (k2_relat_1 @ X12))
% 1.62/1.87          | ~ (v1_funct_1 @ X12)
% 1.62/1.87          | ~ (v1_relat_1 @ X12))),
% 1.62/1.87      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.62/1.87  thf('2', plain,
% 1.62/1.87      (![X12 : $i, X14 : $i, X16 : $i, X17 : $i]:
% 1.62/1.87         (((X14) != (k2_relat_1 @ X12))
% 1.62/1.87          | (r2_hidden @ X16 @ X14)
% 1.62/1.87          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X12))
% 1.62/1.87          | ((X16) != (k1_funct_1 @ X12 @ X17))
% 1.62/1.87          | ~ (v1_funct_1 @ X12)
% 1.62/1.87          | ~ (v1_relat_1 @ X12))),
% 1.62/1.87      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.62/1.87  thf('3', plain,
% 1.62/1.87      (![X12 : $i, X17 : $i]:
% 1.62/1.87         (~ (v1_relat_1 @ X12)
% 1.62/1.87          | ~ (v1_funct_1 @ X12)
% 1.62/1.87          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X12))
% 1.62/1.87          | (r2_hidden @ (k1_funct_1 @ X12 @ X17) @ (k2_relat_1 @ X12)))),
% 1.62/1.87      inference('simplify', [status(thm)], ['2'])).
% 1.62/1.87  thf('4', plain,
% 1.62/1.87      (![X0 : $i, X1 : $i]:
% 1.62/1.87         (~ (v1_relat_1 @ X0)
% 1.62/1.87          | ~ (v1_funct_1 @ X0)
% 1.62/1.87          | ((X1) = (k2_relat_1 @ X0))
% 1.62/1.87          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 1.62/1.87          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ X1 @ X0)) @ 
% 1.62/1.87             (k2_relat_1 @ X0))
% 1.62/1.87          | ~ (v1_funct_1 @ X0)
% 1.62/1.87          | ~ (v1_relat_1 @ X0))),
% 1.62/1.87      inference('sup-', [status(thm)], ['1', '3'])).
% 1.62/1.87  thf('5', plain,
% 1.62/1.87      (![X0 : $i, X1 : $i]:
% 1.62/1.87         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ X1 @ X0)) @ (k2_relat_1 @ X0))
% 1.62/1.87          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 1.62/1.87          | ((X1) = (k2_relat_1 @ X0))
% 1.62/1.87          | ~ (v1_funct_1 @ X0)
% 1.62/1.87          | ~ (v1_relat_1 @ X0))),
% 1.62/1.87      inference('simplify', [status(thm)], ['4'])).
% 1.62/1.87  thf('6', plain,
% 1.62/1.87      (![X0 : $i, X1 : $i]:
% 1.62/1.87         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k2_relat_1 @ X0))
% 1.62/1.87          | ~ (v1_relat_1 @ X0)
% 1.62/1.87          | ~ (v1_funct_1 @ X0)
% 1.62/1.87          | ((X1) = (k2_relat_1 @ X0))
% 1.62/1.87          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 1.62/1.87          | ~ (v1_relat_1 @ X0)
% 1.62/1.87          | ~ (v1_funct_1 @ X0)
% 1.62/1.87          | ((X1) = (k2_relat_1 @ X0))
% 1.62/1.87          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1))),
% 1.62/1.87      inference('sup+', [status(thm)], ['0', '5'])).
% 1.62/1.87  thf('7', plain,
% 1.62/1.87      (![X0 : $i, X1 : $i]:
% 1.62/1.87         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 1.62/1.87          | ((X1) = (k2_relat_1 @ X0))
% 1.62/1.87          | ~ (v1_funct_1 @ X0)
% 1.62/1.87          | ~ (v1_relat_1 @ X0)
% 1.62/1.87          | (r2_hidden @ (sk_C_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.62/1.87      inference('simplify', [status(thm)], ['6'])).
% 1.62/1.87  thf(t16_funct_2, conjecture,
% 1.62/1.87    (![A:$i,B:$i,C:$i]:
% 1.62/1.87     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.62/1.87         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.62/1.87       ( ( ![D:$i]:
% 1.62/1.87           ( ~( ( r2_hidden @ D @ B ) & 
% 1.62/1.87                ( ![E:$i]:
% 1.62/1.87                  ( ~( ( r2_hidden @ E @ A ) & 
% 1.62/1.87                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 1.62/1.87         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 1.62/1.87  thf(zf_stmt_0, negated_conjecture,
% 1.62/1.87    (~( ![A:$i,B:$i,C:$i]:
% 1.62/1.87        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.62/1.87            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.62/1.87          ( ( ![D:$i]:
% 1.62/1.87              ( ~( ( r2_hidden @ D @ B ) & 
% 1.62/1.87                   ( ![E:$i]:
% 1.62/1.87                     ( ~( ( r2_hidden @ E @ A ) & 
% 1.62/1.87                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 1.62/1.87            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 1.62/1.87    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 1.62/1.87  thf('8', plain,
% 1.62/1.87      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.62/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.87  thf(cc2_relset_1, axiom,
% 1.62/1.87    (![A:$i,B:$i,C:$i]:
% 1.62/1.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.62/1.87       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.62/1.87  thf('9', plain,
% 1.62/1.87      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.62/1.87         ((v5_relat_1 @ X20 @ X22)
% 1.62/1.87          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.62/1.87      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.62/1.87  thf('10', plain, ((v5_relat_1 @ sk_C_2 @ sk_B)),
% 1.62/1.87      inference('sup-', [status(thm)], ['8', '9'])).
% 1.62/1.87  thf(d19_relat_1, axiom,
% 1.62/1.87    (![A:$i,B:$i]:
% 1.62/1.87     ( ( v1_relat_1 @ B ) =>
% 1.62/1.87       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.62/1.87  thf('11', plain,
% 1.62/1.87      (![X7 : $i, X8 : $i]:
% 1.62/1.87         (~ (v5_relat_1 @ X7 @ X8)
% 1.62/1.87          | (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 1.62/1.87          | ~ (v1_relat_1 @ X7))),
% 1.62/1.87      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.62/1.87  thf('12', plain,
% 1.62/1.87      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B))),
% 1.62/1.87      inference('sup-', [status(thm)], ['10', '11'])).
% 1.62/1.87  thf('13', plain,
% 1.62/1.87      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.62/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.87  thf(cc2_relat_1, axiom,
% 1.62/1.87    (![A:$i]:
% 1.62/1.87     ( ( v1_relat_1 @ A ) =>
% 1.62/1.87       ( ![B:$i]:
% 1.62/1.87         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.62/1.87  thf('14', plain,
% 1.62/1.87      (![X5 : $i, X6 : $i]:
% 1.62/1.87         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 1.62/1.87          | (v1_relat_1 @ X5)
% 1.62/1.87          | ~ (v1_relat_1 @ X6))),
% 1.62/1.87      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.62/1.87  thf('15', plain,
% 1.62/1.87      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_2))),
% 1.62/1.87      inference('sup-', [status(thm)], ['13', '14'])).
% 1.62/1.87  thf(fc6_relat_1, axiom,
% 1.62/1.87    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.62/1.87  thf('16', plain,
% 1.62/1.87      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 1.62/1.87      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.62/1.87  thf('17', plain, ((v1_relat_1 @ sk_C_2)),
% 1.62/1.87      inference('demod', [status(thm)], ['15', '16'])).
% 1.62/1.87  thf('18', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 1.62/1.87      inference('demod', [status(thm)], ['12', '17'])).
% 1.62/1.87  thf(d3_tarski, axiom,
% 1.62/1.87    (![A:$i,B:$i]:
% 1.62/1.87     ( ( r1_tarski @ A @ B ) <=>
% 1.62/1.87       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.62/1.87  thf('19', plain,
% 1.62/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.62/1.87         (~ (r2_hidden @ X0 @ X1)
% 1.62/1.87          | (r2_hidden @ X0 @ X2)
% 1.62/1.87          | ~ (r1_tarski @ X1 @ X2))),
% 1.62/1.87      inference('cnf', [status(esa)], [d3_tarski])).
% 1.62/1.87  thf('20', plain,
% 1.62/1.87      (![X0 : $i]:
% 1.62/1.87         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 1.62/1.87      inference('sup-', [status(thm)], ['18', '19'])).
% 1.62/1.87  thf('21', plain,
% 1.62/1.87      (![X0 : $i]:
% 1.62/1.87         (~ (v1_relat_1 @ sk_C_2)
% 1.62/1.87          | ~ (v1_funct_1 @ sk_C_2)
% 1.62/1.87          | ((X0) = (k2_relat_1 @ sk_C_2))
% 1.62/1.87          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 1.62/1.87          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_B))),
% 1.62/1.87      inference('sup-', [status(thm)], ['7', '20'])).
% 1.62/1.87  thf('22', plain, ((v1_relat_1 @ sk_C_2)),
% 1.62/1.87      inference('demod', [status(thm)], ['15', '16'])).
% 1.62/1.87  thf('23', plain, ((v1_funct_1 @ sk_C_2)),
% 1.62/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.87  thf('24', plain,
% 1.62/1.87      (![X0 : $i]:
% 1.62/1.87         (((X0) = (k2_relat_1 @ sk_C_2))
% 1.62/1.87          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 1.62/1.87          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_B))),
% 1.62/1.87      inference('demod', [status(thm)], ['21', '22', '23'])).
% 1.62/1.87  thf('25', plain,
% 1.62/1.87      (((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)
% 1.62/1.87        | ((sk_B) = (k2_relat_1 @ sk_C_2)))),
% 1.62/1.87      inference('eq_fact', [status(thm)], ['24'])).
% 1.62/1.87  thf('26', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))),
% 1.62/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.87  thf('27', plain,
% 1.62/1.87      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.62/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.87  thf(redefinition_k2_relset_1, axiom,
% 1.62/1.87    (![A:$i,B:$i,C:$i]:
% 1.62/1.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.62/1.87       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.62/1.87  thf('28', plain,
% 1.62/1.87      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.62/1.87         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 1.62/1.87          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.62/1.87      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.62/1.87  thf('29', plain,
% 1.62/1.87      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 1.62/1.87      inference('sup-', [status(thm)], ['27', '28'])).
% 1.62/1.87  thf('30', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 1.62/1.87      inference('demod', [status(thm)], ['26', '29'])).
% 1.62/1.87  thf('31', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 1.62/1.87      inference('simplify_reflect-', [status(thm)], ['25', '30'])).
% 1.62/1.87  thf('32', plain,
% 1.62/1.87      (![X37 : $i]:
% 1.62/1.87         (~ (r2_hidden @ X37 @ sk_B)
% 1.62/1.87          | ((X37) = (k1_funct_1 @ sk_C_2 @ (sk_E @ X37))))),
% 1.62/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.87  thf('33', plain,
% 1.62/1.87      (((sk_C_1 @ sk_B @ sk_C_2)
% 1.62/1.87         = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2))))),
% 1.62/1.87      inference('sup-', [status(thm)], ['31', '32'])).
% 1.62/1.87  thf('34', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 1.62/1.87      inference('simplify_reflect-', [status(thm)], ['25', '30'])).
% 1.62/1.87  thf('35', plain,
% 1.62/1.87      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.62/1.87         (~ (r2_hidden @ (sk_C_1 @ X11 @ X12) @ X11)
% 1.62/1.87          | ((sk_C_1 @ X11 @ X12) != (k1_funct_1 @ X12 @ X13))
% 1.62/1.87          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X12))
% 1.62/1.87          | ((X11) = (k2_relat_1 @ X12))
% 1.62/1.87          | ~ (v1_funct_1 @ X12)
% 1.62/1.87          | ~ (v1_relat_1 @ X12))),
% 1.62/1.87      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.62/1.87  thf('36', plain,
% 1.62/1.87      (![X0 : $i]:
% 1.62/1.87         (~ (v1_relat_1 @ sk_C_2)
% 1.62/1.87          | ~ (v1_funct_1 @ sk_C_2)
% 1.62/1.87          | ((sk_B) = (k2_relat_1 @ sk_C_2))
% 1.62/1.87          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 1.62/1.87          | ((sk_C_1 @ sk_B @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 1.62/1.87      inference('sup-', [status(thm)], ['34', '35'])).
% 1.62/1.87  thf('37', plain, ((v1_relat_1 @ sk_C_2)),
% 1.62/1.87      inference('demod', [status(thm)], ['15', '16'])).
% 1.62/1.87  thf('38', plain, ((v1_funct_1 @ sk_C_2)),
% 1.62/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.87  thf(d1_funct_2, axiom,
% 1.62/1.87    (![A:$i,B:$i,C:$i]:
% 1.62/1.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.62/1.87       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.62/1.87           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.62/1.87             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.62/1.87         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.62/1.87           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.62/1.87             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.62/1.87  thf(zf_stmt_1, axiom,
% 1.62/1.87    (![B:$i,A:$i]:
% 1.62/1.87     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.62/1.87       ( zip_tseitin_0 @ B @ A ) ))).
% 1.62/1.87  thf('39', plain,
% 1.62/1.87      (![X29 : $i, X30 : $i]:
% 1.62/1.87         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 1.62/1.87      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.62/1.87  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.62/1.87  thf('40', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 1.62/1.87      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.62/1.87  thf('41', plain,
% 1.62/1.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.62/1.87         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 1.62/1.87      inference('sup+', [status(thm)], ['39', '40'])).
% 1.62/1.87  thf('42', plain,
% 1.62/1.87      (![X1 : $i, X3 : $i]:
% 1.62/1.87         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.62/1.87      inference('cnf', [status(esa)], [d3_tarski])).
% 1.62/1.87  thf('43', plain,
% 1.62/1.87      (![X0 : $i]:
% 1.62/1.87         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 1.62/1.87      inference('sup-', [status(thm)], ['18', '19'])).
% 1.62/1.87  thf('44', plain,
% 1.62/1.87      (![X0 : $i]:
% 1.62/1.87         ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ X0)
% 1.62/1.87          | (r2_hidden @ (sk_C @ X0 @ (k2_relat_1 @ sk_C_2)) @ sk_B))),
% 1.62/1.87      inference('sup-', [status(thm)], ['42', '43'])).
% 1.62/1.87  thf(t7_ordinal1, axiom,
% 1.62/1.87    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.62/1.87  thf('45', plain,
% 1.62/1.87      (![X18 : $i, X19 : $i]:
% 1.62/1.87         (~ (r2_hidden @ X18 @ X19) | ~ (r1_tarski @ X19 @ X18))),
% 1.62/1.87      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.62/1.87  thf('46', plain,
% 1.62/1.87      (![X0 : $i]:
% 1.62/1.87         ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ X0)
% 1.62/1.87          | ~ (r1_tarski @ sk_B @ (sk_C @ X0 @ (k2_relat_1 @ sk_C_2))))),
% 1.62/1.87      inference('sup-', [status(thm)], ['44', '45'])).
% 1.62/1.87  thf('47', plain,
% 1.62/1.87      (![X0 : $i, X1 : $i]:
% 1.62/1.87         ((zip_tseitin_0 @ sk_B @ X1)
% 1.62/1.87          | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ X0))),
% 1.62/1.87      inference('sup-', [status(thm)], ['41', '46'])).
% 1.62/1.87  thf('48', plain,
% 1.62/1.87      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.62/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.87  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.62/1.87  thf(zf_stmt_3, axiom,
% 1.62/1.87    (![C:$i,B:$i,A:$i]:
% 1.62/1.87     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.62/1.87       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.62/1.87  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.62/1.87  thf(zf_stmt_5, axiom,
% 1.62/1.87    (![A:$i,B:$i,C:$i]:
% 1.62/1.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.62/1.87       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.62/1.87         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.62/1.87           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.62/1.87             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.62/1.87  thf('49', plain,
% 1.62/1.87      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.62/1.87         (~ (zip_tseitin_0 @ X34 @ X35)
% 1.62/1.87          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 1.62/1.87          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 1.62/1.87      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.62/1.87  thf('50', plain,
% 1.62/1.87      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 1.62/1.87        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.62/1.87      inference('sup-', [status(thm)], ['48', '49'])).
% 1.62/1.87  thf('51', plain,
% 1.62/1.87      (![X0 : $i]:
% 1.62/1.87         ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ X0)
% 1.62/1.87          | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 1.62/1.87      inference('sup-', [status(thm)], ['47', '50'])).
% 1.62/1.87  thf('52', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 1.62/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.87  thf('53', plain,
% 1.62/1.87      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.62/1.87         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 1.62/1.87          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 1.62/1.87          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 1.62/1.87      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.62/1.87  thf('54', plain,
% 1.62/1.87      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 1.62/1.87        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 1.62/1.87      inference('sup-', [status(thm)], ['52', '53'])).
% 1.62/1.87  thf('55', plain,
% 1.62/1.87      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.62/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.87  thf(redefinition_k1_relset_1, axiom,
% 1.62/1.87    (![A:$i,B:$i,C:$i]:
% 1.62/1.87     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.62/1.87       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.62/1.87  thf('56', plain,
% 1.62/1.87      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.62/1.87         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 1.62/1.87          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 1.62/1.87      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.62/1.87  thf('57', plain,
% 1.62/1.87      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 1.62/1.87      inference('sup-', [status(thm)], ['55', '56'])).
% 1.62/1.87  thf('58', plain,
% 1.62/1.87      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 1.62/1.87        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 1.62/1.87      inference('demod', [status(thm)], ['54', '57'])).
% 1.62/1.87  thf('59', plain,
% 1.62/1.87      (![X0 : $i]:
% 1.62/1.87         ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ X0)
% 1.62/1.87          | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 1.62/1.87      inference('sup-', [status(thm)], ['51', '58'])).
% 1.62/1.87  thf('60', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 1.62/1.87      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.62/1.87  thf('61', plain,
% 1.62/1.87      (![X11 : $i, X12 : $i]:
% 1.62/1.87         ((r2_hidden @ (sk_C_1 @ X11 @ X12) @ X11)
% 1.62/1.87          | (r2_hidden @ (sk_D @ X11 @ X12) @ (k1_relat_1 @ X12))
% 1.62/1.87          | ((X11) = (k2_relat_1 @ X12))
% 1.62/1.87          | ~ (v1_funct_1 @ X12)
% 1.62/1.87          | ~ (v1_relat_1 @ X12))),
% 1.62/1.87      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.62/1.87  thf('62', plain,
% 1.62/1.87      (![X18 : $i, X19 : $i]:
% 1.62/1.87         (~ (r2_hidden @ X18 @ X19) | ~ (r1_tarski @ X19 @ X18))),
% 1.62/1.87      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.62/1.87  thf('63', plain,
% 1.62/1.87      (![X0 : $i, X1 : $i]:
% 1.62/1.87         (~ (v1_relat_1 @ X1)
% 1.62/1.87          | ~ (v1_funct_1 @ X1)
% 1.62/1.87          | ((X0) = (k2_relat_1 @ X1))
% 1.62/1.87          | (r2_hidden @ (sk_D @ X0 @ X1) @ (k1_relat_1 @ X1))
% 1.62/1.87          | ~ (r1_tarski @ X0 @ (sk_C_1 @ X0 @ X1)))),
% 1.62/1.87      inference('sup-', [status(thm)], ['61', '62'])).
% 1.62/1.87  thf('64', plain,
% 1.62/1.87      (![X0 : $i]:
% 1.62/1.87         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X0) @ (k1_relat_1 @ X0))
% 1.62/1.87          | ((k1_xboole_0) = (k2_relat_1 @ X0))
% 1.62/1.87          | ~ (v1_funct_1 @ X0)
% 1.62/1.87          | ~ (v1_relat_1 @ X0))),
% 1.62/1.87      inference('sup-', [status(thm)], ['60', '63'])).
% 1.62/1.87  thf('65', plain,
% 1.62/1.87      (![X12 : $i, X17 : $i]:
% 1.62/1.87         (~ (v1_relat_1 @ X12)
% 1.62/1.87          | ~ (v1_funct_1 @ X12)
% 1.62/1.87          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X12))
% 1.62/1.87          | (r2_hidden @ (k1_funct_1 @ X12 @ X17) @ (k2_relat_1 @ X12)))),
% 1.62/1.87      inference('simplify', [status(thm)], ['2'])).
% 1.62/1.87  thf('66', plain,
% 1.62/1.87      (![X0 : $i]:
% 1.62/1.87         (~ (v1_relat_1 @ X0)
% 1.62/1.87          | ~ (v1_funct_1 @ X0)
% 1.62/1.87          | ((k1_xboole_0) = (k2_relat_1 @ X0))
% 1.62/1.87          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ k1_xboole_0 @ X0)) @ 
% 1.62/1.87             (k2_relat_1 @ X0))
% 1.62/1.87          | ~ (v1_funct_1 @ X0)
% 1.62/1.87          | ~ (v1_relat_1 @ X0))),
% 1.62/1.87      inference('sup-', [status(thm)], ['64', '65'])).
% 1.62/1.87  thf('67', plain,
% 1.62/1.87      (![X0 : $i]:
% 1.62/1.87         ((r2_hidden @ (k1_funct_1 @ X0 @ (sk_D @ k1_xboole_0 @ X0)) @ 
% 1.62/1.87           (k2_relat_1 @ X0))
% 1.62/1.87          | ((k1_xboole_0) = (k2_relat_1 @ X0))
% 1.62/1.87          | ~ (v1_funct_1 @ X0)
% 1.62/1.87          | ~ (v1_relat_1 @ X0))),
% 1.62/1.87      inference('simplify', [status(thm)], ['66'])).
% 1.62/1.87  thf('68', plain,
% 1.62/1.87      (![X18 : $i, X19 : $i]:
% 1.62/1.87         (~ (r2_hidden @ X18 @ X19) | ~ (r1_tarski @ X19 @ X18))),
% 1.62/1.87      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.62/1.87  thf('69', plain,
% 1.62/1.87      (![X0 : $i]:
% 1.62/1.87         (~ (v1_relat_1 @ X0)
% 1.62/1.87          | ~ (v1_funct_1 @ X0)
% 1.62/1.87          | ((k1_xboole_0) = (k2_relat_1 @ X0))
% 1.62/1.87          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 1.62/1.87               (k1_funct_1 @ X0 @ (sk_D @ k1_xboole_0 @ X0))))),
% 1.62/1.87      inference('sup-', [status(thm)], ['67', '68'])).
% 1.62/1.87  thf('70', plain,
% 1.62/1.87      ((((sk_A) = (k1_relat_1 @ sk_C_2))
% 1.62/1.87        | ((k1_xboole_0) = (k2_relat_1 @ sk_C_2))
% 1.62/1.87        | ~ (v1_funct_1 @ sk_C_2)
% 1.62/1.87        | ~ (v1_relat_1 @ sk_C_2))),
% 1.62/1.87      inference('sup-', [status(thm)], ['59', '69'])).
% 1.62/1.87  thf('71', plain, ((v1_funct_1 @ sk_C_2)),
% 1.62/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.87  thf('72', plain, ((v1_relat_1 @ sk_C_2)),
% 1.62/1.87      inference('demod', [status(thm)], ['15', '16'])).
% 1.62/1.87  thf('73', plain,
% 1.62/1.87      ((((sk_A) = (k1_relat_1 @ sk_C_2))
% 1.62/1.87        | ((k1_xboole_0) = (k2_relat_1 @ sk_C_2)))),
% 1.62/1.87      inference('demod', [status(thm)], ['70', '71', '72'])).
% 1.62/1.87  thf('74', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 1.62/1.87      inference('demod', [status(thm)], ['26', '29'])).
% 1.62/1.87  thf('75', plain,
% 1.62/1.87      ((((k1_xboole_0) != (sk_B)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 1.62/1.87      inference('sup-', [status(thm)], ['73', '74'])).
% 1.62/1.87  thf('76', plain,
% 1.62/1.87      (![X29 : $i, X30 : $i]:
% 1.62/1.87         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 1.62/1.87      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.62/1.87  thf('77', plain,
% 1.62/1.87      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 1.62/1.87        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.62/1.87      inference('sup-', [status(thm)], ['48', '49'])).
% 1.62/1.87  thf('78', plain,
% 1.62/1.87      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 1.62/1.87      inference('sup-', [status(thm)], ['76', '77'])).
% 1.62/1.87  thf('79', plain,
% 1.62/1.87      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 1.62/1.87        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 1.62/1.87      inference('demod', [status(thm)], ['54', '57'])).
% 1.62/1.87  thf('80', plain,
% 1.62/1.87      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 1.62/1.87      inference('sup-', [status(thm)], ['78', '79'])).
% 1.62/1.87  thf('81', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 1.62/1.87      inference('clc', [status(thm)], ['75', '80'])).
% 1.62/1.87  thf('82', plain,
% 1.62/1.87      (![X0 : $i]:
% 1.62/1.87         (((sk_B) = (k2_relat_1 @ sk_C_2))
% 1.62/1.87          | ~ (r2_hidden @ X0 @ sk_A)
% 1.62/1.87          | ((sk_C_1 @ sk_B @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 1.62/1.87      inference('demod', [status(thm)], ['36', '37', '38', '81'])).
% 1.62/1.87  thf('83', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 1.62/1.87      inference('demod', [status(thm)], ['26', '29'])).
% 1.62/1.87  thf('84', plain,
% 1.62/1.87      (![X0 : $i]:
% 1.62/1.87         (~ (r2_hidden @ X0 @ sk_A)
% 1.62/1.87          | ((sk_C_1 @ sk_B @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 1.62/1.87      inference('simplify_reflect-', [status(thm)], ['82', '83'])).
% 1.62/1.87  thf('85', plain,
% 1.62/1.87      ((((sk_C_1 @ sk_B @ sk_C_2) != (sk_C_1 @ sk_B @ sk_C_2))
% 1.62/1.87        | ~ (r2_hidden @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2)) @ sk_A))),
% 1.62/1.87      inference('sup-', [status(thm)], ['33', '84'])).
% 1.62/1.87  thf('86', plain, ((r2_hidden @ (sk_C_1 @ sk_B @ sk_C_2) @ sk_B)),
% 1.62/1.87      inference('simplify_reflect-', [status(thm)], ['25', '30'])).
% 1.62/1.87  thf('87', plain,
% 1.62/1.87      (![X37 : $i]:
% 1.62/1.87         (~ (r2_hidden @ X37 @ sk_B) | (r2_hidden @ (sk_E @ X37) @ sk_A))),
% 1.62/1.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.62/1.87  thf('88', plain, ((r2_hidden @ (sk_E @ (sk_C_1 @ sk_B @ sk_C_2)) @ sk_A)),
% 1.62/1.87      inference('sup-', [status(thm)], ['86', '87'])).
% 1.62/1.87  thf('89', plain, (((sk_C_1 @ sk_B @ sk_C_2) != (sk_C_1 @ sk_B @ sk_C_2))),
% 1.62/1.87      inference('demod', [status(thm)], ['85', '88'])).
% 1.62/1.87  thf('90', plain, ($false), inference('simplify', [status(thm)], ['89'])).
% 1.62/1.87  
% 1.62/1.87  % SZS output end Refutation
% 1.62/1.87  
% 1.71/1.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
