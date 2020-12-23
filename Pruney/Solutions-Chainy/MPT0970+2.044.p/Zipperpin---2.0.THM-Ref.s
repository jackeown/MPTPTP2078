%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QJBVwzSqmw

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:23 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 197 expanded)
%              Number of leaves         :   43 (  77 expanded)
%              Depth                    :   22
%              Number of atoms          :  818 (2166 expanded)
%              Number of equality atoms :   52 ( 139 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v5_relat_1 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['4','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X43: $i] :
      ( ~ ( r2_hidden @ X43 @ sk_B )
      | ( X43
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( sk_C @ X0 @ sk_B )
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X43: $i] :
      ( ~ ( r2_hidden @ X43 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X43 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

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

thf('19',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('20',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
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

thf('23',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('24',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_B = X1 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['4','9'])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('32',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = sk_B )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
      | ( zip_tseitin_0 @ X0 @ X1 )
      | ( ( k2_relat_1 @ sk_C_2 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['25','37'])).

thf('39',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X34 @ X32 )
        = ( k2_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('42',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['44','47'])).

thf('49',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('51',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('53',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('54',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('58',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('60',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['58','59'])).

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

thf('61',plain,(
    ! [X20: $i,X22: $i,X24: $i,X25: $i] :
      ( ( X22
       != ( k2_relat_1 @ X20 ) )
      | ( r2_hidden @ X24 @ X22 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X20 ) )
      | ( X24
       != ( k1_funct_1 @ X20 @ X25 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('62',plain,(
    ! [X20: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X20 @ X25 ) @ ( k2_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['7','8'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['18','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('71',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['12','72'])).

thf('74',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['39','42'])).

thf('75',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QJBVwzSqmw
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:53:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.77  % Solved by: fo/fo7.sh
% 0.53/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.77  % done 314 iterations in 0.304s
% 0.53/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.77  % SZS output start Refutation
% 0.53/0.77  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.53/0.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.53/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.77  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.53/0.77  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.53/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.77  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.53/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.77  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.53/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.77  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.53/0.77  thf(sk_E_type, type, sk_E: $i > $i).
% 0.53/0.77  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.53/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.53/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.77  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.53/0.77  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.53/0.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.53/0.77  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.53/0.77  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.53/0.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.53/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.53/0.77  thf(t16_funct_2, conjecture,
% 0.53/0.77    (![A:$i,B:$i,C:$i]:
% 0.53/0.77     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.53/0.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.77       ( ( ![D:$i]:
% 0.53/0.77           ( ~( ( r2_hidden @ D @ B ) & 
% 0.53/0.77                ( ![E:$i]:
% 0.53/0.77                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.53/0.77                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.53/0.77         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.53/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.77    (~( ![A:$i,B:$i,C:$i]:
% 0.53/0.77        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.53/0.77            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.53/0.77          ( ( ![D:$i]:
% 0.53/0.77              ( ~( ( r2_hidden @ D @ B ) & 
% 0.53/0.77                   ( ![E:$i]:
% 0.53/0.77                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.53/0.77                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.53/0.77            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.53/0.77    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.53/0.77  thf('0', plain,
% 0.53/0.77      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf(cc2_relset_1, axiom,
% 0.53/0.77    (![A:$i,B:$i,C:$i]:
% 0.53/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.77       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.53/0.77  thf('1', plain,
% 0.53/0.77      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.53/0.77         ((v5_relat_1 @ X26 @ X28)
% 0.53/0.77          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.53/0.77      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.53/0.77  thf('2', plain, ((v5_relat_1 @ sk_C_2 @ sk_B)),
% 0.53/0.77      inference('sup-', [status(thm)], ['0', '1'])).
% 0.53/0.77  thf(d19_relat_1, axiom,
% 0.53/0.77    (![A:$i,B:$i]:
% 0.53/0.77     ( ( v1_relat_1 @ B ) =>
% 0.53/0.77       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.53/0.77  thf('3', plain,
% 0.53/0.77      (![X15 : $i, X16 : $i]:
% 0.53/0.77         (~ (v5_relat_1 @ X15 @ X16)
% 0.53/0.77          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 0.53/0.77          | ~ (v1_relat_1 @ X15))),
% 0.53/0.77      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.53/0.77  thf('4', plain,
% 0.53/0.77      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B))),
% 0.53/0.77      inference('sup-', [status(thm)], ['2', '3'])).
% 0.53/0.77  thf('5', plain,
% 0.53/0.77      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf(cc2_relat_1, axiom,
% 0.53/0.77    (![A:$i]:
% 0.53/0.77     ( ( v1_relat_1 @ A ) =>
% 0.53/0.77       ( ![B:$i]:
% 0.53/0.77         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.53/0.77  thf('6', plain,
% 0.53/0.77      (![X13 : $i, X14 : $i]:
% 0.53/0.77         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.53/0.77          | (v1_relat_1 @ X13)
% 0.53/0.77          | ~ (v1_relat_1 @ X14))),
% 0.53/0.77      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.53/0.77  thf('7', plain,
% 0.53/0.77      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_2))),
% 0.53/0.77      inference('sup-', [status(thm)], ['5', '6'])).
% 0.53/0.77  thf(fc6_relat_1, axiom,
% 0.53/0.77    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.53/0.77  thf('8', plain,
% 0.53/0.77      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.53/0.77      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.53/0.77  thf('9', plain, ((v1_relat_1 @ sk_C_2)),
% 0.53/0.77      inference('demod', [status(thm)], ['7', '8'])).
% 0.53/0.77  thf('10', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.53/0.77      inference('demod', [status(thm)], ['4', '9'])).
% 0.53/0.77  thf(d10_xboole_0, axiom,
% 0.53/0.77    (![A:$i,B:$i]:
% 0.53/0.77     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.53/0.77  thf('11', plain,
% 0.53/0.77      (![X4 : $i, X6 : $i]:
% 0.53/0.77         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.53/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.77  thf('12', plain,
% 0.53/0.77      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 0.53/0.77        | ((sk_B) = (k2_relat_1 @ sk_C_2)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['10', '11'])).
% 0.53/0.77  thf(d3_tarski, axiom,
% 0.53/0.77    (![A:$i,B:$i]:
% 0.53/0.77     ( ( r1_tarski @ A @ B ) <=>
% 0.53/0.77       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.53/0.77  thf('13', plain,
% 0.53/0.77      (![X1 : $i, X3 : $i]:
% 0.53/0.77         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.53/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.77  thf('14', plain,
% 0.53/0.77      (![X43 : $i]:
% 0.53/0.77         (~ (r2_hidden @ X43 @ sk_B)
% 0.53/0.77          | ((X43) = (k1_funct_1 @ sk_C_2 @ (sk_E @ X43))))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('15', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((r1_tarski @ sk_B @ X0)
% 0.53/0.77          | ((sk_C @ X0 @ sk_B)
% 0.53/0.77              = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B)))))),
% 0.53/0.77      inference('sup-', [status(thm)], ['13', '14'])).
% 0.53/0.77  thf('16', plain,
% 0.53/0.77      (![X1 : $i, X3 : $i]:
% 0.53/0.77         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.53/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.77  thf('17', plain,
% 0.53/0.77      (![X43 : $i]:
% 0.53/0.77         (~ (r2_hidden @ X43 @ sk_B) | (r2_hidden @ (sk_E @ X43) @ sk_A))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('18', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((r1_tarski @ sk_B @ X0)
% 0.53/0.77          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ sk_B)) @ sk_A))),
% 0.53/0.77      inference('sup-', [status(thm)], ['16', '17'])).
% 0.53/0.77  thf(d1_funct_2, axiom,
% 0.53/0.77    (![A:$i,B:$i,C:$i]:
% 0.53/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.77       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.53/0.77           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.53/0.77             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.53/0.77         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.53/0.77           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.53/0.77             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.53/0.77  thf(zf_stmt_1, axiom,
% 0.53/0.77    (![B:$i,A:$i]:
% 0.53/0.77     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.53/0.77       ( zip_tseitin_0 @ B @ A ) ))).
% 0.53/0.77  thf('19', plain,
% 0.53/0.77      (![X35 : $i, X36 : $i]:
% 0.53/0.77         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.53/0.77  thf('20', plain,
% 0.53/0.77      (![X35 : $i, X36 : $i]:
% 0.53/0.77         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.53/0.77  thf('21', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.77         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X3) | (zip_tseitin_0 @ X1 @ X2))),
% 0.53/0.77      inference('sup+', [status(thm)], ['19', '20'])).
% 0.53/0.77  thf('22', plain,
% 0.53/0.77      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.53/0.77  thf(zf_stmt_3, axiom,
% 0.53/0.77    (![C:$i,B:$i,A:$i]:
% 0.53/0.77     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.53/0.77       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.53/0.77  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.53/0.77  thf(zf_stmt_5, axiom,
% 0.53/0.77    (![A:$i,B:$i,C:$i]:
% 0.53/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.77       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.53/0.77         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.53/0.77           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.53/0.77             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.53/0.77  thf('23', plain,
% 0.53/0.77      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.53/0.77         (~ (zip_tseitin_0 @ X40 @ X41)
% 0.53/0.77          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 0.53/0.77          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.53/0.77  thf('24', plain,
% 0.53/0.77      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.53/0.77        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.53/0.77      inference('sup-', [status(thm)], ['22', '23'])).
% 0.53/0.77  thf('25', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((zip_tseitin_0 @ X1 @ X0)
% 0.53/0.77          | ((sk_B) = (X1))
% 0.53/0.77          | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 0.53/0.77      inference('sup-', [status(thm)], ['21', '24'])).
% 0.53/0.77  thf('26', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.53/0.77      inference('demod', [status(thm)], ['4', '9'])).
% 0.53/0.77  thf('27', plain,
% 0.53/0.77      (![X1 : $i, X3 : $i]:
% 0.53/0.77         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.53/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.77  thf('28', plain,
% 0.53/0.77      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.53/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.77  thf('29', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.53/0.77      inference('simplify', [status(thm)], ['28'])).
% 0.53/0.77  thf(t3_subset, axiom,
% 0.53/0.77    (![A:$i,B:$i]:
% 0.53/0.77     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.53/0.77  thf('30', plain,
% 0.53/0.77      (![X7 : $i, X9 : $i]:
% 0.53/0.77         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.53/0.77      inference('cnf', [status(esa)], [t3_subset])).
% 0.53/0.77  thf('31', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.53/0.77      inference('sup-', [status(thm)], ['29', '30'])).
% 0.53/0.77  thf(t5_subset, axiom,
% 0.53/0.77    (![A:$i,B:$i,C:$i]:
% 0.53/0.77     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.53/0.77          ( v1_xboole_0 @ C ) ) ))).
% 0.53/0.77  thf('32', plain,
% 0.53/0.77      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.53/0.77         (~ (r2_hidden @ X10 @ X11)
% 0.53/0.77          | ~ (v1_xboole_0 @ X12)
% 0.53/0.77          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.53/0.77      inference('cnf', [status(esa)], [t5_subset])).
% 0.53/0.77  thf('33', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.53/0.77      inference('sup-', [status(thm)], ['31', '32'])).
% 0.53/0.77  thf('34', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.53/0.77      inference('sup-', [status(thm)], ['27', '33'])).
% 0.53/0.77  thf('35', plain,
% 0.53/0.77      (![X4 : $i, X6 : $i]:
% 0.53/0.77         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.53/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.77  thf('36', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['34', '35'])).
% 0.53/0.77  thf('37', plain,
% 0.53/0.77      ((((k2_relat_1 @ sk_C_2) = (sk_B)) | ~ (v1_xboole_0 @ sk_B))),
% 0.53/0.77      inference('sup-', [status(thm)], ['26', '36'])).
% 0.53/0.77  thf('38', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         (~ (v1_xboole_0 @ X0)
% 0.53/0.77          | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.53/0.77          | (zip_tseitin_0 @ X0 @ X1)
% 0.53/0.77          | ((k2_relat_1 @ sk_C_2) = (sk_B)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['25', '37'])).
% 0.53/0.77  thf('39', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('40', plain,
% 0.53/0.77      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf(redefinition_k2_relset_1, axiom,
% 0.53/0.77    (![A:$i,B:$i,C:$i]:
% 0.53/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.77       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.53/0.77  thf('41', plain,
% 0.53/0.77      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.53/0.77         (((k2_relset_1 @ X33 @ X34 @ X32) = (k2_relat_1 @ X32))
% 0.53/0.77          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.53/0.77      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.53/0.77  thf('42', plain,
% 0.53/0.77      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.53/0.77      inference('sup-', [status(thm)], ['40', '41'])).
% 0.53/0.77  thf('43', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 0.53/0.77      inference('demod', [status(thm)], ['39', '42'])).
% 0.53/0.77  thf('44', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         (~ (v1_xboole_0 @ X0)
% 0.53/0.77          | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.53/0.77          | (zip_tseitin_0 @ X0 @ X1))),
% 0.53/0.77      inference('simplify_reflect-', [status(thm)], ['38', '43'])).
% 0.53/0.77  thf('45', plain,
% 0.53/0.77      (![X35 : $i, X36 : $i]:
% 0.53/0.77         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.53/0.77  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.53/0.77  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.53/0.77      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.53/0.77  thf('47', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.53/0.77      inference('sup+', [status(thm)], ['45', '46'])).
% 0.53/0.77  thf('48', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((zip_tseitin_0 @ X0 @ X1) | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 0.53/0.77      inference('clc', [status(thm)], ['44', '47'])).
% 0.53/0.77  thf('49', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('50', plain,
% 0.53/0.77      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.53/0.77         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 0.53/0.77          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 0.53/0.77          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.53/0.77  thf('51', plain,
% 0.53/0.77      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.53/0.77        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['49', '50'])).
% 0.53/0.77  thf('52', plain,
% 0.53/0.77      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf(redefinition_k1_relset_1, axiom,
% 0.53/0.77    (![A:$i,B:$i,C:$i]:
% 0.53/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.53/0.77       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.53/0.77  thf('53', plain,
% 0.53/0.77      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.53/0.77         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 0.53/0.77          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.53/0.77      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.53/0.77  thf('54', plain,
% 0.53/0.77      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.53/0.77      inference('sup-', [status(thm)], ['52', '53'])).
% 0.53/0.77  thf('55', plain,
% 0.53/0.77      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.53/0.77        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 0.53/0.77      inference('demod', [status(thm)], ['51', '54'])).
% 0.53/0.77  thf('56', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         ((zip_tseitin_0 @ X1 @ X0) | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['48', '55'])).
% 0.53/0.77  thf('57', plain,
% 0.53/0.77      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.53/0.77        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.53/0.77      inference('sup-', [status(thm)], ['22', '23'])).
% 0.53/0.77  thf('58', plain,
% 0.53/0.77      ((((sk_A) = (k1_relat_1 @ sk_C_2))
% 0.53/0.77        | (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A))),
% 0.53/0.77      inference('sup-', [status(thm)], ['56', '57'])).
% 0.53/0.77  thf('59', plain,
% 0.53/0.77      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 0.53/0.77        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 0.53/0.77      inference('demod', [status(thm)], ['51', '54'])).
% 0.53/0.77  thf('60', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.53/0.77      inference('clc', [status(thm)], ['58', '59'])).
% 0.53/0.77  thf(d5_funct_1, axiom,
% 0.53/0.77    (![A:$i]:
% 0.53/0.77     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.53/0.77       ( ![B:$i]:
% 0.53/0.77         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.53/0.77           ( ![C:$i]:
% 0.53/0.77             ( ( r2_hidden @ C @ B ) <=>
% 0.53/0.77               ( ?[D:$i]:
% 0.53/0.77                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.53/0.77                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.53/0.77  thf('61', plain,
% 0.53/0.77      (![X20 : $i, X22 : $i, X24 : $i, X25 : $i]:
% 0.53/0.77         (((X22) != (k2_relat_1 @ X20))
% 0.53/0.77          | (r2_hidden @ X24 @ X22)
% 0.53/0.77          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X20))
% 0.53/0.77          | ((X24) != (k1_funct_1 @ X20 @ X25))
% 0.53/0.77          | ~ (v1_funct_1 @ X20)
% 0.53/0.77          | ~ (v1_relat_1 @ X20))),
% 0.53/0.77      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.53/0.77  thf('62', plain,
% 0.53/0.77      (![X20 : $i, X25 : $i]:
% 0.53/0.77         (~ (v1_relat_1 @ X20)
% 0.53/0.77          | ~ (v1_funct_1 @ X20)
% 0.53/0.77          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X20))
% 0.53/0.77          | (r2_hidden @ (k1_funct_1 @ X20 @ X25) @ (k2_relat_1 @ X20)))),
% 0.53/0.77      inference('simplify', [status(thm)], ['61'])).
% 0.53/0.77  thf('63', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         (~ (r2_hidden @ X0 @ sk_A)
% 0.53/0.77          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2))
% 0.53/0.77          | ~ (v1_funct_1 @ sk_C_2)
% 0.53/0.77          | ~ (v1_relat_1 @ sk_C_2))),
% 0.53/0.77      inference('sup-', [status(thm)], ['60', '62'])).
% 0.53/0.77  thf('64', plain, ((v1_funct_1 @ sk_C_2)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('65', plain, ((v1_relat_1 @ sk_C_2)),
% 0.53/0.77      inference('demod', [status(thm)], ['7', '8'])).
% 0.53/0.77  thf('66', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         (~ (r2_hidden @ X0 @ sk_A)
% 0.53/0.77          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 0.53/0.77      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.53/0.77  thf('67', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((r1_tarski @ sk_B @ X0)
% 0.53/0.77          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B))) @ 
% 0.53/0.77             (k2_relat_1 @ sk_C_2)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['18', '66'])).
% 0.53/0.77  thf('68', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2))
% 0.53/0.77          | (r1_tarski @ sk_B @ X0)
% 0.53/0.77          | (r1_tarski @ sk_B @ X0))),
% 0.53/0.77      inference('sup+', [status(thm)], ['15', '67'])).
% 0.53/0.77  thf('69', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         ((r1_tarski @ sk_B @ X0)
% 0.53/0.77          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2)))),
% 0.53/0.77      inference('simplify', [status(thm)], ['68'])).
% 0.53/0.77  thf('70', plain,
% 0.53/0.77      (![X1 : $i, X3 : $i]:
% 0.53/0.77         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.53/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.53/0.77  thf('71', plain,
% 0.53/0.77      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 0.53/0.77        | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2)))),
% 0.53/0.77      inference('sup-', [status(thm)], ['69', '70'])).
% 0.53/0.77  thf('72', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))),
% 0.53/0.77      inference('simplify', [status(thm)], ['71'])).
% 0.53/0.77  thf('73', plain, (((sk_B) = (k2_relat_1 @ sk_C_2))),
% 0.53/0.77      inference('demod', [status(thm)], ['12', '72'])).
% 0.53/0.77  thf('74', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 0.53/0.77      inference('demod', [status(thm)], ['39', '42'])).
% 0.53/0.77  thf('75', plain, ($false),
% 0.53/0.77      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 0.53/0.77  
% 0.53/0.77  % SZS output end Refutation
% 0.53/0.77  
% 0.61/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
