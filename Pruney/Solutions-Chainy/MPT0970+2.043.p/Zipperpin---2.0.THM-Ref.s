%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cSwwJ0uBKy

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:22 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 179 expanded)
%              Number of leaves         :   43 (  73 expanded)
%              Depth                    :   20
%              Number of atoms          :  769 (1823 expanded)
%              Number of equality atoms :   44 ( 103 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v5_relat_1 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['4','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_relat_1 @ sk_C_2 ) )
    | ( sk_B_1
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X40: $i] :
      ( ~ ( r2_hidden @ X40 @ sk_B_1 )
      | ( X40
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( ( sk_C @ X0 @ sk_B_1 )
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X40: $i] :
      ( ~ ( r2_hidden @ X40 @ sk_B_1 )
      | ( r2_hidden @ ( sk_E @ X40 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ X0 @ sk_B_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
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
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('20',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('26',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('27',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('33',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_1 )
      | ~ ( v1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('40',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('41',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('44',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['4','9'])).

thf('45',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) )
    | ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_C_2 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['42','49'])).

thf('51',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['28','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('53',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('54',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['21','51','54'])).

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

thf('56',plain,(
    ! [X17: $i,X19: $i,X21: $i,X22: $i] :
      ( ( X19
       != ( k2_relat_1 @ X17 ) )
      | ( r2_hidden @ X21 @ X19 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X17 ) )
      | ( X21
       != ( k1_funct_1 @ X17 @ X22 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('57',plain,(
    ! [X17: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X17 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X17 @ X22 ) @ ( k2_relat_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['7','8'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B_1 ) ) ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['18','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('66',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k2_relat_1 @ sk_C_2 ) )
    | ( r1_tarski @ sk_B_1 @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r1_tarski @ sk_B_1 @ ( k2_relat_1 @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( sk_B_1
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['12','67'])).

thf('69',plain,(
    ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('71',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B_1 ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['68','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cSwwJ0uBKy
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:38:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.61/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.61/0.83  % Solved by: fo/fo7.sh
% 0.61/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.83  % done 294 iterations in 0.376s
% 0.61/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.61/0.83  % SZS output start Refutation
% 0.61/0.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.61/0.83  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.61/0.83  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.61/0.83  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.61/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.83  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.61/0.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.61/0.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.61/0.83  thf(sk_E_type, type, sk_E: $i > $i).
% 0.61/0.83  thf(sk_B_type, type, sk_B: $i > $i).
% 0.61/0.83  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.61/0.83  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.61/0.83  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.61/0.83  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.61/0.83  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.61/0.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.61/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.83  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.61/0.83  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.61/0.83  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.61/0.83  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.61/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.83  thf(t16_funct_2, conjecture,
% 0.61/0.83    (![A:$i,B:$i,C:$i]:
% 0.61/0.83     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.61/0.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.61/0.83       ( ( ![D:$i]:
% 0.61/0.83           ( ~( ( r2_hidden @ D @ B ) & 
% 0.61/0.83                ( ![E:$i]:
% 0.61/0.83                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.61/0.83                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.61/0.83         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.61/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.83    (~( ![A:$i,B:$i,C:$i]:
% 0.61/0.83        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.61/0.83            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.61/0.83          ( ( ![D:$i]:
% 0.61/0.83              ( ~( ( r2_hidden @ D @ B ) & 
% 0.61/0.83                   ( ![E:$i]:
% 0.61/0.83                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.61/0.83                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.61/0.83            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.61/0.83    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.61/0.83  thf('0', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf(cc2_relset_1, axiom,
% 0.61/0.83    (![A:$i,B:$i,C:$i]:
% 0.61/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.83       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.61/0.83  thf('1', plain,
% 0.61/0.83      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.61/0.83         ((v5_relat_1 @ X23 @ X25)
% 0.61/0.83          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.61/0.83      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.61/0.83  thf('2', plain, ((v5_relat_1 @ sk_C_2 @ sk_B_1)),
% 0.61/0.83      inference('sup-', [status(thm)], ['0', '1'])).
% 0.61/0.83  thf(d19_relat_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( v1_relat_1 @ B ) =>
% 0.61/0.83       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.61/0.83  thf('3', plain,
% 0.61/0.83      (![X12 : $i, X13 : $i]:
% 0.61/0.83         (~ (v5_relat_1 @ X12 @ X13)
% 0.61/0.83          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.61/0.83          | ~ (v1_relat_1 @ X12))),
% 0.61/0.83      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.61/0.83  thf('4', plain,
% 0.61/0.83      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_1))),
% 0.61/0.83      inference('sup-', [status(thm)], ['2', '3'])).
% 0.61/0.83  thf('5', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf(cc2_relat_1, axiom,
% 0.61/0.83    (![A:$i]:
% 0.61/0.83     ( ( v1_relat_1 @ A ) =>
% 0.61/0.83       ( ![B:$i]:
% 0.61/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.61/0.83  thf('6', plain,
% 0.61/0.83      (![X10 : $i, X11 : $i]:
% 0.61/0.83         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.61/0.83          | (v1_relat_1 @ X10)
% 0.61/0.83          | ~ (v1_relat_1 @ X11))),
% 0.61/0.83      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.61/0.83  thf('7', plain,
% 0.61/0.83      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_2))),
% 0.61/0.83      inference('sup-', [status(thm)], ['5', '6'])).
% 0.61/0.83  thf(fc6_relat_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.61/0.83  thf('8', plain,
% 0.61/0.83      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.61/0.83      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.61/0.83  thf('9', plain, ((v1_relat_1 @ sk_C_2)),
% 0.61/0.83      inference('demod', [status(thm)], ['7', '8'])).
% 0.61/0.83  thf('10', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_1)),
% 0.61/0.83      inference('demod', [status(thm)], ['4', '9'])).
% 0.61/0.83  thf(d10_xboole_0, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.61/0.83  thf('11', plain,
% 0.61/0.83      (![X7 : $i, X9 : $i]:
% 0.61/0.83         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.61/0.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.83  thf('12', plain,
% 0.61/0.83      ((~ (r1_tarski @ sk_B_1 @ (k2_relat_1 @ sk_C_2))
% 0.61/0.83        | ((sk_B_1) = (k2_relat_1 @ sk_C_2)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['10', '11'])).
% 0.61/0.83  thf(d3_tarski, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( r1_tarski @ A @ B ) <=>
% 0.61/0.83       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.61/0.83  thf('13', plain,
% 0.61/0.83      (![X4 : $i, X6 : $i]:
% 0.61/0.83         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.61/0.83      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.83  thf('14', plain,
% 0.61/0.83      (![X40 : $i]:
% 0.61/0.83         (~ (r2_hidden @ X40 @ sk_B_1)
% 0.61/0.83          | ((X40) = (k1_funct_1 @ sk_C_2 @ (sk_E @ X40))))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('15', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         ((r1_tarski @ sk_B_1 @ X0)
% 0.61/0.83          | ((sk_C @ X0 @ sk_B_1)
% 0.61/0.83              = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B_1)))))),
% 0.61/0.83      inference('sup-', [status(thm)], ['13', '14'])).
% 0.61/0.83  thf('16', plain,
% 0.61/0.83      (![X4 : $i, X6 : $i]:
% 0.61/0.83         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.61/0.83      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.83  thf('17', plain,
% 0.61/0.83      (![X40 : $i]:
% 0.61/0.83         (~ (r2_hidden @ X40 @ sk_B_1) | (r2_hidden @ (sk_E @ X40) @ sk_A))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('18', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         ((r1_tarski @ sk_B_1 @ X0)
% 0.61/0.83          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ sk_B_1)) @ sk_A))),
% 0.61/0.83      inference('sup-', [status(thm)], ['16', '17'])).
% 0.61/0.83  thf('19', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf(d1_funct_2, axiom,
% 0.61/0.83    (![A:$i,B:$i,C:$i]:
% 0.61/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.83       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.61/0.83           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.61/0.83             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.61/0.83         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.61/0.83           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.61/0.83             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.61/0.83  thf(zf_stmt_1, axiom,
% 0.61/0.83    (![C:$i,B:$i,A:$i]:
% 0.61/0.83     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.61/0.83       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.61/0.83  thf('20', plain,
% 0.61/0.83      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.61/0.83         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 0.61/0.83          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 0.61/0.83          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.61/0.83  thf('21', plain,
% 0.61/0.83      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 0.61/0.83        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['19', '20'])).
% 0.61/0.83  thf(zf_stmt_2, axiom,
% 0.61/0.83    (![B:$i,A:$i]:
% 0.61/0.83     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.61/0.83       ( zip_tseitin_0 @ B @ A ) ))).
% 0.61/0.83  thf('22', plain,
% 0.61/0.83      (![X32 : $i, X33 : $i]:
% 0.61/0.83         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.61/0.83  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.61/0.83  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.61/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.61/0.83  thf('24', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.61/0.83      inference('sup+', [status(thm)], ['22', '23'])).
% 0.61/0.83  thf('25', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.61/0.83  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.61/0.83  thf(zf_stmt_5, axiom,
% 0.61/0.83    (![A:$i,B:$i,C:$i]:
% 0.61/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.83       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.61/0.83         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.61/0.83           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.61/0.83             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.61/0.83  thf('26', plain,
% 0.61/0.83      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.61/0.83         (~ (zip_tseitin_0 @ X37 @ X38)
% 0.61/0.83          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 0.61/0.83          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.61/0.83  thf('27', plain,
% 0.61/0.83      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 0.61/0.83        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.61/0.83      inference('sup-', [status(thm)], ['25', '26'])).
% 0.61/0.83  thf('28', plain,
% 0.61/0.83      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 0.61/0.83      inference('sup-', [status(thm)], ['24', '27'])).
% 0.61/0.83  thf('29', plain,
% 0.61/0.83      (![X4 : $i, X6 : $i]:
% 0.61/0.83         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.61/0.83      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.83  thf(d1_xboole_0, axiom,
% 0.61/0.83    (![A:$i]:
% 0.61/0.83     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.61/0.83  thf('30', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.61/0.83      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.61/0.83  thf('31', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.61/0.83      inference('sup-', [status(thm)], ['29', '30'])).
% 0.61/0.83  thf('32', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.61/0.83      inference('sup-', [status(thm)], ['29', '30'])).
% 0.61/0.83  thf('33', plain,
% 0.61/0.83      (![X7 : $i, X9 : $i]:
% 0.61/0.83         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.61/0.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.61/0.83  thf('34', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i]:
% 0.61/0.83         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['32', '33'])).
% 0.61/0.83  thf('35', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i]:
% 0.61/0.83         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.61/0.83      inference('sup-', [status(thm)], ['31', '34'])).
% 0.61/0.83  thf('36', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) != (sk_B_1))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('37', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         (((X0) != (sk_B_1))
% 0.61/0.83          | ~ (v1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2))
% 0.61/0.83          | ~ (v1_xboole_0 @ X0))),
% 0.61/0.83      inference('sup-', [status(thm)], ['35', '36'])).
% 0.61/0.83  thf('38', plain,
% 0.61/0.83      ((~ (v1_xboole_0 @ sk_B_1)
% 0.61/0.83        | ~ (v1_xboole_0 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 0.61/0.83      inference('simplify', [status(thm)], ['37'])).
% 0.61/0.83  thf('39', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf(redefinition_k2_relset_1, axiom,
% 0.61/0.83    (![A:$i,B:$i,C:$i]:
% 0.61/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.83       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.61/0.83  thf('40', plain,
% 0.61/0.83      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.61/0.83         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 0.61/0.83          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.61/0.83      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.61/0.83  thf('41', plain,
% 0.61/0.83      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.61/0.83      inference('sup-', [status(thm)], ['39', '40'])).
% 0.61/0.83  thf('42', plain,
% 0.61/0.83      ((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_C_2)))),
% 0.61/0.83      inference('demod', [status(thm)], ['38', '41'])).
% 0.61/0.83  thf('43', plain,
% 0.61/0.83      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.61/0.83      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.61/0.83  thf('44', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_1)),
% 0.61/0.83      inference('demod', [status(thm)], ['4', '9'])).
% 0.61/0.83  thf('45', plain,
% 0.61/0.83      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.61/0.83         (~ (r2_hidden @ X3 @ X4)
% 0.61/0.83          | (r2_hidden @ X3 @ X5)
% 0.61/0.83          | ~ (r1_tarski @ X4 @ X5))),
% 0.61/0.83      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.83  thf('46', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         ((r2_hidden @ X0 @ sk_B_1)
% 0.61/0.83          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['44', '45'])).
% 0.61/0.83  thf('47', plain,
% 0.61/0.83      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_2))
% 0.61/0.83        | (r2_hidden @ (sk_B @ (k2_relat_1 @ sk_C_2)) @ sk_B_1))),
% 0.61/0.83      inference('sup-', [status(thm)], ['43', '46'])).
% 0.61/0.83  thf('48', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.61/0.83      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.61/0.83  thf('49', plain,
% 0.61/0.83      (((v1_xboole_0 @ (k2_relat_1 @ sk_C_2)) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.61/0.83      inference('sup-', [status(thm)], ['47', '48'])).
% 0.61/0.83  thf('50', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.61/0.83      inference('clc', [status(thm)], ['42', '49'])).
% 0.61/0.83  thf('51', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)),
% 0.61/0.83      inference('clc', [status(thm)], ['28', '50'])).
% 0.61/0.83  thf('52', plain,
% 0.61/0.83      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf(redefinition_k1_relset_1, axiom,
% 0.61/0.83    (![A:$i,B:$i,C:$i]:
% 0.61/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.83       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.61/0.83  thf('53', plain,
% 0.61/0.83      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.61/0.83         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 0.61/0.83          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.61/0.83      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.61/0.83  thf('54', plain,
% 0.61/0.83      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.61/0.83      inference('sup-', [status(thm)], ['52', '53'])).
% 0.61/0.83  thf('55', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.61/0.83      inference('demod', [status(thm)], ['21', '51', '54'])).
% 0.61/0.83  thf(d5_funct_1, axiom,
% 0.61/0.83    (![A:$i]:
% 0.61/0.83     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.61/0.83       ( ![B:$i]:
% 0.61/0.83         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.61/0.83           ( ![C:$i]:
% 0.61/0.83             ( ( r2_hidden @ C @ B ) <=>
% 0.61/0.83               ( ?[D:$i]:
% 0.61/0.83                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.61/0.83                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.61/0.83  thf('56', plain,
% 0.61/0.83      (![X17 : $i, X19 : $i, X21 : $i, X22 : $i]:
% 0.61/0.83         (((X19) != (k2_relat_1 @ X17))
% 0.61/0.83          | (r2_hidden @ X21 @ X19)
% 0.61/0.83          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X17))
% 0.61/0.83          | ((X21) != (k1_funct_1 @ X17 @ X22))
% 0.61/0.83          | ~ (v1_funct_1 @ X17)
% 0.61/0.83          | ~ (v1_relat_1 @ X17))),
% 0.61/0.83      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.61/0.83  thf('57', plain,
% 0.61/0.83      (![X17 : $i, X22 : $i]:
% 0.61/0.83         (~ (v1_relat_1 @ X17)
% 0.61/0.83          | ~ (v1_funct_1 @ X17)
% 0.61/0.83          | ~ (r2_hidden @ X22 @ (k1_relat_1 @ X17))
% 0.61/0.83          | (r2_hidden @ (k1_funct_1 @ X17 @ X22) @ (k2_relat_1 @ X17)))),
% 0.61/0.83      inference('simplify', [status(thm)], ['56'])).
% 0.61/0.83  thf('58', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         (~ (r2_hidden @ X0 @ sk_A)
% 0.61/0.83          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2))
% 0.61/0.83          | ~ (v1_funct_1 @ sk_C_2)
% 0.61/0.83          | ~ (v1_relat_1 @ sk_C_2))),
% 0.61/0.83      inference('sup-', [status(thm)], ['55', '57'])).
% 0.61/0.83  thf('59', plain, ((v1_funct_1 @ sk_C_2)),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('60', plain, ((v1_relat_1 @ sk_C_2)),
% 0.61/0.83      inference('demod', [status(thm)], ['7', '8'])).
% 0.61/0.83  thf('61', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         (~ (r2_hidden @ X0 @ sk_A)
% 0.61/0.83          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 0.61/0.83      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.61/0.83  thf('62', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         ((r1_tarski @ sk_B_1 @ X0)
% 0.61/0.83          | (r2_hidden @ 
% 0.61/0.83             (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B_1))) @ 
% 0.61/0.83             (k2_relat_1 @ sk_C_2)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['18', '61'])).
% 0.61/0.83  thf('63', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         ((r2_hidden @ (sk_C @ X0 @ sk_B_1) @ (k2_relat_1 @ sk_C_2))
% 0.61/0.83          | (r1_tarski @ sk_B_1 @ X0)
% 0.61/0.83          | (r1_tarski @ sk_B_1 @ X0))),
% 0.61/0.83      inference('sup+', [status(thm)], ['15', '62'])).
% 0.61/0.83  thf('64', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         ((r1_tarski @ sk_B_1 @ X0)
% 0.61/0.83          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ (k2_relat_1 @ sk_C_2)))),
% 0.61/0.83      inference('simplify', [status(thm)], ['63'])).
% 0.61/0.83  thf('65', plain,
% 0.61/0.83      (![X4 : $i, X6 : $i]:
% 0.61/0.83         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.61/0.83      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.83  thf('66', plain,
% 0.61/0.83      (((r1_tarski @ sk_B_1 @ (k2_relat_1 @ sk_C_2))
% 0.61/0.83        | (r1_tarski @ sk_B_1 @ (k2_relat_1 @ sk_C_2)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['64', '65'])).
% 0.61/0.83  thf('67', plain, ((r1_tarski @ sk_B_1 @ (k2_relat_1 @ sk_C_2))),
% 0.61/0.83      inference('simplify', [status(thm)], ['66'])).
% 0.61/0.83  thf('68', plain, (((sk_B_1) = (k2_relat_1 @ sk_C_2))),
% 0.61/0.83      inference('demod', [status(thm)], ['12', '67'])).
% 0.61/0.83  thf('69', plain, (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) != (sk_B_1))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('70', plain,
% 0.61/0.83      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.61/0.83      inference('sup-', [status(thm)], ['39', '40'])).
% 0.61/0.83  thf('71', plain, (((k2_relat_1 @ sk_C_2) != (sk_B_1))),
% 0.61/0.83      inference('demod', [status(thm)], ['69', '70'])).
% 0.61/0.83  thf('72', plain, ($false),
% 0.61/0.83      inference('simplify_reflect-', [status(thm)], ['68', '71'])).
% 0.61/0.83  
% 0.61/0.83  % SZS output end Refutation
% 0.61/0.83  
% 0.61/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
