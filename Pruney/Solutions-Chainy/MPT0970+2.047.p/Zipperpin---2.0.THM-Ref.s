%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WTGYj3YTM4

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:23 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 154 expanded)
%              Number of leaves         :   40 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :  648 (1660 expanded)
%              Number of equality atoms :   39 ( 100 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v5_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
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
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) ) ),
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
    ! [X33: $i] :
      ( ~ ( r2_hidden @ X33 @ sk_B )
      | ( X33
        = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( sk_C @ X0 @ sk_B )
        = ( k1_funct_1 @ sk_C_1 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X33: $i] :
      ( ~ ( r2_hidden @ X33 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X33 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['4','9'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('24',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_C_1 )
        = sk_B )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('30',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('31',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = sk_B )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('35',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('36',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['33','36'])).

thf('38',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['32','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('40',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('41',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['21','38','41'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('43',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X15 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X15 @ X14 ) @ ( k2_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('46',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ X0 ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_1 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['18','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_1 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['12','53'])).

thf('55',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != sk_B ),
    inference(demod,[status(thm)],['33','36'])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WTGYj3YTM4
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:20:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.56  % Solved by: fo/fo7.sh
% 0.37/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.56  % done 96 iterations in 0.108s
% 0.37/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.56  % SZS output start Refutation
% 0.37/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.56  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.37/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.37/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.37/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.37/0.56  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.37/0.56  thf(sk_E_type, type, sk_E: $i > $i).
% 0.37/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.37/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.56  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.37/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.56  thf(t16_funct_2, conjecture,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.56       ( ( ![D:$i]:
% 0.37/0.56           ( ~( ( r2_hidden @ D @ B ) & 
% 0.37/0.56                ( ![E:$i]:
% 0.37/0.56                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.37/0.56                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.37/0.56         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.56        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.37/0.56            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.56          ( ( ![D:$i]:
% 0.37/0.56              ( ~( ( r2_hidden @ D @ B ) & 
% 0.37/0.56                   ( ![E:$i]:
% 0.37/0.56                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.37/0.56                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.37/0.56            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.37/0.56    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.37/0.56  thf('0', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(cc2_relset_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.56       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.37/0.56  thf('1', plain,
% 0.37/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.56         ((v5_relat_1 @ X16 @ X18)
% 0.37/0.56          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.37/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.56  thf('2', plain, ((v5_relat_1 @ sk_C_1 @ sk_B)),
% 0.37/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.56  thf(d19_relat_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ B ) =>
% 0.37/0.56       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.37/0.56  thf('3', plain,
% 0.37/0.56      (![X10 : $i, X11 : $i]:
% 0.37/0.56         (~ (v5_relat_1 @ X10 @ X11)
% 0.37/0.56          | (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 0.37/0.56          | ~ (v1_relat_1 @ X10))),
% 0.37/0.56      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.37/0.56  thf('4', plain,
% 0.37/0.56      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B))),
% 0.37/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.56  thf('5', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(cc2_relat_1, axiom,
% 0.37/0.56    (![A:$i]:
% 0.37/0.56     ( ( v1_relat_1 @ A ) =>
% 0.37/0.56       ( ![B:$i]:
% 0.37/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.37/0.56  thf('6', plain,
% 0.37/0.56      (![X8 : $i, X9 : $i]:
% 0.37/0.56         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.37/0.56          | (v1_relat_1 @ X8)
% 0.37/0.56          | ~ (v1_relat_1 @ X9))),
% 0.37/0.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.37/0.56  thf('7', plain,
% 0.37/0.56      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.56  thf(fc6_relat_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.37/0.56  thf('8', plain,
% 0.37/0.56      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 0.37/0.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.37/0.56  thf('9', plain, ((v1_relat_1 @ sk_C_1)),
% 0.37/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf('10', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.37/0.56      inference('demod', [status(thm)], ['4', '9'])).
% 0.37/0.56  thf(d10_xboole_0, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.56  thf('11', plain,
% 0.37/0.56      (![X4 : $i, X6 : $i]:
% 0.37/0.56         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.56  thf('12', plain,
% 0.37/0.56      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))
% 0.37/0.56        | ((sk_B) = (k2_relat_1 @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.56  thf(d3_tarski, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.56  thf('13', plain,
% 0.37/0.56      (![X1 : $i, X3 : $i]:
% 0.37/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.56  thf('14', plain,
% 0.37/0.56      (![X33 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X33 @ sk_B)
% 0.37/0.56          | ((X33) = (k1_funct_1 @ sk_C_1 @ (sk_E @ X33))))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('15', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r1_tarski @ sk_B @ X0)
% 0.37/0.56          | ((sk_C @ X0 @ sk_B)
% 0.37/0.56              = (k1_funct_1 @ sk_C_1 @ (sk_E @ (sk_C @ X0 @ sk_B)))))),
% 0.37/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.56  thf('16', plain,
% 0.37/0.56      (![X1 : $i, X3 : $i]:
% 0.37/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.56  thf('17', plain,
% 0.37/0.56      (![X33 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X33 @ sk_B) | (r2_hidden @ (sk_E @ X33) @ sk_A))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('18', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r1_tarski @ sk_B @ X0)
% 0.37/0.56          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ sk_B)) @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.56  thf('19', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(d1_funct_2, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.56       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.56           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.37/0.56             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.37/0.56         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.56           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.37/0.56             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.37/0.56  thf(zf_stmt_1, axiom,
% 0.37/0.56    (![C:$i,B:$i,A:$i]:
% 0.37/0.56     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.37/0.56       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.37/0.56  thf('20', plain,
% 0.37/0.56      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.37/0.56         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 0.37/0.56          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 0.37/0.56          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.56  thf('21', plain,
% 0.37/0.56      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.37/0.56        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.56  thf('22', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.37/0.56      inference('demod', [status(thm)], ['4', '9'])).
% 0.37/0.56  thf(zf_stmt_2, axiom,
% 0.37/0.56    (![B:$i,A:$i]:
% 0.37/0.56     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.56       ( zip_tseitin_0 @ B @ A ) ))).
% 0.37/0.56  thf('23', plain,
% 0.37/0.56      (![X25 : $i, X26 : $i]:
% 0.37/0.56         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.37/0.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.56  thf('24', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.37/0.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.56  thf('25', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.37/0.56      inference('sup+', [status(thm)], ['23', '24'])).
% 0.37/0.56  thf('26', plain,
% 0.37/0.56      (![X4 : $i, X6 : $i]:
% 0.37/0.56         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.37/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.56  thf('27', plain,
% 0.37/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.56         ((zip_tseitin_0 @ X1 @ X2) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.56  thf('28', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (((k2_relat_1 @ sk_C_1) = (sk_B)) | (zip_tseitin_0 @ sk_B @ X0))),
% 0.37/0.56      inference('sup-', [status(thm)], ['22', '27'])).
% 0.37/0.56  thf('29', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.37/0.56  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.37/0.56  thf(zf_stmt_5, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.56       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.37/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.56           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.37/0.56             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.37/0.56  thf('30', plain,
% 0.37/0.56      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.37/0.56         (~ (zip_tseitin_0 @ X30 @ X31)
% 0.37/0.56          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 0.37/0.56          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.37/0.56  thf('31', plain,
% 0.37/0.56      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.37/0.56        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.56  thf('32', plain,
% 0.37/0.56      ((((k2_relat_1 @ sk_C_1) = (sk_B))
% 0.37/0.56        | (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 0.37/0.56      inference('sup-', [status(thm)], ['28', '31'])).
% 0.37/0.56  thf('33', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('34', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(redefinition_k2_relset_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.56       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.37/0.56  thf('35', plain,
% 0.37/0.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.37/0.56         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 0.37/0.56          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.37/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.37/0.56  thf('36', plain,
% 0.37/0.56      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.56  thf('37', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 0.37/0.56      inference('demod', [status(thm)], ['33', '36'])).
% 0.37/0.56  thf('38', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)], ['32', '37'])).
% 0.37/0.56  thf('39', plain,
% 0.37/0.56      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.37/0.56    (![A:$i,B:$i,C:$i]:
% 0.37/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.37/0.56  thf('40', plain,
% 0.37/0.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.56         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.37/0.56          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.37/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.37/0.56  thf('41', plain,
% 0.37/0.56      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.37/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.56  thf('42', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.37/0.56      inference('demod', [status(thm)], ['21', '38', '41'])).
% 0.37/0.56  thf(t12_funct_1, axiom,
% 0.37/0.56    (![A:$i,B:$i]:
% 0.37/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.56       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.37/0.56         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.37/0.56  thf('43', plain,
% 0.37/0.56      (![X14 : $i, X15 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X14 @ (k1_relat_1 @ X15))
% 0.37/0.56          | (r2_hidden @ (k1_funct_1 @ X15 @ X14) @ (k2_relat_1 @ X15))
% 0.37/0.56          | ~ (v1_funct_1 @ X15)
% 0.37/0.56          | ~ (v1_relat_1 @ X15))),
% 0.37/0.56      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.37/0.56  thf('44', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X0 @ sk_A)
% 0.37/0.56          | ~ (v1_relat_1 @ sk_C_1)
% 0.37/0.56          | ~ (v1_funct_1 @ sk_C_1)
% 0.37/0.56          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.37/0.56  thf('45', plain, ((v1_relat_1 @ sk_C_1)),
% 0.37/0.56      inference('demod', [status(thm)], ['7', '8'])).
% 0.37/0.56  thf('46', plain, ((v1_funct_1 @ sk_C_1)),
% 0.37/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.56  thf('47', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         (~ (r2_hidden @ X0 @ sk_A)
% 0.37/0.56          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ X0) @ (k2_relat_1 @ sk_C_1)))),
% 0.37/0.56      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.37/0.56  thf('48', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r1_tarski @ sk_B @ X0)
% 0.37/0.56          | (r2_hidden @ (k1_funct_1 @ sk_C_1 @ (sk_E @ (sk_C @ X0 @ sk_B))) @ 
% 0.37/0.56             (k2_relat_1 @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['18', '47'])).
% 0.37/0.56  thf('49', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_1))
% 0.37/0.56          | (r1_tarski @ sk_B @ X0)
% 0.37/0.56          | (r1_tarski @ sk_B @ X0))),
% 0.37/0.56      inference('sup+', [status(thm)], ['15', '48'])).
% 0.37/0.56  thf('50', plain,
% 0.37/0.56      (![X0 : $i]:
% 0.37/0.56         ((r1_tarski @ sk_B @ X0)
% 0.37/0.56          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_1)))),
% 0.37/0.56      inference('simplify', [status(thm)], ['49'])).
% 0.37/0.56  thf('51', plain,
% 0.37/0.56      (![X1 : $i, X3 : $i]:
% 0.37/0.56         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.37/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.56  thf('52', plain,
% 0.37/0.56      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))
% 0.37/0.56        | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1)))),
% 0.37/0.56      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.56  thf('53', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_1))),
% 0.37/0.56      inference('simplify', [status(thm)], ['52'])).
% 0.37/0.56  thf('54', plain, (((sk_B) = (k2_relat_1 @ sk_C_1))),
% 0.37/0.56      inference('demod', [status(thm)], ['12', '53'])).
% 0.37/0.56  thf('55', plain, (((k2_relat_1 @ sk_C_1) != (sk_B))),
% 0.37/0.56      inference('demod', [status(thm)], ['33', '36'])).
% 0.37/0.56  thf('56', plain, ($false),
% 0.37/0.56      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.37/0.56  
% 0.37/0.56  % SZS output end Refutation
% 0.37/0.56  
% 0.37/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
