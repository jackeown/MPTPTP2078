%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qCKqthAPfJ

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:12 EST 2020

% Result     : Theorem 10.16s
% Output     : Refutation 10.16s
% Verified   : 
% Statistics : Number of formulae       :  238 (2954 expanded)
%              Number of leaves         :   36 ( 820 expanded)
%              Depth                    :   26
%              Number of atoms          : 2475 (55054 expanded)
%              Number of equality atoms :  213 (4316 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t145_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( ( B = k1_xboole_0 )
             => ( A = k1_xboole_0 ) )
           => ( ( r1_partfun1 @ C @ D )
            <=> ! [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ( ( B = k1_xboole_0 )
               => ( A = k1_xboole_0 ) )
             => ( ( r1_partfun1 @ C @ D )
              <=> ! [E: $i] :
                    ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) )
                   => ( ( k1_funct_1 @ C @ E )
                      = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t145_funct_2])).

thf('0',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
    | ~ ( r1_partfun1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
   <= ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relat_1 @ sk_C_2 ) )
   <= ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
    | ~ ( r1_partfun1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
    | ~ ( r1_partfun1 @ sk_C_2 @ sk_D ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

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

thf('12',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D )
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('20',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('22',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X18 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('24',plain,(
    ! [X17: $i] :
      ( zip_tseitin_0 @ X17 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','24'])).

thf('26',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','25'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('31',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X11 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('32',plain,
    ( ( m1_subset_1 @ ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('34',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('35',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_2 )
      = ( k1_relat_1 @ sk_C_2 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( m1_subset_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','35'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('37',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_C_2 ) ) @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','38'])).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,
    ( ( ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('43',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('44',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t132_partfun1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( r1_partfun1 @ A @ B )
            <=> ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ( r2_hidden @ ( sk_C_1 @ X25 @ X26 ) @ ( k1_relat_1 @ X26 ) )
      | ( r1_partfun1 @ X26 @ X25 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X26 ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ sk_C_2 )
        | ~ ( v1_funct_1 @ sk_C_2 )
        | ( r1_partfun1 @ sk_C_2 @ X0 )
        | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('48',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('49',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
        | ( r1_partfun1 @ sk_C_2 @ X0 )
        | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ k1_xboole_0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','49','50','51'])).

thf('53',plain,
    ( ( ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ k1_xboole_0 )
      | ( r1_partfun1 @ sk_C_2 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','52'])).

thf('54',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('60',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ k1_xboole_0 )
      | ( r1_partfun1 @ sk_C_2 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','57','60','61'])).

thf('63',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('64',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('65',plain,(
    ! [X28: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
      | ( ( k1_funct_1 @ sk_C_2 @ X28 )
        = ( k1_funct_1 @ sk_D @ X28 ) )
      | ( r1_partfun1 @ sk_C_2 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ! [X28: $i] :
        ( ~ ( r2_hidden @ X28 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
        | ( ( k1_funct_1 @ sk_C_2 @ X28 )
          = ( k1_funct_1 @ sk_D @ X28 ) ) )
   <= ! [X28: $i] :
        ( ~ ( r2_hidden @ X28 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
        | ( ( k1_funct_1 @ sk_C_2 @ X28 )
          = ( k1_funct_1 @ sk_D @ X28 ) ) ) ),
    inference(split,[status(esa)],['65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
        | ( ( k1_funct_1 @ sk_C_2 @ X0 )
          = ( k1_funct_1 @ sk_D @ X0 ) ) )
   <= ! [X28: $i] :
        ( ~ ( r2_hidden @ X28 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
        | ( ( k1_funct_1 @ sk_C_2 @ X28 )
          = ( k1_funct_1 @ sk_D @ X28 ) ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( ( k1_funct_1 @ sk_C_2 @ X0 )
          = ( k1_funct_1 @ sk_D @ X0 ) ) )
   <= ( ( sk_A = k1_xboole_0 )
      & ! [X28: $i] :
          ( ~ ( r2_hidden @ X28 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X28 )
            = ( k1_funct_1 @ sk_D @ X28 ) ) ) ) ),
    inference('sup-',[status(thm)],['63','67'])).

thf('69',plain,
    ( ( ( r1_partfun1 @ sk_C_2 @ sk_D )
      | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
        = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) )
   <= ( ( sk_A = k1_xboole_0 )
      & ! [X28: $i] :
          ( ~ ( r2_hidden @ X28 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X28 )
            = ( k1_funct_1 @ sk_D @ X28 ) ) ) ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf('70',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ( ( k1_funct_1 @ X26 @ ( sk_C_1 @ X25 @ X26 ) )
       != ( k1_funct_1 @ X25 @ ( sk_C_1 @ X25 @ X26 ) ) )
      | ( r1_partfun1 @ X26 @ X25 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X26 ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('71',plain,
    ( ( ( ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
       != ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
      | ( r1_partfun1 @ sk_C_2 @ sk_D )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_relat_1 @ sk_D ) )
      | ( r1_partfun1 @ sk_C_2 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) )
   <= ( ( sk_A = k1_xboole_0 )
      & ! [X28: $i] :
          ( ~ ( r2_hidden @ X28 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X28 )
            = ( k1_funct_1 @ sk_D @ X28 ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['47','48'])).

thf('73',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('75',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','25'])).

thf('76',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('77',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['58','59'])).

thf('79',plain,
    ( ( ( ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
       != ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
      | ( r1_partfun1 @ sk_C_2 @ sk_D )
      | ( r1_partfun1 @ sk_C_2 @ sk_D ) )
   <= ( ( sk_A = k1_xboole_0 )
      & ! [X28: $i] :
          ( ~ ( r2_hidden @ X28 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X28 )
            = ( k1_funct_1 @ sk_D @ X28 ) ) ) ) ),
    inference(demod,[status(thm)],['71','72','73','74','75','76','77','78'])).

thf('80',plain,
    ( ( r1_partfun1 @ sk_C_2 @ sk_D )
   <= ( ( sk_A = k1_xboole_0 )
      & ! [X28: $i] :
          ( ~ ( r2_hidden @ X28 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X28 )
            = ( k1_funct_1 @ sk_D @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,
    ( ~ ( r1_partfun1 @ sk_C_2 @ sk_D )
   <= ~ ( r1_partfun1 @ sk_C_2 @ sk_D ) ),
    inference(split,[status(esa)],['6'])).

thf('82',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( r1_partfun1 @ sk_C_2 @ sk_D )
    | ~ ! [X28: $i] :
          ( ~ ( r2_hidden @ X28 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X28 )
            = ( k1_funct_1 @ sk_D @ X28 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
   <= ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('84',plain,
    ( ! [X28: $i] :
        ( ~ ( r2_hidden @ X28 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
        | ( ( k1_funct_1 @ sk_C_2 @ X28 )
          = ( k1_funct_1 @ sk_D @ X28 ) ) )
   <= ! [X28: $i] :
        ( ~ ( r2_hidden @ X28 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
        | ( ( k1_funct_1 @ sk_C_2 @ X28 )
          = ( k1_funct_1 @ sk_D @ X28 ) ) ) ),
    inference(split,[status(esa)],['65'])).

thf('85',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ sk_E )
      = ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
      & ! [X28: $i] :
          ( ~ ( r2_hidden @ X28 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X28 )
            = ( k1_funct_1 @ sk_D @ X28 ) ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( k1_funct_1 @ sk_C_2 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['6'])).

thf('87',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( ( k1_funct_1 @ sk_C_2 @ sk_E )
       != ( k1_funct_1 @ sk_D @ sk_E ) )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
      & ! [X28: $i] :
          ( ~ ( r2_hidden @ X28 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X28 )
            = ( k1_funct_1 @ sk_D @ X28 ) ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ! [X28: $i] :
          ( ~ ( r2_hidden @ X28 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X28 )
            = ( k1_funct_1 @ sk_D @ X28 ) ) )
    | ( ( k1_funct_1 @ sk_C_2 @ sk_E )
      = ( k1_funct_1 @ sk_D @ sk_E ) )
    | ~ ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_2 )
      = ( k1_relat_1 @ sk_C_2 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('90',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('91',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
   <= ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('92',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( ( sk_A = k1_xboole_0 )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relat_1 @ sk_C_2 ) )
   <= ( ( sk_A = k1_xboole_0 )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup+',[status(thm)],['89','92'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('95',plain,
    ( ( r2_hidden @ sk_E @ k1_xboole_0 )
   <= ( ( sk_A = k1_xboole_0 )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( r1_partfun1 @ sk_C_2 @ sk_D )
   <= ( r1_partfun1 @ sk_C_2 @ sk_D ) ),
    inference(split,[status(esa)],['65'])).

thf('97',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','25'])).

thf('98',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('99',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( r1_partfun1 @ X26 @ X25 )
      | ( ( k1_funct_1 @ X26 @ X27 )
        = ( k1_funct_1 @ X25 @ X27 ) )
      | ~ ( r2_hidden @ X27 @ ( k1_relat_1 @ X26 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X26 ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('100',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ sk_C_2 )
        | ~ ( v1_funct_1 @ sk_C_2 )
        | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_2 ) )
        | ( ( k1_funct_1 @ sk_C_2 @ X1 )
          = ( k1_funct_1 @ X0 @ X1 ) )
        | ~ ( r1_partfun1 @ sk_C_2 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['47','48'])).

thf('102',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('104',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
        | ~ ( r2_hidden @ X1 @ k1_xboole_0 )
        | ( ( k1_funct_1 @ sk_C_2 @ X1 )
          = ( k1_funct_1 @ X0 @ X1 ) )
        | ~ ( r1_partfun1 @ sk_C_2 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 )
        | ~ ( v1_relat_1 @ sk_D )
        | ~ ( v1_funct_1 @ sk_D )
        | ~ ( r1_partfun1 @ sk_C_2 @ sk_D )
        | ( ( k1_funct_1 @ sk_C_2 @ X0 )
          = ( k1_funct_1 @ sk_D @ X0 ) )
        | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('107',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['58','59'])).

thf('108',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_partfun1 @ sk_C_2 @ sk_D )
        | ( ( k1_funct_1 @ sk_C_2 @ X0 )
          = ( k1_funct_1 @ sk_D @ X0 ) )
        | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('110',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( ( k1_funct_1 @ sk_C_2 @ X0 )
          = ( k1_funct_1 @ sk_D @ X0 ) ) )
   <= ( ( sk_A = k1_xboole_0 )
      & ( r1_partfun1 @ sk_C_2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['96','109'])).

thf('111',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ sk_E )
      = ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( sk_A = k1_xboole_0 )
      & ( r1_partfun1 @ sk_C_2 @ sk_D )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['95','110'])).

thf('112',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( k1_funct_1 @ sk_C_2 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['6'])).

thf('113',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( ( k1_funct_1 @ sk_C_2 @ sk_E )
       != ( k1_funct_1 @ sk_D @ sk_E ) )
      & ( sk_A = k1_xboole_0 )
      & ( r1_partfun1 @ sk_C_2 @ sk_D )
      & ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( r1_partfun1 @ sk_C_2 @ sk_D )
    | ~ ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
    | ( ( k1_funct_1 @ sk_C_2 @ sk_E )
      = ( k1_funct_1 @ sk_D @ sk_E ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('116',plain,
    ( ( r1_partfun1 @ sk_C_2 @ sk_D )
    | ! [X28: $i] :
        ( ~ ( r2_hidden @ X28 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
        | ( ( k1_funct_1 @ sk_C_2 @ X28 )
          = ( k1_funct_1 @ sk_D @ X28 ) ) ) ),
    inference(split,[status(esa)],['65'])).

thf('117',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('118',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X11 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('120',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('122',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_C_2 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','124'])).

thf('126',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('127',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('130',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('131',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('135',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( sk_B = X1 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','135'])).

thf('137',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('139',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('142',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['139','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B = X0 )
      | ( zip_tseitin_0 @ X0 @ X1 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['136','143'])).

thf('145',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('146',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) )
        | ( zip_tseitin_0 @ X0 @ X1 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ! [X1: $i] :
        ( ( zip_tseitin_0 @ k1_xboole_0 @ X1 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ X0 @ X1 )
        | ( zip_tseitin_0 @ X0 @ X2 )
        | ( sk_A
          = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['129','147'])).

thf('149',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_D ) )
        | ( zip_tseitin_0 @ X1 @ X0 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['148'])).

thf('150',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('151',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['139','142'])).

thf('153',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ( r2_hidden @ ( sk_C_1 @ X25 @ X26 ) @ ( k1_relat_1 @ X26 ) )
      | ( r1_partfun1 @ X26 @ X25 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X26 ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('155',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( r1_partfun1 @ X0 @ sk_D )
        | ( r2_hidden @ ( sk_C_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_funct_1 @ sk_D )
        | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['58','59'])).

thf('158',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ( r1_partfun1 @ X0 @ sk_D )
        | ( r2_hidden @ ( sk_C_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ X0 ) ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,
    ( ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( r1_partfun1 @ sk_C_2 @ sk_D )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['128','158'])).

thf('160',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['47','48'])).

thf('162',plain,
    ( ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( r1_partfun1 @ sk_C_2 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['159','160','161'])).

thf('163',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
        | ( ( k1_funct_1 @ sk_C_2 @ X0 )
          = ( k1_funct_1 @ sk_D @ X0 ) ) )
   <= ! [X28: $i] :
        ( ~ ( r2_hidden @ X28 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
        | ( ( k1_funct_1 @ sk_C_2 @ X28 )
          = ( k1_funct_1 @ sk_D @ X28 ) ) ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('164',plain,
    ( ( ( r1_partfun1 @ sk_C_2 @ sk_D )
      | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
        = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ! [X28: $i] :
          ( ~ ( r2_hidden @ X28 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X28 )
            = ( k1_funct_1 @ sk_D @ X28 ) ) ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ( ( k1_funct_1 @ X26 @ ( sk_C_1 @ X25 @ X26 ) )
       != ( k1_funct_1 @ X25 @ ( sk_C_1 @ X25 @ X26 ) ) )
      | ( r1_partfun1 @ X26 @ X25 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X26 ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('166',plain,
    ( ( ( ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
       != ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
      | ( r1_partfun1 @ sk_C_2 @ sk_D )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_relat_1 @ sk_D ) )
      | ( r1_partfun1 @ sk_C_2 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ! [X28: $i] :
          ( ~ ( r2_hidden @ X28 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X28 )
            = ( k1_funct_1 @ sk_D @ X28 ) ) ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['47','48'])).

thf('168',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('170',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ),
    inference(simplify,[status(thm)],['127'])).

thf('171',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['58','59'])).

thf('173',plain,
    ( ( ( ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
       != ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
      | ( r1_partfun1 @ sk_C_2 @ sk_D )
      | ( r1_partfun1 @ sk_C_2 @ sk_D ) )
   <= ( ( sk_B != k1_xboole_0 )
      & ! [X28: $i] :
          ( ~ ( r2_hidden @ X28 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X28 )
            = ( k1_funct_1 @ sk_D @ X28 ) ) ) ) ),
    inference(demod,[status(thm)],['166','167','168','169','170','171','172'])).

thf('174',plain,
    ( ( r1_partfun1 @ sk_C_2 @ sk_D )
   <= ( ( sk_B != k1_xboole_0 )
      & ! [X28: $i] :
          ( ~ ( r2_hidden @ X28 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X28 )
            = ( k1_funct_1 @ sk_D @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
    ( ~ ( r1_partfun1 @ sk_C_2 @ sk_D )
   <= ~ ( r1_partfun1 @ sk_C_2 @ sk_D ) ),
    inference(split,[status(esa)],['6'])).

thf('176',plain,
    ( ~ ! [X28: $i] :
          ( ~ ( r2_hidden @ X28 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
          | ( ( k1_funct_1 @ sk_C_2 @ X28 )
            = ( k1_funct_1 @ sk_D @ X28 ) ) )
    | ( r1_partfun1 @ sk_C_2 @ sk_D )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ( r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
    | ~ ( r1_partfun1 @ sk_C_2 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('178',plain,(
    r2_hidden @ sk_E @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ),
    inference('sat_resolution*',[status(thm)],['7','82','88','114','115','116','176','177'])).

thf('179',plain,(
    r2_hidden @ sk_E @ ( k1_relat_1 @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['5','178'])).

thf('180',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ),
    inference(simplify,[status(thm)],['127'])).

thf('181',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('182',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( r1_partfun1 @ X26 @ X25 )
      | ( ( k1_funct_1 @ X26 @ X27 )
        = ( k1_funct_1 @ X25 @ X27 ) )
      | ~ ( r2_hidden @ X27 @ ( k1_relat_1 @ X26 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X26 ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t132_partfun1])).

thf('183',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
        | ( ( k1_funct_1 @ X0 @ X1 )
          = ( k1_funct_1 @ sk_D @ X1 ) )
        | ~ ( r1_partfun1 @ X0 @ sk_D )
        | ~ ( v1_funct_1 @ sk_D )
        | ~ ( v1_relat_1 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['58','59'])).

thf('186',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_funct_1 @ X0 )
        | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
        | ( ( k1_funct_1 @ X0 @ X1 )
          = ( k1_funct_1 @ sk_D @ X1 ) )
        | ~ ( r1_partfun1 @ X0 @ sk_D ) )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['116','7','177','82','88','114','115'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
        = ( k1_funct_1 @ sk_D @ X1 ) )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ~ ( r1_partfun1 @ sk_C_2 @ sk_D )
      | ( ( k1_funct_1 @ sk_C_2 @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['180','188'])).

thf('190',plain,
    ( ( r1_partfun1 @ sk_C_2 @ sk_D )
   <= ( r1_partfun1 @ sk_C_2 @ sk_D ) ),
    inference(split,[status(esa)],['65'])).

thf('191',plain,(
    r1_partfun1 @ sk_C_2 @ sk_D ),
    inference('sat_resolution*',[status(thm)],['7','177','82','88','114','115','116','176'])).

thf('192',plain,(
    r1_partfun1 @ sk_C_2 @ sk_D ),
    inference(simpl_trail,[status(thm)],['190','191'])).

thf('193',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['47','48'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['189','192','193','194'])).

thf('196',plain,
    ( ( k1_funct_1 @ sk_C_2 @ sk_E )
    = ( k1_funct_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['179','195'])).

thf('197',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
   <= ( ( k1_funct_1 @ sk_C_2 @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) ) ),
    inference(split,[status(esa)],['6'])).

thf('198',plain,(
    ( k1_funct_1 @ sk_C_2 @ sk_E )
 != ( k1_funct_1 @ sk_D @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['177','82','88','114','115','116','176','7'])).

thf('199',plain,(
    ( k1_funct_1 @ sk_C_2 @ sk_E )
 != ( k1_funct_1 @ sk_D @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['197','198'])).

thf('200',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['196','199'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qCKqthAPfJ
% 0.15/0.37  % Computer   : n016.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 09:29:50 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 10.16/10.36  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 10.16/10.36  % Solved by: fo/fo7.sh
% 10.16/10.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.16/10.36  % done 4545 iterations in 9.869s
% 10.16/10.36  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 10.16/10.36  % SZS output start Refutation
% 10.16/10.36  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.16/10.36  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 10.16/10.36  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 10.16/10.36  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 10.16/10.36  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 10.16/10.36  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 10.16/10.36  thf(sk_E_type, type, sk_E: $i).
% 10.16/10.36  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.16/10.36  thf(sk_B_type, type, sk_B: $i).
% 10.16/10.36  thf(sk_D_type, type, sk_D: $i).
% 10.16/10.36  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 10.16/10.36  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 10.16/10.36  thf(sk_A_type, type, sk_A: $i).
% 10.16/10.36  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 10.16/10.36  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 10.16/10.36  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.16/10.36  thf(sk_C_2_type, type, sk_C_2: $i).
% 10.16/10.36  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.16/10.36  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 10.16/10.36  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 10.16/10.36  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 10.16/10.36  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 10.16/10.36  thf(t145_funct_2, conjecture,
% 10.16/10.36    (![A:$i,B:$i,C:$i]:
% 10.16/10.36     ( ( ( v1_funct_1 @ C ) & 
% 10.16/10.36         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.16/10.36       ( ![D:$i]:
% 10.16/10.36         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 10.16/10.36             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.16/10.36           ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 10.16/10.36             ( ( r1_partfun1 @ C @ D ) <=>
% 10.16/10.36               ( ![E:$i]:
% 10.16/10.36                 ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) ) =>
% 10.16/10.36                   ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ) ))).
% 10.16/10.36  thf(zf_stmt_0, negated_conjecture,
% 10.16/10.36    (~( ![A:$i,B:$i,C:$i]:
% 10.16/10.36        ( ( ( v1_funct_1 @ C ) & 
% 10.16/10.36            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.16/10.36          ( ![D:$i]:
% 10.16/10.36            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 10.16/10.36                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 10.16/10.36              ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 10.16/10.36                ( ( r1_partfun1 @ C @ D ) <=>
% 10.16/10.36                  ( ![E:$i]:
% 10.16/10.36                    ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) ) =>
% 10.16/10.36                      ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ) ) )),
% 10.16/10.36    inference('cnf.neg', [status(esa)], [t145_funct_2])).
% 10.16/10.36  thf('0', plain,
% 10.16/10.36      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 10.16/10.36        | ~ (r1_partfun1 @ sk_C_2 @ sk_D))),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf('1', plain,
% 10.16/10.36      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))
% 10.16/10.36         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 10.16/10.36      inference('split', [status(esa)], ['0'])).
% 10.16/10.36  thf('2', plain,
% 10.16/10.36      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf(redefinition_k1_relset_1, axiom,
% 10.16/10.36    (![A:$i,B:$i,C:$i]:
% 10.16/10.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.16/10.36       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 10.16/10.36  thf('3', plain,
% 10.16/10.36      (![X14 : $i, X15 : $i, X16 : $i]:
% 10.16/10.36         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 10.16/10.36          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 10.16/10.36      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 10.16/10.36  thf('4', plain,
% 10.16/10.36      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 10.16/10.36      inference('sup-', [status(thm)], ['2', '3'])).
% 10.16/10.36  thf('5', plain,
% 10.16/10.36      (((r2_hidden @ sk_E @ (k1_relat_1 @ sk_C_2)))
% 10.16/10.36         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 10.16/10.36      inference('demod', [status(thm)], ['1', '4'])).
% 10.16/10.36  thf('6', plain,
% 10.16/10.36      ((((k1_funct_1 @ sk_C_2 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E))
% 10.16/10.36        | ~ (r1_partfun1 @ sk_C_2 @ sk_D))),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf('7', plain,
% 10.16/10.36      (~ (((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) | 
% 10.16/10.36       ~ ((r1_partfun1 @ sk_C_2 @ sk_D))),
% 10.16/10.36      inference('split', [status(esa)], ['6'])).
% 10.16/10.36  thf('8', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) != (k1_xboole_0)))),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf('9', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('split', [status(esa)], ['8'])).
% 10.16/10.36  thf('10', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf('11', plain,
% 10.16/10.36      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup+', [status(thm)], ['9', '10'])).
% 10.16/10.36  thf(d1_funct_2, axiom,
% 10.16/10.36    (![A:$i,B:$i,C:$i]:
% 10.16/10.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.16/10.36       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 10.16/10.36           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 10.16/10.36             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 10.16/10.36         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 10.16/10.36           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 10.16/10.36             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 10.16/10.36  thf(zf_stmt_1, axiom,
% 10.16/10.36    (![C:$i,B:$i,A:$i]:
% 10.16/10.36     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 10.16/10.36       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 10.16/10.36  thf('12', plain,
% 10.16/10.36      (![X19 : $i, X20 : $i, X21 : $i]:
% 10.16/10.36         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 10.16/10.36          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 10.16/10.36          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_1])).
% 10.16/10.36  thf('13', plain,
% 10.16/10.36      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 10.16/10.36         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['11', '12'])).
% 10.16/10.36  thf('14', plain,
% 10.16/10.36      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('split', [status(esa)], ['8'])).
% 10.16/10.36  thf('15', plain,
% 10.16/10.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf('16', plain,
% 10.16/10.36      (((m1_subset_1 @ sk_D @ 
% 10.16/10.36         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup+', [status(thm)], ['14', '15'])).
% 10.16/10.36  thf('17', plain,
% 10.16/10.36      (![X14 : $i, X15 : $i, X16 : $i]:
% 10.16/10.36         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 10.16/10.36          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 10.16/10.36      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 10.16/10.36  thf('18', plain,
% 10.16/10.36      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D) = (k1_relat_1 @ sk_D)))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['16', '17'])).
% 10.16/10.36  thf('19', plain,
% 10.16/10.36      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 10.16/10.36         | ((k1_xboole_0) = (k1_relat_1 @ sk_D))))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('demod', [status(thm)], ['13', '18'])).
% 10.16/10.36  thf('20', plain,
% 10.16/10.36      (((m1_subset_1 @ sk_D @ 
% 10.16/10.36         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup+', [status(thm)], ['14', '15'])).
% 10.16/10.36  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 10.16/10.36  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 10.16/10.36  thf(zf_stmt_4, axiom,
% 10.16/10.36    (![B:$i,A:$i]:
% 10.16/10.36     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 10.16/10.36       ( zip_tseitin_0 @ B @ A ) ))).
% 10.16/10.36  thf(zf_stmt_5, axiom,
% 10.16/10.36    (![A:$i,B:$i,C:$i]:
% 10.16/10.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.16/10.36       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 10.16/10.36         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 10.16/10.36           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 10.16/10.36             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 10.16/10.36  thf('21', plain,
% 10.16/10.36      (![X22 : $i, X23 : $i, X24 : $i]:
% 10.16/10.36         (~ (zip_tseitin_0 @ X22 @ X23)
% 10.16/10.36          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 10.16/10.36          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_5])).
% 10.16/10.36  thf('22', plain,
% 10.16/10.36      ((((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 10.16/10.36         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['20', '21'])).
% 10.16/10.36  thf('23', plain,
% 10.16/10.36      (![X17 : $i, X18 : $i]:
% 10.16/10.36         ((zip_tseitin_0 @ X17 @ X18) | ((X18) != (k1_xboole_0)))),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_4])).
% 10.16/10.36  thf('24', plain, (![X17 : $i]: (zip_tseitin_0 @ X17 @ k1_xboole_0)),
% 10.16/10.36      inference('simplify', [status(thm)], ['23'])).
% 10.16/10.36  thf('25', plain,
% 10.16/10.36      (((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('demod', [status(thm)], ['22', '24'])).
% 10.16/10.36  thf('26', plain,
% 10.16/10.36      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('demod', [status(thm)], ['19', '25'])).
% 10.16/10.36  thf(d3_tarski, axiom,
% 10.16/10.36    (![A:$i,B:$i]:
% 10.16/10.36     ( ( r1_tarski @ A @ B ) <=>
% 10.16/10.36       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 10.16/10.36  thf('27', plain,
% 10.16/10.36      (![X1 : $i, X3 : $i]:
% 10.16/10.36         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 10.16/10.36      inference('cnf', [status(esa)], [d3_tarski])).
% 10.16/10.36  thf('28', plain,
% 10.16/10.36      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('split', [status(esa)], ['8'])).
% 10.16/10.36  thf('29', plain,
% 10.16/10.36      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf('30', plain,
% 10.16/10.36      (((m1_subset_1 @ sk_C_2 @ 
% 10.16/10.36         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup+', [status(thm)], ['28', '29'])).
% 10.16/10.36  thf(dt_k1_relset_1, axiom,
% 10.16/10.36    (![A:$i,B:$i,C:$i]:
% 10.16/10.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.16/10.36       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 10.16/10.36  thf('31', plain,
% 10.16/10.36      (![X11 : $i, X12 : $i, X13 : $i]:
% 10.16/10.36         ((m1_subset_1 @ (k1_relset_1 @ X11 @ X12 @ X13) @ (k1_zfmisc_1 @ X11))
% 10.16/10.36          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 10.16/10.36      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 10.16/10.36  thf('32', plain,
% 10.16/10.36      (((m1_subset_1 @ (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_2) @ 
% 10.16/10.36         (k1_zfmisc_1 @ k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['30', '31'])).
% 10.16/10.36  thf('33', plain,
% 10.16/10.36      (((m1_subset_1 @ sk_C_2 @ 
% 10.16/10.36         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup+', [status(thm)], ['28', '29'])).
% 10.16/10.36  thf('34', plain,
% 10.16/10.36      (![X14 : $i, X15 : $i, X16 : $i]:
% 10.16/10.36         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 10.16/10.36          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 10.16/10.36      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 10.16/10.36  thf('35', plain,
% 10.16/10.36      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2)))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['33', '34'])).
% 10.16/10.36  thf('36', plain,
% 10.16/10.36      (((m1_subset_1 @ (k1_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ k1_xboole_0)))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('demod', [status(thm)], ['32', '35'])).
% 10.16/10.36  thf(l3_subset_1, axiom,
% 10.16/10.36    (![A:$i,B:$i]:
% 10.16/10.36     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 10.16/10.36       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 10.16/10.36  thf('37', plain,
% 10.16/10.36      (![X5 : $i, X6 : $i, X7 : $i]:
% 10.16/10.36         (~ (r2_hidden @ X5 @ X6)
% 10.16/10.36          | (r2_hidden @ X5 @ X7)
% 10.16/10.36          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 10.16/10.36      inference('cnf', [status(esa)], [l3_subset_1])).
% 10.16/10.36  thf('38', plain,
% 10.16/10.36      ((![X0 : $i]:
% 10.16/10.36          ((r2_hidden @ X0 @ k1_xboole_0)
% 10.16/10.36           | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['36', '37'])).
% 10.16/10.36  thf('39', plain,
% 10.16/10.36      ((![X0 : $i]:
% 10.16/10.36          ((r1_tarski @ (k1_relat_1 @ sk_C_2) @ X0)
% 10.16/10.36           | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_C_2)) @ k1_xboole_0)))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['27', '38'])).
% 10.16/10.36  thf('40', plain,
% 10.16/10.36      (![X1 : $i, X3 : $i]:
% 10.16/10.36         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 10.16/10.36      inference('cnf', [status(esa)], [d3_tarski])).
% 10.16/10.36  thf('41', plain,
% 10.16/10.36      ((((r1_tarski @ (k1_relat_1 @ sk_C_2) @ k1_xboole_0)
% 10.16/10.36         | (r1_tarski @ (k1_relat_1 @ sk_C_2) @ k1_xboole_0)))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['39', '40'])).
% 10.16/10.36  thf('42', plain,
% 10.16/10.36      (((r1_tarski @ (k1_relat_1 @ sk_C_2) @ k1_xboole_0))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('simplify', [status(thm)], ['41'])).
% 10.16/10.36  thf(t3_xboole_1, axiom,
% 10.16/10.36    (![A:$i]:
% 10.16/10.36     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 10.16/10.36  thf('43', plain,
% 10.16/10.36      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 10.16/10.36      inference('cnf', [status(esa)], [t3_xboole_1])).
% 10.16/10.36  thf('44', plain,
% 10.16/10.36      ((((k1_relat_1 @ sk_C_2) = (k1_xboole_0)))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['42', '43'])).
% 10.16/10.36  thf(t132_partfun1, axiom,
% 10.16/10.36    (![A:$i]:
% 10.16/10.36     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 10.16/10.36       ( ![B:$i]:
% 10.16/10.36         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 10.16/10.36           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 10.16/10.36             ( ( r1_partfun1 @ A @ B ) <=>
% 10.16/10.36               ( ![C:$i]:
% 10.16/10.36                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 10.16/10.36                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) ) ) ) ))).
% 10.16/10.36  thf('45', plain,
% 10.16/10.36      (![X25 : $i, X26 : $i]:
% 10.16/10.36         (~ (v1_relat_1 @ X25)
% 10.16/10.36          | ~ (v1_funct_1 @ X25)
% 10.16/10.36          | (r2_hidden @ (sk_C_1 @ X25 @ X26) @ (k1_relat_1 @ X26))
% 10.16/10.36          | (r1_partfun1 @ X26 @ X25)
% 10.16/10.36          | ~ (r1_tarski @ (k1_relat_1 @ X26) @ (k1_relat_1 @ X25))
% 10.16/10.36          | ~ (v1_funct_1 @ X26)
% 10.16/10.36          | ~ (v1_relat_1 @ X26))),
% 10.16/10.36      inference('cnf', [status(esa)], [t132_partfun1])).
% 10.16/10.36  thf('46', plain,
% 10.16/10.36      ((![X0 : $i]:
% 10.16/10.36          (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 10.16/10.36           | ~ (v1_relat_1 @ sk_C_2)
% 10.16/10.36           | ~ (v1_funct_1 @ sk_C_2)
% 10.16/10.36           | (r1_partfun1 @ sk_C_2 @ X0)
% 10.16/10.36           | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 10.16/10.36           | ~ (v1_funct_1 @ X0)
% 10.16/10.36           | ~ (v1_relat_1 @ X0)))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['44', '45'])).
% 10.16/10.36  thf('47', plain,
% 10.16/10.36      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf(cc1_relset_1, axiom,
% 10.16/10.36    (![A:$i,B:$i,C:$i]:
% 10.16/10.36     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.16/10.36       ( v1_relat_1 @ C ) ))).
% 10.16/10.36  thf('48', plain,
% 10.16/10.36      (![X8 : $i, X9 : $i, X10 : $i]:
% 10.16/10.36         ((v1_relat_1 @ X8)
% 10.16/10.36          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 10.16/10.36      inference('cnf', [status(esa)], [cc1_relset_1])).
% 10.16/10.36  thf('49', plain, ((v1_relat_1 @ sk_C_2)),
% 10.16/10.36      inference('sup-', [status(thm)], ['47', '48'])).
% 10.16/10.36  thf('50', plain, ((v1_funct_1 @ sk_C_2)),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf('51', plain,
% 10.16/10.36      ((((k1_relat_1 @ sk_C_2) = (k1_xboole_0)))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['42', '43'])).
% 10.16/10.36  thf('52', plain,
% 10.16/10.36      ((![X0 : $i]:
% 10.16/10.36          (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 10.16/10.36           | (r1_partfun1 @ sk_C_2 @ X0)
% 10.16/10.36           | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ k1_xboole_0)
% 10.16/10.36           | ~ (v1_funct_1 @ X0)
% 10.16/10.36           | ~ (v1_relat_1 @ X0)))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('demod', [status(thm)], ['46', '49', '50', '51'])).
% 10.16/10.36  thf('53', plain,
% 10.16/10.36      (((~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 10.16/10.36         | ~ (v1_relat_1 @ sk_D)
% 10.16/10.36         | ~ (v1_funct_1 @ sk_D)
% 10.16/10.36         | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ k1_xboole_0)
% 10.16/10.36         | (r1_partfun1 @ sk_C_2 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['26', '52'])).
% 10.16/10.36  thf('54', plain,
% 10.16/10.36      (![X1 : $i, X3 : $i]:
% 10.16/10.36         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 10.16/10.36      inference('cnf', [status(esa)], [d3_tarski])).
% 10.16/10.36  thf('55', plain,
% 10.16/10.36      (![X1 : $i, X3 : $i]:
% 10.16/10.36         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 10.16/10.36      inference('cnf', [status(esa)], [d3_tarski])).
% 10.16/10.36  thf('56', plain,
% 10.16/10.36      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 10.16/10.36      inference('sup-', [status(thm)], ['54', '55'])).
% 10.16/10.36  thf('57', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 10.16/10.36      inference('simplify', [status(thm)], ['56'])).
% 10.16/10.36  thf('58', plain,
% 10.16/10.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf('59', plain,
% 10.16/10.36      (![X8 : $i, X9 : $i, X10 : $i]:
% 10.16/10.36         ((v1_relat_1 @ X8)
% 10.16/10.36          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 10.16/10.36      inference('cnf', [status(esa)], [cc1_relset_1])).
% 10.16/10.36  thf('60', plain, ((v1_relat_1 @ sk_D)),
% 10.16/10.36      inference('sup-', [status(thm)], ['58', '59'])).
% 10.16/10.36  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf('62', plain,
% 10.16/10.36      ((((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ k1_xboole_0)
% 10.16/10.36         | (r1_partfun1 @ sk_C_2 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('demod', [status(thm)], ['53', '57', '60', '61'])).
% 10.16/10.36  thf('63', plain,
% 10.16/10.36      ((((k1_relat_1 @ sk_C_2) = (k1_xboole_0)))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['42', '43'])).
% 10.16/10.36  thf('64', plain,
% 10.16/10.36      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 10.16/10.36      inference('sup-', [status(thm)], ['2', '3'])).
% 10.16/10.36  thf('65', plain,
% 10.16/10.36      (![X28 : $i]:
% 10.16/10.36         (~ (r2_hidden @ X28 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 10.16/10.36          | ((k1_funct_1 @ sk_C_2 @ X28) = (k1_funct_1 @ sk_D @ X28))
% 10.16/10.36          | (r1_partfun1 @ sk_C_2 @ sk_D))),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf('66', plain,
% 10.16/10.36      ((![X28 : $i]:
% 10.16/10.36          (~ (r2_hidden @ X28 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 10.16/10.36           | ((k1_funct_1 @ sk_C_2 @ X28) = (k1_funct_1 @ sk_D @ X28))))
% 10.16/10.36         <= ((![X28 : $i]:
% 10.16/10.36                (~ (r2_hidden @ X28 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 10.16/10.36                 | ((k1_funct_1 @ sk_C_2 @ X28) = (k1_funct_1 @ sk_D @ X28)))))),
% 10.16/10.36      inference('split', [status(esa)], ['65'])).
% 10.16/10.36  thf('67', plain,
% 10.16/10.36      ((![X0 : $i]:
% 10.16/10.36          (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 10.16/10.36           | ((k1_funct_1 @ sk_C_2 @ X0) = (k1_funct_1 @ sk_D @ X0))))
% 10.16/10.36         <= ((![X28 : $i]:
% 10.16/10.36                (~ (r2_hidden @ X28 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 10.16/10.36                 | ((k1_funct_1 @ sk_C_2 @ X28) = (k1_funct_1 @ sk_D @ X28)))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['64', '66'])).
% 10.16/10.36  thf('68', plain,
% 10.16/10.36      ((![X0 : $i]:
% 10.16/10.36          (~ (r2_hidden @ X0 @ k1_xboole_0)
% 10.16/10.36           | ((k1_funct_1 @ sk_C_2 @ X0) = (k1_funct_1 @ sk_D @ X0))))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))) & 
% 10.16/10.36             (![X28 : $i]:
% 10.16/10.36                (~ (r2_hidden @ X28 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 10.16/10.36                 | ((k1_funct_1 @ sk_C_2 @ X28) = (k1_funct_1 @ sk_D @ X28)))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['63', '67'])).
% 10.16/10.36  thf('69', plain,
% 10.16/10.36      ((((r1_partfun1 @ sk_C_2 @ sk_D)
% 10.16/10.36         | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 10.16/10.36             = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))) & 
% 10.16/10.36             (![X28 : $i]:
% 10.16/10.36                (~ (r2_hidden @ X28 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 10.16/10.36                 | ((k1_funct_1 @ sk_C_2 @ X28) = (k1_funct_1 @ sk_D @ X28)))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['62', '68'])).
% 10.16/10.36  thf('70', plain,
% 10.16/10.36      (![X25 : $i, X26 : $i]:
% 10.16/10.36         (~ (v1_relat_1 @ X25)
% 10.16/10.36          | ~ (v1_funct_1 @ X25)
% 10.16/10.36          | ((k1_funct_1 @ X26 @ (sk_C_1 @ X25 @ X26))
% 10.16/10.36              != (k1_funct_1 @ X25 @ (sk_C_1 @ X25 @ X26)))
% 10.16/10.36          | (r1_partfun1 @ X26 @ X25)
% 10.16/10.36          | ~ (r1_tarski @ (k1_relat_1 @ X26) @ (k1_relat_1 @ X25))
% 10.16/10.36          | ~ (v1_funct_1 @ X26)
% 10.16/10.36          | ~ (v1_relat_1 @ X26))),
% 10.16/10.36      inference('cnf', [status(esa)], [t132_partfun1])).
% 10.16/10.36  thf('71', plain,
% 10.16/10.36      (((((k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))
% 10.16/10.36           != (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))
% 10.16/10.36         | (r1_partfun1 @ sk_C_2 @ sk_D)
% 10.16/10.36         | ~ (v1_relat_1 @ sk_C_2)
% 10.16/10.36         | ~ (v1_funct_1 @ sk_C_2)
% 10.16/10.36         | ~ (r1_tarski @ (k1_relat_1 @ sk_C_2) @ (k1_relat_1 @ sk_D))
% 10.16/10.36         | (r1_partfun1 @ sk_C_2 @ sk_D)
% 10.16/10.36         | ~ (v1_funct_1 @ sk_D)
% 10.16/10.36         | ~ (v1_relat_1 @ sk_D)))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))) & 
% 10.16/10.36             (![X28 : $i]:
% 10.16/10.36                (~ (r2_hidden @ X28 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 10.16/10.36                 | ((k1_funct_1 @ sk_C_2 @ X28) = (k1_funct_1 @ sk_D @ X28)))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['69', '70'])).
% 10.16/10.36  thf('72', plain, ((v1_relat_1 @ sk_C_2)),
% 10.16/10.36      inference('sup-', [status(thm)], ['47', '48'])).
% 10.16/10.36  thf('73', plain, ((v1_funct_1 @ sk_C_2)),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf('74', plain,
% 10.16/10.36      ((((k1_relat_1 @ sk_C_2) = (k1_xboole_0)))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['42', '43'])).
% 10.16/10.36  thf('75', plain,
% 10.16/10.36      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('demod', [status(thm)], ['19', '25'])).
% 10.16/10.36  thf('76', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 10.16/10.36      inference('simplify', [status(thm)], ['56'])).
% 10.16/10.36  thf('77', plain, ((v1_funct_1 @ sk_D)),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf('78', plain, ((v1_relat_1 @ sk_D)),
% 10.16/10.36      inference('sup-', [status(thm)], ['58', '59'])).
% 10.16/10.36  thf('79', plain,
% 10.16/10.36      (((((k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))
% 10.16/10.36           != (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))
% 10.16/10.36         | (r1_partfun1 @ sk_C_2 @ sk_D)
% 10.16/10.36         | (r1_partfun1 @ sk_C_2 @ sk_D)))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))) & 
% 10.16/10.36             (![X28 : $i]:
% 10.16/10.36                (~ (r2_hidden @ X28 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 10.16/10.36                 | ((k1_funct_1 @ sk_C_2 @ X28) = (k1_funct_1 @ sk_D @ X28)))))),
% 10.16/10.36      inference('demod', [status(thm)],
% 10.16/10.36                ['71', '72', '73', '74', '75', '76', '77', '78'])).
% 10.16/10.36  thf('80', plain,
% 10.16/10.36      (((r1_partfun1 @ sk_C_2 @ sk_D))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))) & 
% 10.16/10.36             (![X28 : $i]:
% 10.16/10.36                (~ (r2_hidden @ X28 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 10.16/10.36                 | ((k1_funct_1 @ sk_C_2 @ X28) = (k1_funct_1 @ sk_D @ X28)))))),
% 10.16/10.36      inference('simplify', [status(thm)], ['79'])).
% 10.16/10.36  thf('81', plain,
% 10.16/10.36      ((~ (r1_partfun1 @ sk_C_2 @ sk_D)) <= (~ ((r1_partfun1 @ sk_C_2 @ sk_D)))),
% 10.16/10.36      inference('split', [status(esa)], ['6'])).
% 10.16/10.36  thf('82', plain,
% 10.16/10.36      (~ (((sk_A) = (k1_xboole_0))) | ((r1_partfun1 @ sk_C_2 @ sk_D)) | 
% 10.16/10.36       ~
% 10.16/10.36       (![X28 : $i]:
% 10.16/10.36          (~ (r2_hidden @ X28 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 10.16/10.36           | ((k1_funct_1 @ sk_C_2 @ X28) = (k1_funct_1 @ sk_D @ X28))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['80', '81'])).
% 10.16/10.36  thf('83', plain,
% 10.16/10.36      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))
% 10.16/10.36         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 10.16/10.36      inference('split', [status(esa)], ['0'])).
% 10.16/10.36  thf('84', plain,
% 10.16/10.36      ((![X28 : $i]:
% 10.16/10.36          (~ (r2_hidden @ X28 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 10.16/10.36           | ((k1_funct_1 @ sk_C_2 @ X28) = (k1_funct_1 @ sk_D @ X28))))
% 10.16/10.36         <= ((![X28 : $i]:
% 10.16/10.36                (~ (r2_hidden @ X28 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 10.16/10.36                 | ((k1_funct_1 @ sk_C_2 @ X28) = (k1_funct_1 @ sk_D @ X28)))))),
% 10.16/10.36      inference('split', [status(esa)], ['65'])).
% 10.16/10.36  thf('85', plain,
% 10.16/10.36      ((((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E)))
% 10.16/10.36         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))) & 
% 10.16/10.36             (![X28 : $i]:
% 10.16/10.36                (~ (r2_hidden @ X28 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 10.16/10.36                 | ((k1_funct_1 @ sk_C_2 @ X28) = (k1_funct_1 @ sk_D @ X28)))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['83', '84'])).
% 10.16/10.36  thf('86', plain,
% 10.16/10.36      ((((k1_funct_1 @ sk_C_2 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 10.16/10.36         <= (~ (((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))))),
% 10.16/10.36      inference('split', [status(esa)], ['6'])).
% 10.16/10.36  thf('87', plain,
% 10.16/10.36      ((((k1_funct_1 @ sk_D @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 10.16/10.36         <= (~ (((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) & 
% 10.16/10.36             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))) & 
% 10.16/10.36             (![X28 : $i]:
% 10.16/10.36                (~ (r2_hidden @ X28 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 10.16/10.36                 | ((k1_funct_1 @ sk_C_2 @ X28) = (k1_funct_1 @ sk_D @ X28)))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['85', '86'])).
% 10.16/10.36  thf('88', plain,
% 10.16/10.36      (~
% 10.16/10.36       (![X28 : $i]:
% 10.16/10.36          (~ (r2_hidden @ X28 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 10.16/10.36           | ((k1_funct_1 @ sk_C_2 @ X28) = (k1_funct_1 @ sk_D @ X28)))) | 
% 10.16/10.36       (((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) | 
% 10.16/10.36       ~ ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 10.16/10.36      inference('simplify', [status(thm)], ['87'])).
% 10.16/10.36  thf('89', plain,
% 10.16/10.36      ((((k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2)))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['33', '34'])).
% 10.16/10.36  thf('90', plain,
% 10.16/10.36      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('split', [status(esa)], ['8'])).
% 10.16/10.36  thf('91', plain,
% 10.16/10.36      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))
% 10.16/10.36         <= (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 10.16/10.36      inference('split', [status(esa)], ['0'])).
% 10.16/10.36  thf('92', plain,
% 10.16/10.36      (((r2_hidden @ sk_E @ (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_C_2)))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))) & 
% 10.16/10.36             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 10.16/10.36      inference('sup+', [status(thm)], ['90', '91'])).
% 10.16/10.36  thf('93', plain,
% 10.16/10.36      (((r2_hidden @ sk_E @ (k1_relat_1 @ sk_C_2)))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))) & 
% 10.16/10.36             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 10.16/10.36      inference('sup+', [status(thm)], ['89', '92'])).
% 10.16/10.36  thf('94', plain,
% 10.16/10.36      ((![X0 : $i]:
% 10.16/10.36          ((r2_hidden @ X0 @ k1_xboole_0)
% 10.16/10.36           | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['36', '37'])).
% 10.16/10.36  thf('95', plain,
% 10.16/10.36      (((r2_hidden @ sk_E @ k1_xboole_0))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))) & 
% 10.16/10.36             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['93', '94'])).
% 10.16/10.36  thf('96', plain,
% 10.16/10.36      (((r1_partfun1 @ sk_C_2 @ sk_D)) <= (((r1_partfun1 @ sk_C_2 @ sk_D)))),
% 10.16/10.36      inference('split', [status(esa)], ['65'])).
% 10.16/10.36  thf('97', plain,
% 10.16/10.36      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('demod', [status(thm)], ['19', '25'])).
% 10.16/10.36  thf('98', plain,
% 10.16/10.36      ((((k1_relat_1 @ sk_C_2) = (k1_xboole_0)))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['42', '43'])).
% 10.16/10.36  thf('99', plain,
% 10.16/10.36      (![X25 : $i, X26 : $i, X27 : $i]:
% 10.16/10.36         (~ (v1_relat_1 @ X25)
% 10.16/10.36          | ~ (v1_funct_1 @ X25)
% 10.16/10.36          | ~ (r1_partfun1 @ X26 @ X25)
% 10.16/10.36          | ((k1_funct_1 @ X26 @ X27) = (k1_funct_1 @ X25 @ X27))
% 10.16/10.36          | ~ (r2_hidden @ X27 @ (k1_relat_1 @ X26))
% 10.16/10.36          | ~ (r1_tarski @ (k1_relat_1 @ X26) @ (k1_relat_1 @ X25))
% 10.16/10.36          | ~ (v1_funct_1 @ X26)
% 10.16/10.36          | ~ (v1_relat_1 @ X26))),
% 10.16/10.36      inference('cnf', [status(esa)], [t132_partfun1])).
% 10.16/10.36  thf('100', plain,
% 10.16/10.36      ((![X0 : $i, X1 : $i]:
% 10.16/10.36          (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 10.16/10.36           | ~ (v1_relat_1 @ sk_C_2)
% 10.16/10.36           | ~ (v1_funct_1 @ sk_C_2)
% 10.16/10.36           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_2))
% 10.16/10.36           | ((k1_funct_1 @ sk_C_2 @ X1) = (k1_funct_1 @ X0 @ X1))
% 10.16/10.36           | ~ (r1_partfun1 @ sk_C_2 @ X0)
% 10.16/10.36           | ~ (v1_funct_1 @ X0)
% 10.16/10.36           | ~ (v1_relat_1 @ X0)))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['98', '99'])).
% 10.16/10.36  thf('101', plain, ((v1_relat_1 @ sk_C_2)),
% 10.16/10.36      inference('sup-', [status(thm)], ['47', '48'])).
% 10.16/10.36  thf('102', plain, ((v1_funct_1 @ sk_C_2)),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf('103', plain,
% 10.16/10.36      ((((k1_relat_1 @ sk_C_2) = (k1_xboole_0)))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['42', '43'])).
% 10.16/10.36  thf('104', plain,
% 10.16/10.36      ((![X0 : $i, X1 : $i]:
% 10.16/10.36          (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 10.16/10.36           | ~ (r2_hidden @ X1 @ k1_xboole_0)
% 10.16/10.36           | ((k1_funct_1 @ sk_C_2 @ X1) = (k1_funct_1 @ X0 @ X1))
% 10.16/10.36           | ~ (r1_partfun1 @ sk_C_2 @ X0)
% 10.16/10.36           | ~ (v1_funct_1 @ X0)
% 10.16/10.36           | ~ (v1_relat_1 @ X0)))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 10.16/10.36  thf('105', plain,
% 10.16/10.36      ((![X0 : $i]:
% 10.16/10.36          (~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0)
% 10.16/10.36           | ~ (v1_relat_1 @ sk_D)
% 10.16/10.36           | ~ (v1_funct_1 @ sk_D)
% 10.16/10.36           | ~ (r1_partfun1 @ sk_C_2 @ sk_D)
% 10.16/10.36           | ((k1_funct_1 @ sk_C_2 @ X0) = (k1_funct_1 @ sk_D @ X0))
% 10.16/10.36           | ~ (r2_hidden @ X0 @ k1_xboole_0)))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['97', '104'])).
% 10.16/10.36  thf('106', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 10.16/10.36      inference('simplify', [status(thm)], ['56'])).
% 10.16/10.36  thf('107', plain, ((v1_relat_1 @ sk_D)),
% 10.16/10.36      inference('sup-', [status(thm)], ['58', '59'])).
% 10.16/10.36  thf('108', plain, ((v1_funct_1 @ sk_D)),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf('109', plain,
% 10.16/10.36      ((![X0 : $i]:
% 10.16/10.36          (~ (r1_partfun1 @ sk_C_2 @ sk_D)
% 10.16/10.36           | ((k1_funct_1 @ sk_C_2 @ X0) = (k1_funct_1 @ sk_D @ X0))
% 10.16/10.36           | ~ (r2_hidden @ X0 @ k1_xboole_0)))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))))),
% 10.16/10.36      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 10.16/10.36  thf('110', plain,
% 10.16/10.36      ((![X0 : $i]:
% 10.16/10.36          (~ (r2_hidden @ X0 @ k1_xboole_0)
% 10.16/10.36           | ((k1_funct_1 @ sk_C_2 @ X0) = (k1_funct_1 @ sk_D @ X0))))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))) & ((r1_partfun1 @ sk_C_2 @ sk_D)))),
% 10.16/10.36      inference('sup-', [status(thm)], ['96', '109'])).
% 10.16/10.36  thf('111', plain,
% 10.16/10.36      ((((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E)))
% 10.16/10.36         <= ((((sk_A) = (k1_xboole_0))) & 
% 10.16/10.36             ((r1_partfun1 @ sk_C_2 @ sk_D)) & 
% 10.16/10.36             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['95', '110'])).
% 10.16/10.36  thf('112', plain,
% 10.16/10.36      ((((k1_funct_1 @ sk_C_2 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 10.16/10.36         <= (~ (((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))))),
% 10.16/10.36      inference('split', [status(esa)], ['6'])).
% 10.16/10.36  thf('113', plain,
% 10.16/10.36      ((((k1_funct_1 @ sk_D @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 10.16/10.36         <= (~ (((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))) & 
% 10.16/10.36             (((sk_A) = (k1_xboole_0))) & 
% 10.16/10.36             ((r1_partfun1 @ sk_C_2 @ sk_D)) & 
% 10.16/10.36             ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['111', '112'])).
% 10.16/10.36  thf('114', plain,
% 10.16/10.36      (~ (((sk_A) = (k1_xboole_0))) | ~ ((r1_partfun1 @ sk_C_2 @ sk_D)) | 
% 10.16/10.36       ~ ((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))) | 
% 10.16/10.36       (((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E)))),
% 10.16/10.36      inference('simplify', [status(thm)], ['113'])).
% 10.16/10.36  thf('115', plain,
% 10.16/10.36      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 10.16/10.36      inference('split', [status(esa)], ['8'])).
% 10.16/10.36  thf('116', plain,
% 10.16/10.36      (((r1_partfun1 @ sk_C_2 @ sk_D)) | 
% 10.16/10.36       (![X28 : $i]:
% 10.16/10.36          (~ (r2_hidden @ X28 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 10.16/10.36           | ((k1_funct_1 @ sk_C_2 @ X28) = (k1_funct_1 @ sk_D @ X28))))),
% 10.16/10.36      inference('split', [status(esa)], ['65'])).
% 10.16/10.36  thf('117', plain,
% 10.16/10.36      (![X1 : $i, X3 : $i]:
% 10.16/10.36         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 10.16/10.36      inference('cnf', [status(esa)], [d3_tarski])).
% 10.16/10.36  thf('118', plain,
% 10.16/10.36      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf('119', plain,
% 10.16/10.36      (![X11 : $i, X12 : $i, X13 : $i]:
% 10.16/10.36         ((m1_subset_1 @ (k1_relset_1 @ X11 @ X12 @ X13) @ (k1_zfmisc_1 @ X11))
% 10.16/10.36          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 10.16/10.36      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 10.16/10.36  thf('120', plain,
% 10.16/10.36      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2) @ 
% 10.16/10.36        (k1_zfmisc_1 @ sk_A))),
% 10.16/10.36      inference('sup-', [status(thm)], ['118', '119'])).
% 10.16/10.36  thf('121', plain,
% 10.16/10.36      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 10.16/10.36      inference('sup-', [status(thm)], ['2', '3'])).
% 10.16/10.36  thf('122', plain,
% 10.16/10.36      ((m1_subset_1 @ (k1_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_A))),
% 10.16/10.36      inference('demod', [status(thm)], ['120', '121'])).
% 10.16/10.36  thf('123', plain,
% 10.16/10.36      (![X5 : $i, X6 : $i, X7 : $i]:
% 10.16/10.36         (~ (r2_hidden @ X5 @ X6)
% 10.16/10.36          | (r2_hidden @ X5 @ X7)
% 10.16/10.36          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 10.16/10.36      inference('cnf', [status(esa)], [l3_subset_1])).
% 10.16/10.36  thf('124', plain,
% 10.16/10.36      (![X0 : $i]:
% 10.16/10.36         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2)))),
% 10.16/10.36      inference('sup-', [status(thm)], ['122', '123'])).
% 10.16/10.36  thf('125', plain,
% 10.16/10.36      (![X0 : $i]:
% 10.16/10.36         ((r1_tarski @ (k1_relat_1 @ sk_C_2) @ X0)
% 10.16/10.36          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_C_2)) @ sk_A))),
% 10.16/10.36      inference('sup-', [status(thm)], ['117', '124'])).
% 10.16/10.36  thf('126', plain,
% 10.16/10.36      (![X1 : $i, X3 : $i]:
% 10.16/10.36         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 10.16/10.36      inference('cnf', [status(esa)], [d3_tarski])).
% 10.16/10.36  thf('127', plain,
% 10.16/10.36      (((r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_A)
% 10.16/10.36        | (r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_A))),
% 10.16/10.36      inference('sup-', [status(thm)], ['125', '126'])).
% 10.16/10.36  thf('128', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_A)),
% 10.16/10.36      inference('simplify', [status(thm)], ['127'])).
% 10.16/10.36  thf('129', plain,
% 10.16/10.36      (![X17 : $i, X18 : $i]:
% 10.16/10.36         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_4])).
% 10.16/10.36  thf('130', plain,
% 10.16/10.36      (![X17 : $i, X18 : $i]:
% 10.16/10.36         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_4])).
% 10.16/10.36  thf('131', plain,
% 10.16/10.36      (![X17 : $i, X18 : $i]:
% 10.16/10.36         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_4])).
% 10.16/10.36  thf('132', plain,
% 10.16/10.36      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 10.16/10.36         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X3) | (zip_tseitin_0 @ X1 @ X2))),
% 10.16/10.36      inference('sup+', [status(thm)], ['130', '131'])).
% 10.16/10.36  thf('133', plain,
% 10.16/10.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf('134', plain,
% 10.16/10.36      (![X22 : $i, X23 : $i, X24 : $i]:
% 10.16/10.36         (~ (zip_tseitin_0 @ X22 @ X23)
% 10.16/10.36          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 10.16/10.36          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_5])).
% 10.16/10.36  thf('135', plain,
% 10.16/10.36      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 10.16/10.36      inference('sup-', [status(thm)], ['133', '134'])).
% 10.16/10.36  thf('136', plain,
% 10.16/10.36      (![X0 : $i, X1 : $i]:
% 10.16/10.36         ((zip_tseitin_0 @ X1 @ X0)
% 10.16/10.36          | ((sk_B) = (X1))
% 10.16/10.36          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 10.16/10.36      inference('sup-', [status(thm)], ['132', '135'])).
% 10.16/10.36  thf('137', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf('138', plain,
% 10.16/10.36      (![X19 : $i, X20 : $i, X21 : $i]:
% 10.16/10.36         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 10.16/10.36          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 10.16/10.36          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_1])).
% 10.16/10.36  thf('139', plain,
% 10.16/10.36      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 10.16/10.36        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 10.16/10.36      inference('sup-', [status(thm)], ['137', '138'])).
% 10.16/10.36  thf('140', plain,
% 10.16/10.36      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf('141', plain,
% 10.16/10.36      (![X14 : $i, X15 : $i, X16 : $i]:
% 10.16/10.36         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 10.16/10.36          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 10.16/10.36      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 10.16/10.36  thf('142', plain,
% 10.16/10.36      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 10.16/10.36      inference('sup-', [status(thm)], ['140', '141'])).
% 10.16/10.36  thf('143', plain,
% 10.16/10.36      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 10.16/10.36      inference('demod', [status(thm)], ['139', '142'])).
% 10.16/10.36  thf('144', plain,
% 10.16/10.36      (![X0 : $i, X1 : $i]:
% 10.16/10.36         (((sk_B) = (X0))
% 10.16/10.36          | (zip_tseitin_0 @ X0 @ X1)
% 10.16/10.36          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 10.16/10.36      inference('sup-', [status(thm)], ['136', '143'])).
% 10.16/10.36  thf('145', plain,
% 10.16/10.36      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 10.16/10.36      inference('split', [status(esa)], ['8'])).
% 10.16/10.36  thf('146', plain,
% 10.16/10.36      ((![X0 : $i, X1 : $i]:
% 10.16/10.36          (((X0) != (k1_xboole_0))
% 10.16/10.36           | ((sk_A) = (k1_relat_1 @ sk_D))
% 10.16/10.36           | (zip_tseitin_0 @ X0 @ X1)))
% 10.16/10.36         <= (~ (((sk_B) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['144', '145'])).
% 10.16/10.36  thf('147', plain,
% 10.16/10.36      ((![X1 : $i]:
% 10.16/10.36          ((zip_tseitin_0 @ k1_xboole_0 @ X1) | ((sk_A) = (k1_relat_1 @ sk_D))))
% 10.16/10.36         <= (~ (((sk_B) = (k1_xboole_0))))),
% 10.16/10.36      inference('simplify', [status(thm)], ['146'])).
% 10.16/10.36  thf('148', plain,
% 10.16/10.36      ((![X0 : $i, X1 : $i, X2 : $i]:
% 10.16/10.36          ((zip_tseitin_0 @ X0 @ X1)
% 10.16/10.36           | (zip_tseitin_0 @ X0 @ X2)
% 10.16/10.36           | ((sk_A) = (k1_relat_1 @ sk_D))))
% 10.16/10.36         <= (~ (((sk_B) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup+', [status(thm)], ['129', '147'])).
% 10.16/10.36  thf('149', plain,
% 10.16/10.36      ((![X0 : $i, X1 : $i]:
% 10.16/10.36          (((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_0 @ X1 @ X0)))
% 10.16/10.36         <= (~ (((sk_B) = (k1_xboole_0))))),
% 10.16/10.36      inference('condensation', [status(thm)], ['148'])).
% 10.16/10.36  thf('150', plain,
% 10.16/10.36      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 10.16/10.36      inference('sup-', [status(thm)], ['133', '134'])).
% 10.16/10.36  thf('151', plain,
% 10.16/10.36      (((((sk_A) = (k1_relat_1 @ sk_D)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)))
% 10.16/10.36         <= (~ (((sk_B) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['149', '150'])).
% 10.16/10.36  thf('152', plain,
% 10.16/10.36      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 10.16/10.36      inference('demod', [status(thm)], ['139', '142'])).
% 10.16/10.36  thf('153', plain,
% 10.16/10.36      ((((sk_A) = (k1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 10.16/10.36      inference('clc', [status(thm)], ['151', '152'])).
% 10.16/10.36  thf('154', plain,
% 10.16/10.36      (![X25 : $i, X26 : $i]:
% 10.16/10.36         (~ (v1_relat_1 @ X25)
% 10.16/10.36          | ~ (v1_funct_1 @ X25)
% 10.16/10.36          | (r2_hidden @ (sk_C_1 @ X25 @ X26) @ (k1_relat_1 @ X26))
% 10.16/10.36          | (r1_partfun1 @ X26 @ X25)
% 10.16/10.36          | ~ (r1_tarski @ (k1_relat_1 @ X26) @ (k1_relat_1 @ X25))
% 10.16/10.36          | ~ (v1_funct_1 @ X26)
% 10.16/10.36          | ~ (v1_relat_1 @ X26))),
% 10.16/10.36      inference('cnf', [status(esa)], [t132_partfun1])).
% 10.16/10.36  thf('155', plain,
% 10.16/10.36      ((![X0 : $i]:
% 10.16/10.36          (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 10.16/10.36           | ~ (v1_relat_1 @ X0)
% 10.16/10.36           | ~ (v1_funct_1 @ X0)
% 10.16/10.36           | (r1_partfun1 @ X0 @ sk_D)
% 10.16/10.36           | (r2_hidden @ (sk_C_1 @ sk_D @ X0) @ (k1_relat_1 @ X0))
% 10.16/10.36           | ~ (v1_funct_1 @ sk_D)
% 10.16/10.36           | ~ (v1_relat_1 @ sk_D)))
% 10.16/10.36         <= (~ (((sk_B) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['153', '154'])).
% 10.16/10.36  thf('156', plain, ((v1_funct_1 @ sk_D)),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf('157', plain, ((v1_relat_1 @ sk_D)),
% 10.16/10.36      inference('sup-', [status(thm)], ['58', '59'])).
% 10.16/10.36  thf('158', plain,
% 10.16/10.36      ((![X0 : $i]:
% 10.16/10.36          (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 10.16/10.36           | ~ (v1_relat_1 @ X0)
% 10.16/10.36           | ~ (v1_funct_1 @ X0)
% 10.16/10.36           | (r1_partfun1 @ X0 @ sk_D)
% 10.16/10.36           | (r2_hidden @ (sk_C_1 @ sk_D @ X0) @ (k1_relat_1 @ X0))))
% 10.16/10.36         <= (~ (((sk_B) = (k1_xboole_0))))),
% 10.16/10.36      inference('demod', [status(thm)], ['155', '156', '157'])).
% 10.16/10.36  thf('159', plain,
% 10.16/10.36      ((((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 10.16/10.36         | (r1_partfun1 @ sk_C_2 @ sk_D)
% 10.16/10.36         | ~ (v1_funct_1 @ sk_C_2)
% 10.16/10.36         | ~ (v1_relat_1 @ sk_C_2))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['128', '158'])).
% 10.16/10.36  thf('160', plain, ((v1_funct_1 @ sk_C_2)),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf('161', plain, ((v1_relat_1 @ sk_C_2)),
% 10.16/10.36      inference('sup-', [status(thm)], ['47', '48'])).
% 10.16/10.36  thf('162', plain,
% 10.16/10.36      ((((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 10.16/10.36         | (r1_partfun1 @ sk_C_2 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 10.16/10.36      inference('demod', [status(thm)], ['159', '160', '161'])).
% 10.16/10.36  thf('163', plain,
% 10.16/10.36      ((![X0 : $i]:
% 10.16/10.36          (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 10.16/10.36           | ((k1_funct_1 @ sk_C_2 @ X0) = (k1_funct_1 @ sk_D @ X0))))
% 10.16/10.36         <= ((![X28 : $i]:
% 10.16/10.36                (~ (r2_hidden @ X28 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 10.16/10.36                 | ((k1_funct_1 @ sk_C_2 @ X28) = (k1_funct_1 @ sk_D @ X28)))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['64', '66'])).
% 10.16/10.36  thf('164', plain,
% 10.16/10.36      ((((r1_partfun1 @ sk_C_2 @ sk_D)
% 10.16/10.36         | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 10.16/10.36             = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))))
% 10.16/10.36         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 10.16/10.36             (![X28 : $i]:
% 10.16/10.36                (~ (r2_hidden @ X28 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 10.16/10.36                 | ((k1_funct_1 @ sk_C_2 @ X28) = (k1_funct_1 @ sk_D @ X28)))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['162', '163'])).
% 10.16/10.36  thf('165', plain,
% 10.16/10.36      (![X25 : $i, X26 : $i]:
% 10.16/10.36         (~ (v1_relat_1 @ X25)
% 10.16/10.36          | ~ (v1_funct_1 @ X25)
% 10.16/10.36          | ((k1_funct_1 @ X26 @ (sk_C_1 @ X25 @ X26))
% 10.16/10.36              != (k1_funct_1 @ X25 @ (sk_C_1 @ X25 @ X26)))
% 10.16/10.36          | (r1_partfun1 @ X26 @ X25)
% 10.16/10.36          | ~ (r1_tarski @ (k1_relat_1 @ X26) @ (k1_relat_1 @ X25))
% 10.16/10.36          | ~ (v1_funct_1 @ X26)
% 10.16/10.36          | ~ (v1_relat_1 @ X26))),
% 10.16/10.36      inference('cnf', [status(esa)], [t132_partfun1])).
% 10.16/10.36  thf('166', plain,
% 10.16/10.36      (((((k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))
% 10.16/10.36           != (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))
% 10.16/10.36         | (r1_partfun1 @ sk_C_2 @ sk_D)
% 10.16/10.36         | ~ (v1_relat_1 @ sk_C_2)
% 10.16/10.36         | ~ (v1_funct_1 @ sk_C_2)
% 10.16/10.36         | ~ (r1_tarski @ (k1_relat_1 @ sk_C_2) @ (k1_relat_1 @ sk_D))
% 10.16/10.36         | (r1_partfun1 @ sk_C_2 @ sk_D)
% 10.16/10.36         | ~ (v1_funct_1 @ sk_D)
% 10.16/10.36         | ~ (v1_relat_1 @ sk_D)))
% 10.16/10.36         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 10.16/10.36             (![X28 : $i]:
% 10.16/10.36                (~ (r2_hidden @ X28 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 10.16/10.36                 | ((k1_funct_1 @ sk_C_2 @ X28) = (k1_funct_1 @ sk_D @ X28)))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['164', '165'])).
% 10.16/10.36  thf('167', plain, ((v1_relat_1 @ sk_C_2)),
% 10.16/10.36      inference('sup-', [status(thm)], ['47', '48'])).
% 10.16/10.36  thf('168', plain, ((v1_funct_1 @ sk_C_2)),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf('169', plain,
% 10.16/10.36      ((((sk_A) = (k1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 10.16/10.36      inference('clc', [status(thm)], ['151', '152'])).
% 10.16/10.36  thf('170', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_A)),
% 10.16/10.36      inference('simplify', [status(thm)], ['127'])).
% 10.16/10.36  thf('171', plain, ((v1_funct_1 @ sk_D)),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf('172', plain, ((v1_relat_1 @ sk_D)),
% 10.16/10.36      inference('sup-', [status(thm)], ['58', '59'])).
% 10.16/10.36  thf('173', plain,
% 10.16/10.36      (((((k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))
% 10.16/10.36           != (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))
% 10.16/10.36         | (r1_partfun1 @ sk_C_2 @ sk_D)
% 10.16/10.36         | (r1_partfun1 @ sk_C_2 @ sk_D)))
% 10.16/10.36         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 10.16/10.36             (![X28 : $i]:
% 10.16/10.36                (~ (r2_hidden @ X28 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 10.16/10.36                 | ((k1_funct_1 @ sk_C_2 @ X28) = (k1_funct_1 @ sk_D @ X28)))))),
% 10.16/10.36      inference('demod', [status(thm)],
% 10.16/10.36                ['166', '167', '168', '169', '170', '171', '172'])).
% 10.16/10.36  thf('174', plain,
% 10.16/10.36      (((r1_partfun1 @ sk_C_2 @ sk_D))
% 10.16/10.36         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 10.16/10.36             (![X28 : $i]:
% 10.16/10.36                (~ (r2_hidden @ X28 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 10.16/10.36                 | ((k1_funct_1 @ sk_C_2 @ X28) = (k1_funct_1 @ sk_D @ X28)))))),
% 10.16/10.36      inference('simplify', [status(thm)], ['173'])).
% 10.16/10.36  thf('175', plain,
% 10.16/10.36      ((~ (r1_partfun1 @ sk_C_2 @ sk_D)) <= (~ ((r1_partfun1 @ sk_C_2 @ sk_D)))),
% 10.16/10.36      inference('split', [status(esa)], ['6'])).
% 10.16/10.36  thf('176', plain,
% 10.16/10.36      (~
% 10.16/10.36       (![X28 : $i]:
% 10.16/10.36          (~ (r2_hidden @ X28 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 10.16/10.36           | ((k1_funct_1 @ sk_C_2 @ X28) = (k1_funct_1 @ sk_D @ X28)))) | 
% 10.16/10.36       ((r1_partfun1 @ sk_C_2 @ sk_D)) | (((sk_B) = (k1_xboole_0)))),
% 10.16/10.36      inference('sup-', [status(thm)], ['174', '175'])).
% 10.16/10.36  thf('177', plain,
% 10.16/10.36      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2))) | 
% 10.16/10.36       ~ ((r1_partfun1 @ sk_C_2 @ sk_D))),
% 10.16/10.36      inference('split', [status(esa)], ['0'])).
% 10.16/10.36  thf('178', plain,
% 10.16/10.36      (((r2_hidden @ sk_E @ (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 10.16/10.36      inference('sat_resolution*', [status(thm)],
% 10.16/10.36                ['7', '82', '88', '114', '115', '116', '176', '177'])).
% 10.16/10.36  thf('179', plain, ((r2_hidden @ sk_E @ (k1_relat_1 @ sk_C_2))),
% 10.16/10.36      inference('simpl_trail', [status(thm)], ['5', '178'])).
% 10.16/10.36  thf('180', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_A)),
% 10.16/10.36      inference('simplify', [status(thm)], ['127'])).
% 10.16/10.36  thf('181', plain,
% 10.16/10.36      ((((sk_A) = (k1_relat_1 @ sk_D))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 10.16/10.36      inference('clc', [status(thm)], ['151', '152'])).
% 10.16/10.36  thf('182', plain,
% 10.16/10.36      (![X25 : $i, X26 : $i, X27 : $i]:
% 10.16/10.36         (~ (v1_relat_1 @ X25)
% 10.16/10.36          | ~ (v1_funct_1 @ X25)
% 10.16/10.36          | ~ (r1_partfun1 @ X26 @ X25)
% 10.16/10.36          | ((k1_funct_1 @ X26 @ X27) = (k1_funct_1 @ X25 @ X27))
% 10.16/10.36          | ~ (r2_hidden @ X27 @ (k1_relat_1 @ X26))
% 10.16/10.36          | ~ (r1_tarski @ (k1_relat_1 @ X26) @ (k1_relat_1 @ X25))
% 10.16/10.36          | ~ (v1_funct_1 @ X26)
% 10.16/10.36          | ~ (v1_relat_1 @ X26))),
% 10.16/10.36      inference('cnf', [status(esa)], [t132_partfun1])).
% 10.16/10.36  thf('183', plain,
% 10.16/10.36      ((![X0 : $i, X1 : $i]:
% 10.16/10.36          (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 10.16/10.36           | ~ (v1_relat_1 @ X0)
% 10.16/10.36           | ~ (v1_funct_1 @ X0)
% 10.16/10.36           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 10.16/10.36           | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 10.16/10.36           | ~ (r1_partfun1 @ X0 @ sk_D)
% 10.16/10.36           | ~ (v1_funct_1 @ sk_D)
% 10.16/10.36           | ~ (v1_relat_1 @ sk_D)))
% 10.16/10.36         <= (~ (((sk_B) = (k1_xboole_0))))),
% 10.16/10.36      inference('sup-', [status(thm)], ['181', '182'])).
% 10.16/10.36  thf('184', plain, ((v1_funct_1 @ sk_D)),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf('185', plain, ((v1_relat_1 @ sk_D)),
% 10.16/10.36      inference('sup-', [status(thm)], ['58', '59'])).
% 10.16/10.36  thf('186', plain,
% 10.16/10.36      ((![X0 : $i, X1 : $i]:
% 10.16/10.36          (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 10.16/10.36           | ~ (v1_relat_1 @ X0)
% 10.16/10.36           | ~ (v1_funct_1 @ X0)
% 10.16/10.36           | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 10.16/10.36           | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 10.16/10.36           | ~ (r1_partfun1 @ X0 @ sk_D)))
% 10.16/10.36         <= (~ (((sk_B) = (k1_xboole_0))))),
% 10.16/10.36      inference('demod', [status(thm)], ['183', '184', '185'])).
% 10.16/10.36  thf('187', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 10.16/10.36      inference('sat_resolution*', [status(thm)],
% 10.16/10.36                ['116', '7', '177', '82', '88', '114', '115'])).
% 10.16/10.36  thf('188', plain,
% 10.16/10.36      (![X0 : $i, X1 : $i]:
% 10.16/10.36         (~ (r1_tarski @ (k1_relat_1 @ X0) @ sk_A)
% 10.16/10.36          | ~ (v1_relat_1 @ X0)
% 10.16/10.36          | ~ (v1_funct_1 @ X0)
% 10.16/10.36          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 10.16/10.36          | ((k1_funct_1 @ X0 @ X1) = (k1_funct_1 @ sk_D @ X1))
% 10.16/10.36          | ~ (r1_partfun1 @ X0 @ sk_D))),
% 10.16/10.36      inference('simpl_trail', [status(thm)], ['186', '187'])).
% 10.16/10.36  thf('189', plain,
% 10.16/10.36      (![X0 : $i]:
% 10.16/10.36         (~ (r1_partfun1 @ sk_C_2 @ sk_D)
% 10.16/10.36          | ((k1_funct_1 @ sk_C_2 @ X0) = (k1_funct_1 @ sk_D @ X0))
% 10.16/10.36          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 10.16/10.36          | ~ (v1_funct_1 @ sk_C_2)
% 10.16/10.36          | ~ (v1_relat_1 @ sk_C_2))),
% 10.16/10.36      inference('sup-', [status(thm)], ['180', '188'])).
% 10.16/10.36  thf('190', plain,
% 10.16/10.36      (((r1_partfun1 @ sk_C_2 @ sk_D)) <= (((r1_partfun1 @ sk_C_2 @ sk_D)))),
% 10.16/10.36      inference('split', [status(esa)], ['65'])).
% 10.16/10.36  thf('191', plain, (((r1_partfun1 @ sk_C_2 @ sk_D))),
% 10.16/10.36      inference('sat_resolution*', [status(thm)],
% 10.16/10.36                ['7', '177', '82', '88', '114', '115', '116', '176'])).
% 10.16/10.36  thf('192', plain, ((r1_partfun1 @ sk_C_2 @ sk_D)),
% 10.16/10.36      inference('simpl_trail', [status(thm)], ['190', '191'])).
% 10.16/10.36  thf('193', plain, ((v1_funct_1 @ sk_C_2)),
% 10.16/10.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.16/10.36  thf('194', plain, ((v1_relat_1 @ sk_C_2)),
% 10.16/10.36      inference('sup-', [status(thm)], ['47', '48'])).
% 10.16/10.36  thf('195', plain,
% 10.16/10.36      (![X0 : $i]:
% 10.16/10.36         (((k1_funct_1 @ sk_C_2 @ X0) = (k1_funct_1 @ sk_D @ X0))
% 10.16/10.36          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2)))),
% 10.16/10.36      inference('demod', [status(thm)], ['189', '192', '193', '194'])).
% 10.16/10.36  thf('196', plain,
% 10.16/10.36      (((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))),
% 10.16/10.36      inference('sup-', [status(thm)], ['179', '195'])).
% 10.16/10.36  thf('197', plain,
% 10.16/10.36      ((((k1_funct_1 @ sk_C_2 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E)))
% 10.16/10.36         <= (~ (((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E))))),
% 10.16/10.36      inference('split', [status(esa)], ['6'])).
% 10.16/10.36  thf('198', plain,
% 10.16/10.36      (~ (((k1_funct_1 @ sk_C_2 @ sk_E) = (k1_funct_1 @ sk_D @ sk_E)))),
% 10.16/10.36      inference('sat_resolution*', [status(thm)],
% 10.16/10.36                ['177', '82', '88', '114', '115', '116', '176', '7'])).
% 10.16/10.36  thf('199', plain,
% 10.16/10.36      (((k1_funct_1 @ sk_C_2 @ sk_E) != (k1_funct_1 @ sk_D @ sk_E))),
% 10.16/10.36      inference('simpl_trail', [status(thm)], ['197', '198'])).
% 10.16/10.36  thf('200', plain, ($false),
% 10.16/10.36      inference('simplify_reflect-', [status(thm)], ['196', '199'])).
% 10.16/10.36  
% 10.16/10.36  % SZS output end Refutation
% 10.16/10.36  
% 10.16/10.37  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
