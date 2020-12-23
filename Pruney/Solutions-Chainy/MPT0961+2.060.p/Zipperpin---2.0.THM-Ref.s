%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SE4uvKU3ID

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:47 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :  124 (5582 expanded)
%              Number of leaves         :   32 (1564 expanded)
%              Depth                    :   22
%              Number of atoms          :  909 (64116 expanded)
%              Number of equality atoms :   61 (1916 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t3_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v1_funct_1 @ A )
          & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
          & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_A )
   <= ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X9: $i] :
      ( ( r1_tarski @ X9 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X9 ) @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['4','11','12'])).

thf('14',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('15',plain,(
    ! [X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

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

thf('16',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('18',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

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

thf('28',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22
       != ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42'])).

thf('45',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42'])).

thf('46',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','43','44','45'])).

thf('47',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','43','44','45'])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42'])).

thf('57',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','58'])).

thf('60',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25 != k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( v1_funct_2 @ X27 @ X26 @ X25 )
      | ( X27 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('61',plain,(
    ! [X26: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X26 @ k1_xboole_0 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('63',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['54','57'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('65',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('67',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['55','56'])).

thf('68',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X26: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X26 @ k1_xboole_0 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['61','62','68'])).

thf('70',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','58'])).

thf('71',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','71'])).

thf('73',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['69','70'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('75',plain,
    ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['54','57'])).

thf('77',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('78',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('79',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X21 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('83',plain,(
    ! [X20: $i] :
      ( zip_tseitin_0 @ X20 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['81','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','84'])).

thf('86',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['55','56'])).

thf('87',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['69','70'])).

thf('88',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['54','57'])).

thf('89',plain,(
    v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['75','76','85','86','87','88'])).

thf('90',plain,(
    $false ),
    inference(demod,[status(thm)],['72','89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SE4uvKU3ID
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:46:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.34/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.53  % Solved by: fo/fo7.sh
% 0.34/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.53  % done 97 iterations in 0.080s
% 0.34/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.53  % SZS output start Refutation
% 0.34/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.34/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.34/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.34/0.53  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.34/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.34/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.34/0.53  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.34/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.34/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.34/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.34/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.34/0.53  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.34/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.53  thf(t3_funct_2, conjecture,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.34/0.53       ( ( v1_funct_1 @ A ) & 
% 0.34/0.53         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.34/0.53         ( m1_subset_1 @
% 0.34/0.53           A @ 
% 0.34/0.53           ( k1_zfmisc_1 @
% 0.34/0.53             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.34/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.53    (~( ![A:$i]:
% 0.34/0.53        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.34/0.53          ( ( v1_funct_1 @ A ) & 
% 0.34/0.53            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.34/0.53            ( m1_subset_1 @
% 0.34/0.53              A @ 
% 0.34/0.53              ( k1_zfmisc_1 @
% 0.34/0.53                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.34/0.53    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.34/0.53  thf('0', plain,
% 0.34/0.53      ((~ (v1_funct_1 @ sk_A)
% 0.34/0.53        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.34/0.53        | ~ (m1_subset_1 @ sk_A @ 
% 0.34/0.53             (k1_zfmisc_1 @ 
% 0.34/0.53              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('1', plain,
% 0.34/0.53      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.34/0.53         <= (~
% 0.34/0.53             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.34/0.53      inference('split', [status(esa)], ['0'])).
% 0.34/0.53  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.34/0.53      inference('split', [status(esa)], ['0'])).
% 0.34/0.53  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.34/0.53  thf(t21_relat_1, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( v1_relat_1 @ A ) =>
% 0.34/0.53       ( r1_tarski @
% 0.34/0.53         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.34/0.53  thf('5', plain,
% 0.34/0.53      (![X9 : $i]:
% 0.34/0.53         ((r1_tarski @ X9 @ 
% 0.34/0.53           (k2_zfmisc_1 @ (k1_relat_1 @ X9) @ (k2_relat_1 @ X9)))
% 0.34/0.53          | ~ (v1_relat_1 @ X9))),
% 0.34/0.53      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.34/0.53  thf(t3_subset, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.34/0.53  thf('6', plain,
% 0.34/0.53      (![X3 : $i, X5 : $i]:
% 0.34/0.53         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.34/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.34/0.53  thf('7', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v1_relat_1 @ X0)
% 0.34/0.53          | (m1_subset_1 @ X0 @ 
% 0.34/0.53             (k1_zfmisc_1 @ 
% 0.34/0.53              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.34/0.53  thf('8', plain,
% 0.34/0.53      ((~ (m1_subset_1 @ sk_A @ 
% 0.34/0.53           (k1_zfmisc_1 @ 
% 0.34/0.53            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.34/0.53         <= (~
% 0.34/0.53             ((m1_subset_1 @ sk_A @ 
% 0.34/0.53               (k1_zfmisc_1 @ 
% 0.34/0.53                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.34/0.53      inference('split', [status(esa)], ['0'])).
% 0.34/0.53  thf('9', plain,
% 0.34/0.53      ((~ (v1_relat_1 @ sk_A))
% 0.34/0.53         <= (~
% 0.34/0.53             ((m1_subset_1 @ sk_A @ 
% 0.34/0.53               (k1_zfmisc_1 @ 
% 0.34/0.53                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.34/0.53  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('11', plain,
% 0.34/0.53      (((m1_subset_1 @ sk_A @ 
% 0.34/0.53         (k1_zfmisc_1 @ 
% 0.34/0.53          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.34/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.34/0.53  thf('12', plain,
% 0.34/0.53      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.34/0.53       ~
% 0.34/0.53       ((m1_subset_1 @ sk_A @ 
% 0.34/0.53         (k1_zfmisc_1 @ 
% 0.34/0.53          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.34/0.53       ~ ((v1_funct_1 @ sk_A))),
% 0.34/0.53      inference('split', [status(esa)], ['0'])).
% 0.34/0.53  thf('13', plain,
% 0.34/0.53      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.34/0.53      inference('sat_resolution*', [status(thm)], ['4', '11', '12'])).
% 0.34/0.53  thf('14', plain,
% 0.34/0.53      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.34/0.53      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.34/0.53  thf(t29_mcart_1, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.34/0.53          ( ![B:$i]:
% 0.34/0.53            ( ~( ( r2_hidden @ B @ A ) & 
% 0.34/0.53                 ( ![C:$i,D:$i,E:$i]:
% 0.34/0.53                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.34/0.53                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.34/0.53  thf('15', plain,
% 0.34/0.53      (![X16 : $i]:
% 0.34/0.53         (((X16) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X16) @ X16))),
% 0.34/0.53      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.34/0.53  thf(d1_funct_2, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.53       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.34/0.53           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.34/0.53             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.34/0.53         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.34/0.53           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.34/0.53             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.34/0.53  thf(zf_stmt_1, axiom,
% 0.34/0.53    (![B:$i,A:$i]:
% 0.34/0.53     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.34/0.53       ( zip_tseitin_0 @ B @ A ) ))).
% 0.34/0.53  thf('16', plain,
% 0.34/0.53      (![X20 : $i, X21 : $i]:
% 0.34/0.53         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.34/0.53  thf(t113_zfmisc_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.34/0.53       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.34/0.53  thf('17', plain,
% 0.34/0.53      (![X1 : $i, X2 : $i]:
% 0.34/0.53         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.34/0.53  thf('18', plain,
% 0.34/0.53      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.53      inference('simplify', [status(thm)], ['17'])).
% 0.34/0.53  thf('19', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.53         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.34/0.53      inference('sup+', [status(thm)], ['16', '18'])).
% 0.34/0.53  thf('20', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v1_relat_1 @ X0)
% 0.34/0.53          | (m1_subset_1 @ X0 @ 
% 0.34/0.53             (k1_zfmisc_1 @ 
% 0.34/0.53              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.34/0.53  thf(t5_subset, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.34/0.53          ( v1_xboole_0 @ C ) ) ))).
% 0.34/0.53  thf('21', plain,
% 0.34/0.53      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.34/0.53         (~ (r2_hidden @ X6 @ X7)
% 0.34/0.53          | ~ (v1_xboole_0 @ X8)
% 0.34/0.53          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t5_subset])).
% 0.34/0.53  thf('22', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (~ (v1_relat_1 @ X0)
% 0.34/0.53          | ~ (v1_xboole_0 @ 
% 0.34/0.53               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.34/0.53          | ~ (r2_hidden @ X1 @ X0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.34/0.53  thf('23', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.53         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.34/0.53          | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X2)
% 0.34/0.53          | ~ (r2_hidden @ X1 @ X0)
% 0.34/0.53          | ~ (v1_relat_1 @ X0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['19', '22'])).
% 0.34/0.53  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.34/0.53  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.34/0.53      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.34/0.53  thf('25', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.53         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X2)
% 0.34/0.53          | ~ (r2_hidden @ X1 @ X0)
% 0.34/0.53          | ~ (v1_relat_1 @ X0))),
% 0.34/0.53      inference('demod', [status(thm)], ['23', '24'])).
% 0.34/0.53  thf('26', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (((X0) = (k1_xboole_0))
% 0.34/0.53          | ~ (v1_relat_1 @ X0)
% 0.34/0.53          | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1))),
% 0.34/0.53      inference('sup-', [status(thm)], ['15', '25'])).
% 0.34/0.53  thf('27', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v1_relat_1 @ X0)
% 0.34/0.53          | (m1_subset_1 @ X0 @ 
% 0.34/0.53             (k1_zfmisc_1 @ 
% 0.34/0.53              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.34/0.53  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.34/0.53  thf(zf_stmt_3, axiom,
% 0.34/0.53    (![C:$i,B:$i,A:$i]:
% 0.34/0.53     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.34/0.53       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.34/0.53  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.34/0.53  thf(zf_stmt_5, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.53       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.34/0.53         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.34/0.53           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.34/0.53             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.34/0.53  thf('28', plain,
% 0.34/0.53      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.34/0.53         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.34/0.53          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.34/0.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.34/0.53  thf('29', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v1_relat_1 @ X0)
% 0.34/0.53          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.34/0.53          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.34/0.53  thf('30', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v1_relat_1 @ X0)
% 0.34/0.53          | ((X0) = (k1_xboole_0))
% 0.34/0.53          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.34/0.53          | ~ (v1_relat_1 @ X0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['26', '29'])).
% 0.34/0.53  thf('31', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         ((zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.34/0.53          | ((X0) = (k1_xboole_0))
% 0.34/0.53          | ~ (v1_relat_1 @ X0))),
% 0.34/0.53      inference('simplify', [status(thm)], ['30'])).
% 0.34/0.53  thf('32', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v1_relat_1 @ X0)
% 0.34/0.53          | (m1_subset_1 @ X0 @ 
% 0.34/0.53             (k1_zfmisc_1 @ 
% 0.34/0.53              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.34/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.34/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.34/0.53  thf('33', plain,
% 0.34/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.34/0.53         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 0.34/0.53          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.34/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.34/0.53  thf('34', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v1_relat_1 @ X0)
% 0.34/0.53          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.34/0.53              = (k1_relat_1 @ X0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.34/0.53  thf('35', plain,
% 0.34/0.53      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.34/0.53         (((X22) != (k1_relset_1 @ X22 @ X23 @ X24))
% 0.34/0.53          | (v1_funct_2 @ X24 @ X22 @ X23)
% 0.34/0.53          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.34/0.53  thf('36', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.34/0.53          | ~ (v1_relat_1 @ X0)
% 0.34/0.53          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.34/0.53          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['34', '35'])).
% 0.34/0.53  thf('37', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.34/0.53          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.34/0.53          | ~ (v1_relat_1 @ X0))),
% 0.34/0.53      inference('simplify', [status(thm)], ['36'])).
% 0.34/0.53  thf('38', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v1_relat_1 @ X0)
% 0.34/0.53          | ((X0) = (k1_xboole_0))
% 0.34/0.53          | ~ (v1_relat_1 @ X0)
% 0.34/0.53          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['31', '37'])).
% 0.34/0.53  thf('39', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.34/0.53          | ((X0) = (k1_xboole_0))
% 0.34/0.53          | ~ (v1_relat_1 @ X0))),
% 0.34/0.53      inference('simplify', [status(thm)], ['38'])).
% 0.34/0.53  thf('40', plain,
% 0.34/0.53      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.34/0.53      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.34/0.53  thf('41', plain, ((~ (v1_relat_1 @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.34/0.53  thf('42', plain, ((v1_relat_1 @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('43', plain, (((sk_A) = (k1_xboole_0))),
% 0.34/0.53      inference('demod', [status(thm)], ['41', '42'])).
% 0.34/0.53  thf('44', plain, (((sk_A) = (k1_xboole_0))),
% 0.34/0.53      inference('demod', [status(thm)], ['41', '42'])).
% 0.34/0.53  thf('45', plain, (((sk_A) = (k1_xboole_0))),
% 0.34/0.53      inference('demod', [status(thm)], ['41', '42'])).
% 0.34/0.53  thf('46', plain,
% 0.34/0.53      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 0.34/0.53          (k2_relat_1 @ k1_xboole_0))),
% 0.34/0.53      inference('demod', [status(thm)], ['14', '43', '44', '45'])).
% 0.34/0.53  thf('47', plain,
% 0.34/0.53      (![X20 : $i, X21 : $i]:
% 0.34/0.53         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.34/0.53  thf('48', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v1_relat_1 @ X0)
% 0.34/0.53          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.34/0.53          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.34/0.53  thf('49', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.34/0.53          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.34/0.53          | ~ (v1_relat_1 @ X0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['47', '48'])).
% 0.34/0.53  thf('50', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.34/0.53          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.34/0.53          | ~ (v1_relat_1 @ X0))),
% 0.34/0.53      inference('simplify', [status(thm)], ['36'])).
% 0.34/0.53  thf('51', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v1_relat_1 @ X0)
% 0.34/0.53          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.34/0.53          | ~ (v1_relat_1 @ X0)
% 0.34/0.53          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['49', '50'])).
% 0.34/0.53  thf('52', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.34/0.53          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.34/0.53          | ~ (v1_relat_1 @ X0))),
% 0.34/0.53      inference('simplify', [status(thm)], ['51'])).
% 0.34/0.53  thf('53', plain,
% 0.34/0.53      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 0.34/0.53          (k2_relat_1 @ k1_xboole_0))),
% 0.34/0.53      inference('demod', [status(thm)], ['14', '43', '44', '45'])).
% 0.34/0.53  thf('54', plain,
% 0.34/0.53      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.34/0.53        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['52', '53'])).
% 0.34/0.53  thf('55', plain, ((v1_relat_1 @ sk_A)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('56', plain, (((sk_A) = (k1_xboole_0))),
% 0.34/0.53      inference('demod', [status(thm)], ['41', '42'])).
% 0.34/0.53  thf('57', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.34/0.53      inference('demod', [status(thm)], ['55', '56'])).
% 0.34/0.53  thf('58', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.53      inference('demod', [status(thm)], ['54', '57'])).
% 0.34/0.53  thf('59', plain,
% 0.34/0.53      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.34/0.53      inference('demod', [status(thm)], ['46', '58'])).
% 0.34/0.53  thf('60', plain,
% 0.34/0.53      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.34/0.53         (((X25) != (k1_xboole_0))
% 0.34/0.53          | ((X26) = (k1_xboole_0))
% 0.34/0.53          | (v1_funct_2 @ X27 @ X26 @ X25)
% 0.34/0.53          | ((X27) != (k1_xboole_0))
% 0.34/0.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.34/0.53  thf('61', plain,
% 0.34/0.53      (![X26 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.34/0.53             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ k1_xboole_0)))
% 0.34/0.53          | (v1_funct_2 @ k1_xboole_0 @ X26 @ k1_xboole_0)
% 0.34/0.53          | ((X26) = (k1_xboole_0)))),
% 0.34/0.53      inference('simplify', [status(thm)], ['60'])).
% 0.34/0.53  thf('62', plain,
% 0.34/0.53      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.53      inference('simplify', [status(thm)], ['17'])).
% 0.34/0.53  thf('63', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.53      inference('demod', [status(thm)], ['54', '57'])).
% 0.34/0.53  thf('64', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         (~ (v1_relat_1 @ X0)
% 0.34/0.53          | (m1_subset_1 @ X0 @ 
% 0.34/0.53             (k1_zfmisc_1 @ 
% 0.34/0.53              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.34/0.53  thf('65', plain,
% 0.34/0.53      (((m1_subset_1 @ k1_xboole_0 @ 
% 0.34/0.53         (k1_zfmisc_1 @ 
% 0.34/0.53          (k2_zfmisc_1 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)))
% 0.34/0.53        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.34/0.53      inference('sup+', [status(thm)], ['63', '64'])).
% 0.34/0.53  thf('66', plain,
% 0.34/0.53      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.53      inference('simplify', [status(thm)], ['17'])).
% 0.34/0.53  thf('67', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.34/0.53      inference('demod', [status(thm)], ['55', '56'])).
% 0.34/0.53  thf('68', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.34/0.53      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.34/0.53  thf('69', plain,
% 0.34/0.53      (![X26 : $i]:
% 0.34/0.53         ((v1_funct_2 @ k1_xboole_0 @ X26 @ k1_xboole_0)
% 0.34/0.53          | ((X26) = (k1_xboole_0)))),
% 0.34/0.53      inference('demod', [status(thm)], ['61', '62', '68'])).
% 0.34/0.53  thf('70', plain,
% 0.34/0.53      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.34/0.53      inference('demod', [status(thm)], ['46', '58'])).
% 0.34/0.53  thf('71', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['69', '70'])).
% 0.34/0.53  thf('72', plain, (~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.34/0.53      inference('demod', [status(thm)], ['59', '71'])).
% 0.34/0.53  thf('73', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['69', '70'])).
% 0.34/0.53  thf('74', plain,
% 0.34/0.53      (![X0 : $i]:
% 0.34/0.53         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.34/0.53          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.34/0.53          | ~ (v1_relat_1 @ X0))),
% 0.34/0.53      inference('simplify', [status(thm)], ['36'])).
% 0.34/0.53  thf('75', plain,
% 0.34/0.53      ((~ (zip_tseitin_1 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0) @ 
% 0.34/0.53           k1_xboole_0)
% 0.34/0.53        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.34/0.53        | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 0.34/0.53           (k2_relat_1 @ k1_xboole_0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['73', '74'])).
% 0.34/0.53  thf('76', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.53      inference('demod', [status(thm)], ['54', '57'])).
% 0.34/0.53  thf('77', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.34/0.53      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.34/0.53  thf('78', plain,
% 0.34/0.53      (![X1 : $i, X2 : $i]:
% 0.34/0.53         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.34/0.53  thf('79', plain,
% 0.34/0.53      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.34/0.53      inference('simplify', [status(thm)], ['78'])).
% 0.34/0.53  thf('80', plain,
% 0.34/0.53      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.34/0.53         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.34/0.53          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.34/0.53          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.34/0.53  thf('81', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.34/0.53          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 0.34/0.53          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['79', '80'])).
% 0.34/0.53  thf('82', plain,
% 0.34/0.53      (![X20 : $i, X21 : $i]:
% 0.34/0.53         ((zip_tseitin_0 @ X20 @ X21) | ((X21) != (k1_xboole_0)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.34/0.53  thf('83', plain, (![X20 : $i]: (zip_tseitin_0 @ X20 @ k1_xboole_0)),
% 0.34/0.53      inference('simplify', [status(thm)], ['82'])).
% 0.34/0.53  thf('84', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.34/0.53          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 0.34/0.53      inference('demod', [status(thm)], ['81', '83'])).
% 0.34/0.53  thf('85', plain,
% 0.34/0.53      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.34/0.53      inference('sup-', [status(thm)], ['77', '84'])).
% 0.34/0.53  thf('86', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.34/0.53      inference('demod', [status(thm)], ['55', '56'])).
% 0.34/0.53  thf('87', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.53      inference('sup-', [status(thm)], ['69', '70'])).
% 0.34/0.53  thf('88', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.53      inference('demod', [status(thm)], ['54', '57'])).
% 0.34/0.53  thf('89', plain, ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.34/0.53      inference('demod', [status(thm)], ['75', '76', '85', '86', '87', '88'])).
% 0.34/0.53  thf('90', plain, ($false), inference('demod', [status(thm)], ['72', '89'])).
% 0.34/0.53  
% 0.34/0.53  % SZS output end Refutation
% 0.34/0.53  
% 0.37/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
