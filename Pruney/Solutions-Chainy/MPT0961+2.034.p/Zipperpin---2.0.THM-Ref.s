%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XXUCFXVIyN

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:43 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  147 (7295 expanded)
%              Number of leaves         :   32 (1927 expanded)
%              Depth                    :   25
%              Number of atoms          : 1176 (81688 expanded)
%              Number of equality atoms :   85 (3242 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf(zf_stmt_0,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28 != k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( v1_funct_2 @ X30 @ X29 @ X28 )
      | ( X30 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('2',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('4',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X29: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['2','4'])).

thf('6',plain,
    ( ! [X29: $i] :
        ( ( X29 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0 ) )
   <= ! [X29: $i] :
        ( ( X29 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
        | ( zip_tseitin_0 @ X0 @ X2 )
        | ( X1 = k1_xboole_0 ) )
   <= ! [X29: $i] :
        ( ( X29 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','6'])).

thf(t3_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v1_funct_1 @ A )
          & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
          & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_funct_2])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('11',plain,
    ( ~ ( v1_funct_1 @ sk_A )
   <= ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('12',plain,(
    v1_funct_1 @ sk_A ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X17 )
      | ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['8'])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('22',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['8'])).

thf('24',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['12','22','23'])).

thf('25',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['9','24'])).

thf(t34_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) )).

thf('26',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf('27',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('31',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('38',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25
       != ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['9','24'])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('53',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','52'])).

thf('55',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','52'])).

thf('56',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','53','54','55'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ k1_xboole_0 )
          = k1_xboole_0 )
        | ( zip_tseitin_0 @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) )
   <= ! [X29: $i] :
        ( ( X29 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('59',plain,
    ( ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) )
   <= ! [X29: $i] :
        ( ( X29 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('61',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','52'])).

thf('62',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ k1_xboole_0 ) ) )
   <= ! [X29: $i] :
        ( ( X29 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('65',plain,
    ( ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) ) )
   <= ! [X29: $i] :
        ( ( X29 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['60','61'])).

thf('67',plain,
    ( ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) ) )
   <= ! [X29: $i] :
        ( ( X29 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','53','54','55'])).

thf('69',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ! [X29: $i] :
        ( ( X29 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','53','54','55'])).

thf('71',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','53','54','55'])).

thf('78',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['60','61'])).

thf('80',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','80'])).

thf('82',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
   <= ! [X29: $i] :
        ( ( X29 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','81'])).

thf('83',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['78','79'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('85',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('87',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['60','61'])).

thf('88',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,
    ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('90',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ! [X29: $i] :
        ( ( X29 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0 ) )
    | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('92',plain,(
    ! [X29: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0 ) ) ),
    inference('sat_resolution*',[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['82','92'])).

thf('94',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ! [X29: $i] :
        ( ( X29 = k1_xboole_0 )
        | ( v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('95',plain,(
    ! [X29: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0 ) ) ),
    inference('sat_resolution*',[status(thm)],['90','91'])).

thf('96',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('98',plain,
    ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['78','79'])).

thf('100',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('101',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('102',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X23: $i] :
      ( zip_tseitin_0 @ X23 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['104','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','107'])).

thf('109',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['60','61'])).

thf('110',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['94','95'])).

thf('111',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['78','79'])).

thf('112',plain,(
    v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['98','99','108','109','110','111'])).

thf('113',plain,(
    $false ),
    inference(demod,[status(thm)],['93','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XXUCFXVIyN
% 0.14/0.36  % Computer   : n021.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 16:00:04 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 138 iterations in 0.166s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.45/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.65  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.65  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.65  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.45/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.65  thf(d1_funct_2, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.65       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.65           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.45/0.65             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.65         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.65           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.45/0.65             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, axiom,
% 0.45/0.65    (![B:$i,A:$i]:
% 0.45/0.65     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.65       ( zip_tseitin_0 @ B @ A ) ))).
% 0.45/0.65  thf('0', plain,
% 0.45/0.65      (![X23 : $i, X24 : $i]:
% 0.45/0.65         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.45/0.65  thf(zf_stmt_2, axiom,
% 0.45/0.65    (![C:$i,B:$i,A:$i]:
% 0.45/0.65     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.45/0.65       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.45/0.65  thf(zf_stmt_4, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.65       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.45/0.65         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.65           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.65             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.65         (((X28) != (k1_xboole_0))
% 0.45/0.65          | ((X29) = (k1_xboole_0))
% 0.45/0.65          | (v1_funct_2 @ X30 @ X29 @ X28)
% 0.45/0.65          | ((X30) != (k1_xboole_0))
% 0.45/0.65          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      (![X29 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.45/0.65             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ k1_xboole_0)))
% 0.45/0.65          | (v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0)
% 0.45/0.65          | ((X29) = (k1_xboole_0)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['1'])).
% 0.45/0.65  thf(t113_zfmisc_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.45/0.65       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (![X4 : $i, X5 : $i]:
% 0.45/0.65         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.45/0.65  thf('4', plain,
% 0.45/0.65      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['3'])).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      (![X29 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.45/0.65          | (v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0)
% 0.45/0.65          | ((X29) = (k1_xboole_0)))),
% 0.45/0.65      inference('demod', [status(thm)], ['2', '4'])).
% 0.45/0.65  thf('6', plain,
% 0.45/0.65      ((![X29 : $i]:
% 0.45/0.65          (((X29) = (k1_xboole_0))
% 0.45/0.65           | (v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0)))
% 0.45/0.65         <= ((![X29 : $i]:
% 0.45/0.65                (((X29) = (k1_xboole_0))
% 0.45/0.65                 | (v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0))))),
% 0.45/0.65      inference('split', [status(esa)], ['5'])).
% 0.45/0.65  thf('7', plain,
% 0.45/0.65      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65          ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 0.45/0.65           | (zip_tseitin_0 @ X0 @ X2)
% 0.45/0.65           | ((X1) = (k1_xboole_0))))
% 0.45/0.65         <= ((![X29 : $i]:
% 0.45/0.65                (((X29) = (k1_xboole_0))
% 0.45/0.65                 | (v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0))))),
% 0.45/0.65      inference('sup+', [status(thm)], ['0', '6'])).
% 0.45/0.65  thf(t3_funct_2, conjecture,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.65       ( ( v1_funct_1 @ A ) & 
% 0.45/0.65         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.45/0.65         ( m1_subset_1 @
% 0.45/0.65           A @ 
% 0.45/0.65           ( k1_zfmisc_1 @
% 0.45/0.65             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_5, negated_conjecture,
% 0.45/0.65    (~( ![A:$i]:
% 0.45/0.65        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.65          ( ( v1_funct_1 @ A ) & 
% 0.45/0.65            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.45/0.65            ( m1_subset_1 @
% 0.45/0.65              A @ 
% 0.45/0.65              ( k1_zfmisc_1 @
% 0.45/0.65                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      ((~ (v1_funct_1 @ sk_A)
% 0.45/0.65        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.45/0.65        | ~ (m1_subset_1 @ sk_A @ 
% 0.45/0.65             (k1_zfmisc_1 @ 
% 0.45/0.65              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.65  thf('9', plain,
% 0.45/0.65      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.45/0.65         <= (~
% 0.45/0.65             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.45/0.65      inference('split', [status(esa)], ['8'])).
% 0.45/0.65  thf('10', plain, ((v1_funct_1 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.65  thf('11', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.45/0.65      inference('split', [status(esa)], ['8'])).
% 0.45/0.65  thf('12', plain, (((v1_funct_1 @ sk_A))),
% 0.45/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.65  thf(d10_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.65  thf('13', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.65  thf('14', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.45/0.65      inference('simplify', [status(thm)], ['13'])).
% 0.45/0.65  thf('15', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.45/0.65      inference('simplify', [status(thm)], ['13'])).
% 0.45/0.65  thf(t11_relset_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ C ) =>
% 0.45/0.65       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.45/0.65           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.45/0.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.45/0.65         (~ (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 0.45/0.65          | ~ (r1_tarski @ (k2_relat_1 @ X15) @ X17)
% 0.45/0.65          | (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17)))
% 0.45/0.65          | ~ (v1_relat_1 @ X15))),
% 0.45/0.65      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | (m1_subset_1 @ X0 @ 
% 0.45/0.65             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.45/0.65          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.65  thf('18', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((m1_subset_1 @ X0 @ 
% 0.45/0.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['14', '17'])).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      ((~ (m1_subset_1 @ sk_A @ 
% 0.45/0.65           (k1_zfmisc_1 @ 
% 0.45/0.65            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.45/0.65         <= (~
% 0.45/0.65             ((m1_subset_1 @ sk_A @ 
% 0.45/0.65               (k1_zfmisc_1 @ 
% 0.45/0.65                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.45/0.65      inference('split', [status(esa)], ['8'])).
% 0.45/0.65  thf('20', plain,
% 0.45/0.65      ((~ (v1_relat_1 @ sk_A))
% 0.45/0.65         <= (~
% 0.45/0.65             ((m1_subset_1 @ sk_A @ 
% 0.45/0.65               (k1_zfmisc_1 @ 
% 0.45/0.65                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.65  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.65  thf('22', plain,
% 0.45/0.65      (((m1_subset_1 @ sk_A @ 
% 0.45/0.65         (k1_zfmisc_1 @ 
% 0.45/0.65          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.45/0.65      inference('demod', [status(thm)], ['20', '21'])).
% 0.45/0.65  thf('23', plain,
% 0.45/0.65      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.45/0.65       ~
% 0.45/0.65       ((m1_subset_1 @ sk_A @ 
% 0.45/0.65         (k1_zfmisc_1 @ 
% 0.45/0.65          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.45/0.65       ~ ((v1_funct_1 @ sk_A))),
% 0.45/0.65      inference('split', [status(esa)], ['8'])).
% 0.45/0.65  thf('24', plain,
% 0.45/0.65      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.45/0.65      inference('sat_resolution*', [status(thm)], ['12', '22', '23'])).
% 0.45/0.65  thf('25', plain,
% 0.45/0.65      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.45/0.65      inference('simpl_trail', [status(thm)], ['9', '24'])).
% 0.45/0.65  thf(t34_mcart_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.65          ( ![B:$i]:
% 0.45/0.65            ( ~( ( r2_hidden @ B @ A ) & 
% 0.45/0.65                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 0.45/0.65                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.45/0.65                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.65  thf('26', plain,
% 0.45/0.65      (![X18 : $i]:
% 0.45/0.65         (((X18) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X18) @ X18))),
% 0.45/0.65      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.45/0.65  thf('27', plain,
% 0.45/0.65      (![X23 : $i, X24 : $i]:
% 0.45/0.65         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('28', plain,
% 0.45/0.65      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['3'])).
% 0.45/0.65  thf('29', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.45/0.65      inference('sup+', [status(thm)], ['27', '28'])).
% 0.45/0.65  thf('30', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((m1_subset_1 @ X0 @ 
% 0.45/0.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['14', '17'])).
% 0.45/0.65  thf(t5_subset, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.45/0.65          ( v1_xboole_0 @ C ) ) ))).
% 0.45/0.65  thf('31', plain,
% 0.45/0.65      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X6 @ X7)
% 0.45/0.65          | ~ (v1_xboole_0 @ X8)
% 0.45/0.65          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t5_subset])).
% 0.45/0.65  thf('32', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_xboole_0 @ 
% 0.45/0.65               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.45/0.65          | ~ (r2_hidden @ X1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['30', '31'])).
% 0.45/0.65  thf('33', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.45/0.65          | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X2)
% 0.45/0.65          | ~ (r2_hidden @ X1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['29', '32'])).
% 0.45/0.65  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.45/0.65  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.65  thf('35', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X2)
% 0.45/0.65          | ~ (r2_hidden @ X1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('demod', [status(thm)], ['33', '34'])).
% 0.45/0.65  thf('36', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (((X0) = (k1_xboole_0))
% 0.45/0.65          | ~ (v1_relat_1 @ X0)
% 0.45/0.65          | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['26', '35'])).
% 0.45/0.65  thf('37', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((m1_subset_1 @ X0 @ 
% 0.45/0.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['14', '17'])).
% 0.45/0.65  thf('38', plain,
% 0.45/0.65      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.65         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.45/0.65          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.45/0.65          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.45/0.65  thf('39', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.45/0.65          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['37', '38'])).
% 0.45/0.65  thf('40', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | ((X0) = (k1_xboole_0))
% 0.45/0.65          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['36', '39'])).
% 0.45/0.65  thf('41', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.45/0.65          | ((X0) = (k1_xboole_0))
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['40'])).
% 0.45/0.65  thf('42', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((m1_subset_1 @ X0 @ 
% 0.45/0.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['14', '17'])).
% 0.45/0.65  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.65       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.65  thf('43', plain,
% 0.45/0.65      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.65         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 0.45/0.65          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.65  thf('44', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.45/0.65              = (k1_relat_1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.65  thf('45', plain,
% 0.45/0.65      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.65         (((X25) != (k1_relset_1 @ X25 @ X26 @ X27))
% 0.45/0.65          | (v1_funct_2 @ X27 @ X25 @ X26)
% 0.45/0.65          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.65  thf('46', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.45/0.65          | ~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.45/0.65          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['44', '45'])).
% 0.45/0.65  thf('47', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.45/0.65          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['46'])).
% 0.45/0.65  thf('48', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | ((X0) = (k1_xboole_0))
% 0.45/0.65          | ~ (v1_relat_1 @ X0)
% 0.45/0.65          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['41', '47'])).
% 0.45/0.65  thf('49', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.45/0.65          | ((X0) = (k1_xboole_0))
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['48'])).
% 0.45/0.65  thf('50', plain,
% 0.45/0.65      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.45/0.65      inference('simpl_trail', [status(thm)], ['9', '24'])).
% 0.45/0.65  thf('51', plain, ((~ (v1_relat_1 @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['49', '50'])).
% 0.45/0.65  thf('52', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.65  thf('53', plain, (((sk_A) = (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['51', '52'])).
% 0.45/0.65  thf('54', plain, (((sk_A) = (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['51', '52'])).
% 0.45/0.65  thf('55', plain, (((sk_A) = (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['51', '52'])).
% 0.45/0.65  thf('56', plain,
% 0.45/0.65      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 0.45/0.65          (k2_relat_1 @ k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['25', '53', '54', '55'])).
% 0.45/0.65  thf('57', plain,
% 0.45/0.65      ((![X0 : $i]:
% 0.45/0.65          (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.45/0.65           | (zip_tseitin_0 @ (k2_relat_1 @ k1_xboole_0) @ X0)))
% 0.45/0.65         <= ((![X29 : $i]:
% 0.45/0.65                (((X29) = (k1_xboole_0))
% 0.45/0.65                 | (v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['7', '56'])).
% 0.45/0.65  thf('58', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.45/0.65          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['37', '38'])).
% 0.45/0.65  thf('59', plain,
% 0.45/0.65      (((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.45/0.65         | (zip_tseitin_1 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0) @ 
% 0.45/0.65            (k1_relat_1 @ k1_xboole_0))
% 0.45/0.65         | ~ (v1_relat_1 @ k1_xboole_0)))
% 0.45/0.65         <= ((![X29 : $i]:
% 0.45/0.65                (((X29) = (k1_xboole_0))
% 0.45/0.65                 | (v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['57', '58'])).
% 0.45/0.65  thf('60', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.65  thf('61', plain, (((sk_A) = (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['51', '52'])).
% 0.45/0.65  thf('62', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.45/0.65      inference('demod', [status(thm)], ['60', '61'])).
% 0.45/0.65  thf('63', plain,
% 0.45/0.65      (((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.45/0.65         | (zip_tseitin_1 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0) @ 
% 0.45/0.65            (k1_relat_1 @ k1_xboole_0))))
% 0.45/0.65         <= ((![X29 : $i]:
% 0.45/0.65                (((X29) = (k1_xboole_0))
% 0.45/0.65                 | (v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0))))),
% 0.45/0.65      inference('demod', [status(thm)], ['59', '62'])).
% 0.45/0.65  thf('64', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.45/0.65          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['46'])).
% 0.45/0.65  thf('65', plain,
% 0.45/0.65      (((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.45/0.65         | ~ (v1_relat_1 @ k1_xboole_0)
% 0.45/0.65         | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 0.45/0.65            (k2_relat_1 @ k1_xboole_0))))
% 0.45/0.65         <= ((![X29 : $i]:
% 0.45/0.65                (((X29) = (k1_xboole_0))
% 0.45/0.65                 | (v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['63', '64'])).
% 0.45/0.65  thf('66', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.45/0.65      inference('demod', [status(thm)], ['60', '61'])).
% 0.45/0.65  thf('67', plain,
% 0.45/0.65      (((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.45/0.65         | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 0.45/0.65            (k2_relat_1 @ k1_xboole_0))))
% 0.45/0.65         <= ((![X29 : $i]:
% 0.45/0.65                (((X29) = (k1_xboole_0))
% 0.45/0.65                 | (v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0))))),
% 0.45/0.65      inference('demod', [status(thm)], ['65', '66'])).
% 0.45/0.65  thf('68', plain,
% 0.45/0.65      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 0.45/0.65          (k2_relat_1 @ k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['25', '53', '54', '55'])).
% 0.45/0.65  thf('69', plain,
% 0.45/0.65      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 0.45/0.65         <= ((![X29 : $i]:
% 0.45/0.65                (((X29) = (k1_xboole_0))
% 0.45/0.65                 | (v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0))))),
% 0.45/0.65      inference('clc', [status(thm)], ['67', '68'])).
% 0.45/0.65  thf('70', plain,
% 0.45/0.65      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 0.45/0.65          (k2_relat_1 @ k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['25', '53', '54', '55'])).
% 0.45/0.65  thf('71', plain,
% 0.45/0.65      (![X23 : $i, X24 : $i]:
% 0.45/0.65         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('72', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.45/0.65          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['37', '38'])).
% 0.45/0.65  thf('73', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.45/0.65          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['71', '72'])).
% 0.45/0.65  thf('74', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.45/0.65          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['46'])).
% 0.45/0.65  thf('75', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.45/0.65          | ~ (v1_relat_1 @ X0)
% 0.45/0.65          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['73', '74'])).
% 0.45/0.65  thf('76', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.45/0.65          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['75'])).
% 0.45/0.65  thf('77', plain,
% 0.45/0.65      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 0.45/0.65          (k2_relat_1 @ k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['25', '53', '54', '55'])).
% 0.45/0.65  thf('78', plain,
% 0.45/0.65      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.45/0.65        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['76', '77'])).
% 0.45/0.65  thf('79', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.45/0.65      inference('demod', [status(thm)], ['60', '61'])).
% 0.45/0.65  thf('80', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['78', '79'])).
% 0.45/0.65  thf('81', plain,
% 0.45/0.65      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.45/0.65      inference('demod', [status(thm)], ['70', '80'])).
% 0.45/0.65  thf('82', plain,
% 0.45/0.65      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 0.45/0.65         <= ((![X29 : $i]:
% 0.45/0.65                (((X29) = (k1_xboole_0))
% 0.45/0.65                 | (v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['69', '81'])).
% 0.45/0.65  thf('83', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['78', '79'])).
% 0.45/0.65  thf('84', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((m1_subset_1 @ X0 @ 
% 0.45/0.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['14', '17'])).
% 0.45/0.65  thf('85', plain,
% 0.45/0.65      (((m1_subset_1 @ k1_xboole_0 @ 
% 0.45/0.65         (k1_zfmisc_1 @ 
% 0.45/0.65          (k2_zfmisc_1 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)))
% 0.45/0.65        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['83', '84'])).
% 0.45/0.65  thf('86', plain,
% 0.45/0.65      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['3'])).
% 0.45/0.65  thf('87', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.45/0.65      inference('demod', [status(thm)], ['60', '61'])).
% 0.45/0.65  thf('88', plain, ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.45/0.65  thf('89', plain,
% 0.45/0.65      ((~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.45/0.65         <= (~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))))),
% 0.45/0.65      inference('split', [status(esa)], ['5'])).
% 0.45/0.65  thf('90', plain,
% 0.45/0.65      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['88', '89'])).
% 0.45/0.65  thf('91', plain,
% 0.45/0.65      ((![X29 : $i]:
% 0.45/0.65          (((X29) = (k1_xboole_0))
% 0.45/0.65           | (v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0))) | 
% 0.45/0.65       ~ ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 0.45/0.65      inference('split', [status(esa)], ['5'])).
% 0.45/0.65  thf('92', plain,
% 0.45/0.65      ((![X29 : $i]:
% 0.45/0.65          (((X29) = (k1_xboole_0))
% 0.45/0.65           | (v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0)))),
% 0.45/0.65      inference('sat_resolution*', [status(thm)], ['90', '91'])).
% 0.45/0.65  thf('93', plain, (~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.45/0.65      inference('simpl_trail', [status(thm)], ['82', '92'])).
% 0.45/0.65  thf('94', plain,
% 0.45/0.65      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 0.45/0.65         <= ((![X29 : $i]:
% 0.45/0.65                (((X29) = (k1_xboole_0))
% 0.45/0.65                 | (v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0))))),
% 0.45/0.65      inference('clc', [status(thm)], ['67', '68'])).
% 0.45/0.65  thf('95', plain,
% 0.45/0.65      ((![X29 : $i]:
% 0.45/0.65          (((X29) = (k1_xboole_0))
% 0.45/0.65           | (v1_funct_2 @ k1_xboole_0 @ X29 @ k1_xboole_0)))),
% 0.45/0.65      inference('sat_resolution*', [status(thm)], ['90', '91'])).
% 0.45/0.65  thf('96', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('simpl_trail', [status(thm)], ['94', '95'])).
% 0.45/0.65  thf('97', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.45/0.65          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['46'])).
% 0.45/0.65  thf('98', plain,
% 0.45/0.65      ((~ (zip_tseitin_1 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0) @ 
% 0.45/0.65           k1_xboole_0)
% 0.45/0.65        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.45/0.65        | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 0.45/0.65           (k2_relat_1 @ k1_xboole_0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['96', '97'])).
% 0.45/0.65  thf('99', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['78', '79'])).
% 0.45/0.65  thf('100', plain,
% 0.45/0.65      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['85', '86', '87'])).
% 0.45/0.65  thf('101', plain,
% 0.45/0.65      (![X4 : $i, X5 : $i]:
% 0.45/0.65         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.45/0.65  thf('102', plain,
% 0.45/0.65      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['101'])).
% 0.45/0.65  thf('103', plain,
% 0.45/0.65      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.65         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.45/0.65          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.45/0.65          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.45/0.65  thf('104', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.45/0.65          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 0.45/0.65          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['102', '103'])).
% 0.45/0.65  thf('105', plain,
% 0.45/0.65      (![X23 : $i, X24 : $i]:
% 0.45/0.65         ((zip_tseitin_0 @ X23 @ X24) | ((X24) != (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('106', plain, (![X23 : $i]: (zip_tseitin_0 @ X23 @ k1_xboole_0)),
% 0.45/0.65      inference('simplify', [status(thm)], ['105'])).
% 0.45/0.65  thf('107', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.45/0.65          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['104', '106'])).
% 0.45/0.65  thf('108', plain,
% 0.45/0.65      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.45/0.65      inference('sup-', [status(thm)], ['100', '107'])).
% 0.45/0.65  thf('109', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.45/0.65      inference('demod', [status(thm)], ['60', '61'])).
% 0.45/0.65  thf('110', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('simpl_trail', [status(thm)], ['94', '95'])).
% 0.45/0.65  thf('111', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('demod', [status(thm)], ['78', '79'])).
% 0.45/0.65  thf('112', plain, ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.45/0.65      inference('demod', [status(thm)],
% 0.45/0.65                ['98', '99', '108', '109', '110', '111'])).
% 0.45/0.65  thf('113', plain, ($false), inference('demod', [status(thm)], ['93', '112'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.49/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
