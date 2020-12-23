%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UouPkRgqZ9

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:08 EST 2020

% Result     : Theorem 1.88s
% Output     : Refutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :  304 (1790 expanded)
%              Number of leaves         :   49 ( 555 expanded)
%              Depth                    :   34
%              Number of atoms          : 2065 (17366 expanded)
%              Number of equality atoms :  190 (1292 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('11',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('12',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('13',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('20',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['9','21'])).

thf('23',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('28',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('29',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','29'])).

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
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('31',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( X41
       != ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('34',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X40 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('35',plain,(
    ! [X39: $i] :
      ( zip_tseitin_0 @ X39 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('37',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['33','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ X0 @ k1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ X2 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','41'])).

thf(t8_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_5,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_funct_2])).

thf('43',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('44',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,
    ( ( ~ ( v1_xboole_0 @ sk_D )
      | ~ ( v1_xboole_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('47',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('48',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('50',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v4_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k1_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('52',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('55',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('56',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('59',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('60',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k6_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('63',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ( X41
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('66',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('67',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,
    ( ( ( k6_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf('70',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('72',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['27','28'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['69','76'])).

thf('78',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['54','79'])).

thf('81',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( X0 = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ X0 ) )
        = sk_B_1 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['53','82'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('84',plain,(
    ! [X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_B_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( ( k2_zfmisc_1 @ sk_B_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('89',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('90',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('92',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B_1 @ X0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['87','92'])).

thf('94',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('95',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k6_relat_1 @ sk_B_1 ) @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['46','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( X0 = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('102',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ( ( k6_relat_1 @ sk_B_1 )
      = sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( k6_relat_1 @ sk_B_1 )
      = sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('105',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('106',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','106'])).

thf('108',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_relat_1 @ X0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('111',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['105'])).

thf('112',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('113',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v4_relat_1 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_relat_1 @ ( k6_relat_1 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['109','114'])).

thf('116',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_relat_1 @ ( k6_relat_1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( v4_relat_1 @ sk_B_1 @ k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['103','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('123',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['122'])).

thf('124',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['121','123'])).

thf('125',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('127',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('129',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['43'])).

thf('130',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['33','39'])).

thf('132',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('133',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['122'])).

thf('134',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('135',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('137',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['105'])).

thf('139',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('140',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['137','138','139'])).

thf('141',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['132','140'])).

thf('142',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['122'])).

thf('143',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['43'])).

thf('144',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['141','144'])).

thf('146',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['131','145'])).

thf('147',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['105'])).

thf('148',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('149',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['105'])).

thf('151',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['122'])).

thf('152',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['43'])).

thf('153',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['150','153'])).

thf('155',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['149','154'])).

thf('156',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['43'])).

thf('157',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['122'])).

thf('158',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['130','146','155','156','157'])).

thf('159',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['127','158'])).

thf('160',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['118','159'])).

thf('161',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('162',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('165',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('167',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['160','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('170',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['168','171'])).

thf('173',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['45','172'])).

thf('174',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('175',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('176',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X34 @ X32 )
        = ( k2_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('177',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ),
    inference(demod,[status(thm)],['174','177'])).

thf('179',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('180',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('181',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v4_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k1_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('183',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('185',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('186',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('188',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['183','188'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('190',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X35 ) @ X36 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X35 ) @ X37 )
      | ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('191',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['186','187'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['178','193'])).

thf('195',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['43'])).

thf('196',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['43'])).

thf('198',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['130','196','197'])).

thf('199',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['173','198'])).

thf('200',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('201',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['9','21'])).

thf('202',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['200','201'])).

thf('203',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('204',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('205',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) )
    | ( sk_C_1
      = ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('207',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('208',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k2_relat_1 @ sk_D ) )
    | ( sk_C_1
      = ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['205','206','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C_1 @ X0 )
      | ( sk_C_1
        = ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['202','208'])).

thf('210',plain,(
    ! [X23: $i] :
      ( ( ( k2_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( sk_D = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['186','187'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X0 )
      | ( sk_D = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('219',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( X44 != k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( v1_funct_2 @ X46 @ X45 @ X44 )
      | ( X46 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('220',plain,(
    ! [X45: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X45 @ k1_xboole_0 )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['219'])).

thf('221',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('222',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('223',plain,(
    ! [X45: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X45 @ k1_xboole_0 )
      | ( X45 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['220','221','222'])).

thf('224',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ( X41
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0
        = ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['218','228'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['217','229'])).

thf('231',plain,
    ( ( sk_D = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(condensation,[status(thm)],['230'])).

thf('232',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('233',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['178','193'])).

thf('234',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('235',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['178','193'])).

thf('237',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('238',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('239',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['160','167'])).

thf('240',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['238','239'])).

thf('241',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( X41
       != ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['242'])).

thf('244',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['43'])).

thf('245',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['130','196','197'])).

thf('246',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['244','245'])).

thf('247',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['243','246'])).

thf('248',plain,(
    ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['235','247'])).

thf('249',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['232','248'])).

thf('250',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('251',plain,(
    sk_D = k1_xboole_0 ),
    inference(demod,[status(thm)],['231','249','250'])).

thf('252',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('253',plain,(
    $false ),
    inference(demod,[status(thm)],['199','251','252'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UouPkRgqZ9
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:38:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.88/2.08  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.88/2.08  % Solved by: fo/fo7.sh
% 1.88/2.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.88/2.08  % done 2154 iterations in 1.631s
% 1.88/2.08  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.88/2.08  % SZS output start Refutation
% 1.88/2.08  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.88/2.08  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.88/2.08  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.88/2.08  thf(sk_D_type, type, sk_D: $i).
% 1.88/2.08  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.88/2.08  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.88/2.08  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.88/2.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.88/2.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.88/2.08  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.88/2.08  thf(sk_A_type, type, sk_A: $i).
% 1.88/2.08  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.88/2.08  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.88/2.08  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.88/2.08  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.88/2.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.88/2.08  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.88/2.08  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.88/2.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.88/2.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.88/2.08  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.88/2.08  thf(sk_B_type, type, sk_B: $i > $i).
% 1.88/2.08  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.88/2.08  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.88/2.08  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.88/2.08  thf(t7_xboole_0, axiom,
% 1.88/2.08    (![A:$i]:
% 1.88/2.08     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.88/2.08          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.88/2.08  thf('0', plain,
% 1.88/2.08      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 1.88/2.08      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.88/2.08  thf(d10_xboole_0, axiom,
% 1.88/2.08    (![A:$i,B:$i]:
% 1.88/2.08     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.88/2.08  thf('1', plain,
% 1.88/2.08      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 1.88/2.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.88/2.08  thf('2', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 1.88/2.08      inference('simplify', [status(thm)], ['1'])).
% 1.88/2.08  thf(t3_subset, axiom,
% 1.88/2.08    (![A:$i,B:$i]:
% 1.88/2.08     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.88/2.08  thf('3', plain,
% 1.88/2.08      (![X11 : $i, X13 : $i]:
% 1.88/2.08         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 1.88/2.08      inference('cnf', [status(esa)], [t3_subset])).
% 1.88/2.08  thf('4', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['2', '3'])).
% 1.88/2.08  thf(t5_subset, axiom,
% 1.88/2.08    (![A:$i,B:$i,C:$i]:
% 1.88/2.08     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.88/2.08          ( v1_xboole_0 @ C ) ) ))).
% 1.88/2.08  thf('5', plain,
% 1.88/2.08      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.88/2.08         (~ (r2_hidden @ X14 @ X15)
% 1.88/2.08          | ~ (v1_xboole_0 @ X16)
% 1.88/2.08          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 1.88/2.08      inference('cnf', [status(esa)], [t5_subset])).
% 1.88/2.08  thf('6', plain,
% 1.88/2.08      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['4', '5'])).
% 1.88/2.08  thf('7', plain,
% 1.88/2.08      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['0', '6'])).
% 1.88/2.08  thf('8', plain,
% 1.88/2.08      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['0', '6'])).
% 1.88/2.08  thf(d3_tarski, axiom,
% 1.88/2.08    (![A:$i,B:$i]:
% 1.88/2.08     ( ( r1_tarski @ A @ B ) <=>
% 1.88/2.08       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.88/2.08  thf('9', plain,
% 1.88/2.08      (![X1 : $i, X3 : $i]:
% 1.88/2.08         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.88/2.08      inference('cnf', [status(esa)], [d3_tarski])).
% 1.88/2.08  thf(t113_zfmisc_1, axiom,
% 1.88/2.08    (![A:$i,B:$i]:
% 1.88/2.08     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.88/2.08       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.88/2.08  thf('10', plain,
% 1.88/2.08      (![X9 : $i, X10 : $i]:
% 1.88/2.08         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 1.88/2.08      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.88/2.08  thf('11', plain,
% 1.88/2.08      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 1.88/2.08      inference('simplify', [status(thm)], ['10'])).
% 1.88/2.08  thf(t29_relset_1, axiom,
% 1.88/2.08    (![A:$i]:
% 1.88/2.08     ( m1_subset_1 @
% 1.88/2.08       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.88/2.08  thf('12', plain,
% 1.88/2.08      (![X38 : $i]:
% 1.88/2.08         (m1_subset_1 @ (k6_relat_1 @ X38) @ 
% 1.88/2.08          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))),
% 1.88/2.08      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.88/2.08  thf('13', plain,
% 1.88/2.08      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 1.88/2.08      inference('sup+', [status(thm)], ['11', '12'])).
% 1.88/2.08  thf('14', plain,
% 1.88/2.08      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.88/2.08         (~ (r2_hidden @ X14 @ X15)
% 1.88/2.08          | ~ (v1_xboole_0 @ X16)
% 1.88/2.08          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 1.88/2.08      inference('cnf', [status(esa)], [t5_subset])).
% 1.88/2.08  thf('15', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.88/2.08          | ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['13', '14'])).
% 1.88/2.08  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.88/2.08  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.88/2.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.88/2.08  thf('17', plain,
% 1.88/2.08      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0))),
% 1.88/2.08      inference('demod', [status(thm)], ['15', '16'])).
% 1.88/2.08  thf('18', plain,
% 1.88/2.08      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 1.88/2.08      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.88/2.08  thf('19', plain,
% 1.88/2.08      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0))),
% 1.88/2.08      inference('demod', [status(thm)], ['15', '16'])).
% 1.88/2.08  thf('20', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['18', '19'])).
% 1.88/2.08  thf('21', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.88/2.08      inference('demod', [status(thm)], ['17', '20'])).
% 1.88/2.08  thf('22', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.88/2.08      inference('sup-', [status(thm)], ['9', '21'])).
% 1.88/2.08  thf('23', plain,
% 1.88/2.08      (![X11 : $i, X13 : $i]:
% 1.88/2.08         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 1.88/2.08      inference('cnf', [status(esa)], [t3_subset])).
% 1.88/2.08  thf('24', plain,
% 1.88/2.08      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['22', '23'])).
% 1.88/2.08  thf(redefinition_k1_relset_1, axiom,
% 1.88/2.08    (![A:$i,B:$i,C:$i]:
% 1.88/2.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.88/2.08       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.88/2.08  thf('25', plain,
% 1.88/2.08      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.88/2.08         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 1.88/2.08          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.88/2.08      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.88/2.08  thf('26', plain,
% 1.88/2.08      (![X0 : $i, X1 : $i]:
% 1.88/2.08         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['24', '25'])).
% 1.88/2.08  thf('27', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['18', '19'])).
% 1.88/2.08  thf(t71_relat_1, axiom,
% 1.88/2.08    (![A:$i]:
% 1.88/2.08     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.88/2.08       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.88/2.08  thf('28', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 1.88/2.08      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.88/2.08  thf('29', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.88/2.08      inference('sup+', [status(thm)], ['27', '28'])).
% 1.88/2.08  thf('30', plain,
% 1.88/2.08      (![X0 : $i, X1 : $i]:
% 1.88/2.08         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.88/2.08      inference('demod', [status(thm)], ['26', '29'])).
% 1.88/2.08  thf(d1_funct_2, axiom,
% 1.88/2.08    (![A:$i,B:$i,C:$i]:
% 1.88/2.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.88/2.08       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.88/2.08           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.88/2.08             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.88/2.08         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.88/2.08           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.88/2.08             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.88/2.08  thf(zf_stmt_0, axiom,
% 1.88/2.08    (![C:$i,B:$i,A:$i]:
% 1.88/2.08     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.88/2.08       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.88/2.08  thf('31', plain,
% 1.88/2.08      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.88/2.08         (((X41) != (k1_relset_1 @ X41 @ X42 @ X43))
% 1.88/2.08          | (v1_funct_2 @ X43 @ X41 @ X42)
% 1.88/2.08          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.88/2.08  thf('32', plain,
% 1.88/2.08      (![X0 : $i, X1 : $i]:
% 1.88/2.08         (((X1) != (k1_xboole_0))
% 1.88/2.08          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.88/2.08          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['30', '31'])).
% 1.88/2.08  thf('33', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.88/2.08          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.88/2.08      inference('simplify', [status(thm)], ['32'])).
% 1.88/2.08  thf(zf_stmt_1, axiom,
% 1.88/2.08    (![B:$i,A:$i]:
% 1.88/2.08     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.88/2.08       ( zip_tseitin_0 @ B @ A ) ))).
% 1.88/2.08  thf('34', plain,
% 1.88/2.08      (![X39 : $i, X40 : $i]:
% 1.88/2.08         ((zip_tseitin_0 @ X39 @ X40) | ((X40) != (k1_xboole_0)))),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.88/2.08  thf('35', plain, (![X39 : $i]: (zip_tseitin_0 @ X39 @ k1_xboole_0)),
% 1.88/2.08      inference('simplify', [status(thm)], ['34'])).
% 1.88/2.08  thf('36', plain,
% 1.88/2.08      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['22', '23'])).
% 1.88/2.08  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.88/2.08  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.88/2.08  thf(zf_stmt_4, axiom,
% 1.88/2.08    (![A:$i,B:$i,C:$i]:
% 1.88/2.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.88/2.08       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.88/2.08         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.88/2.08           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.88/2.08             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.88/2.08  thf('37', plain,
% 1.88/2.08      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.88/2.08         (~ (zip_tseitin_0 @ X44 @ X45)
% 1.88/2.08          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 1.88/2.08          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.88/2.08  thf('38', plain,
% 1.88/2.08      (![X0 : $i, X1 : $i]:
% 1.88/2.08         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.88/2.08      inference('sup-', [status(thm)], ['36', '37'])).
% 1.88/2.08  thf('39', plain,
% 1.88/2.08      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.88/2.08      inference('sup-', [status(thm)], ['35', '38'])).
% 1.88/2.08  thf('40', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.88/2.08      inference('demod', [status(thm)], ['33', '39'])).
% 1.88/2.08  thf('41', plain,
% 1.88/2.08      (![X0 : $i, X1 : $i]:
% 1.88/2.08         ((v1_funct_2 @ X0 @ k1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.88/2.08      inference('sup+', [status(thm)], ['8', '40'])).
% 1.88/2.08  thf('42', plain,
% 1.88/2.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.88/2.08         ((v1_funct_2 @ X2 @ X0 @ X1)
% 1.88/2.08          | ~ (v1_xboole_0 @ X0)
% 1.88/2.08          | ~ (v1_xboole_0 @ X2))),
% 1.88/2.08      inference('sup+', [status(thm)], ['7', '41'])).
% 1.88/2.08  thf(t8_funct_2, conjecture,
% 1.88/2.08    (![A:$i,B:$i,C:$i,D:$i]:
% 1.88/2.08     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.88/2.08         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.88/2.08       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 1.88/2.08         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.88/2.08           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.88/2.08             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 1.88/2.08  thf(zf_stmt_5, negated_conjecture,
% 1.88/2.08    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.88/2.08        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.88/2.08            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.88/2.08          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 1.88/2.08            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.88/2.08              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.88/2.08                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 1.88/2.08    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 1.88/2.08  thf('43', plain,
% 1.88/2.08      ((~ (v1_funct_1 @ sk_D)
% 1.88/2.08        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 1.88/2.08        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.88/2.08  thf('44', plain,
% 1.88/2.08      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 1.88/2.08         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 1.88/2.08      inference('split', [status(esa)], ['43'])).
% 1.88/2.08  thf('45', plain,
% 1.88/2.08      (((~ (v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A)))
% 1.88/2.08         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['42', '44'])).
% 1.88/2.08  thf('46', plain,
% 1.88/2.08      (![X1 : $i, X3 : $i]:
% 1.88/2.08         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.88/2.08      inference('cnf', [status(esa)], [d3_tarski])).
% 1.88/2.08  thf('47', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['2', '3'])).
% 1.88/2.08  thf(cc2_relset_1, axiom,
% 1.88/2.08    (![A:$i,B:$i,C:$i]:
% 1.88/2.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.88/2.08       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.88/2.08  thf('48', plain,
% 1.88/2.08      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.88/2.08         ((v4_relat_1 @ X26 @ X27)
% 1.88/2.08          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.88/2.08      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.88/2.08  thf('49', plain,
% 1.88/2.08      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 1.88/2.08      inference('sup-', [status(thm)], ['47', '48'])).
% 1.88/2.08  thf(d18_relat_1, axiom,
% 1.88/2.08    (![A:$i,B:$i]:
% 1.88/2.08     ( ( v1_relat_1 @ B ) =>
% 1.88/2.08       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.88/2.08  thf('50', plain,
% 1.88/2.08      (![X19 : $i, X20 : $i]:
% 1.88/2.08         (~ (v4_relat_1 @ X19 @ X20)
% 1.88/2.08          | (r1_tarski @ (k1_relat_1 @ X19) @ X20)
% 1.88/2.08          | ~ (v1_relat_1 @ X19))),
% 1.88/2.08      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.88/2.08  thf('51', plain,
% 1.88/2.08      (![X0 : $i, X1 : $i]:
% 1.88/2.08         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))
% 1.88/2.08          | (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['49', '50'])).
% 1.88/2.08  thf(fc6_relat_1, axiom,
% 1.88/2.08    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.88/2.08  thf('52', plain,
% 1.88/2.08      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 1.88/2.08      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.88/2.08  thf('53', plain,
% 1.88/2.08      (![X0 : $i, X1 : $i]:
% 1.88/2.08         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)),
% 1.88/2.08      inference('demod', [status(thm)], ['51', '52'])).
% 1.88/2.08  thf('54', plain,
% 1.88/2.08      (![X1 : $i, X3 : $i]:
% 1.88/2.08         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.88/2.08      inference('cnf', [status(esa)], [d3_tarski])).
% 1.88/2.08  thf('55', plain,
% 1.88/2.08      (![X39 : $i, X40 : $i]:
% 1.88/2.08         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.88/2.08  thf('56', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['18', '19'])).
% 1.88/2.08  thf('57', plain,
% 1.88/2.08      (![X0 : $i, X1 : $i]:
% 1.88/2.08         (((k6_relat_1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X1))),
% 1.88/2.08      inference('sup+', [status(thm)], ['55', '56'])).
% 1.88/2.08  thf('58', plain,
% 1.88/2.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.88/2.08  thf('59', plain,
% 1.88/2.08      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.88/2.08         (~ (zip_tseitin_0 @ X44 @ X45)
% 1.88/2.08          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 1.88/2.08          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.88/2.08  thf('60', plain,
% 1.88/2.08      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.88/2.08        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.88/2.08      inference('sup-', [status(thm)], ['58', '59'])).
% 1.88/2.08  thf('61', plain,
% 1.88/2.08      ((((k6_relat_1 @ sk_B_1) = (k1_xboole_0))
% 1.88/2.08        | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 1.88/2.08      inference('sup-', [status(thm)], ['57', '60'])).
% 1.88/2.08  thf('62', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.88/2.08  thf('63', plain,
% 1.88/2.08      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.88/2.08         (~ (v1_funct_2 @ X43 @ X41 @ X42)
% 1.88/2.08          | ((X41) = (k1_relset_1 @ X41 @ X42 @ X43))
% 1.88/2.08          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.88/2.08  thf('64', plain,
% 1.88/2.08      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.88/2.08        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['62', '63'])).
% 1.88/2.08  thf('65', plain,
% 1.88/2.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.88/2.08  thf('66', plain,
% 1.88/2.08      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.88/2.08         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 1.88/2.08          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.88/2.08      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.88/2.08  thf('67', plain,
% 1.88/2.08      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.88/2.08      inference('sup-', [status(thm)], ['65', '66'])).
% 1.88/2.08  thf('68', plain,
% 1.88/2.08      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.88/2.08        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.88/2.08      inference('demod', [status(thm)], ['64', '67'])).
% 1.88/2.08  thf('69', plain,
% 1.88/2.08      ((((k6_relat_1 @ sk_B_1) = (k1_xboole_0))
% 1.88/2.08        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['61', '68'])).
% 1.88/2.08  thf('70', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 1.88/2.08      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.88/2.08  thf('71', plain,
% 1.88/2.08      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['0', '6'])).
% 1.88/2.08  thf('72', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.88/2.08      inference('sup+', [status(thm)], ['27', '28'])).
% 1.88/2.08  thf('73', plain,
% 1.88/2.08      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.88/2.08      inference('sup+', [status(thm)], ['71', '72'])).
% 1.88/2.08  thf('74', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.88/2.08      inference('demod', [status(thm)], ['17', '20'])).
% 1.88/2.08  thf('75', plain,
% 1.88/2.08      (![X0 : $i, X1 : $i]:
% 1.88/2.08         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['73', '74'])).
% 1.88/2.08  thf('76', plain,
% 1.88/2.08      (![X0 : $i, X1 : $i]:
% 1.88/2.08         (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ (k6_relat_1 @ X0)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['70', '75'])).
% 1.88/2.08  thf('77', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.88/2.08          | ((sk_A) = (k1_relat_1 @ sk_D))
% 1.88/2.08          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.88/2.08      inference('sup-', [status(thm)], ['69', '76'])).
% 1.88/2.08  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.88/2.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.88/2.08  thf('79', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         (((sk_A) = (k1_relat_1 @ sk_D)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.88/2.08      inference('demod', [status(thm)], ['77', '78'])).
% 1.88/2.08  thf('80', plain,
% 1.88/2.08      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['54', '79'])).
% 1.88/2.08  thf('81', plain,
% 1.88/2.08      (![X5 : $i, X7 : $i]:
% 1.88/2.08         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 1.88/2.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.88/2.08  thf('82', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         (((sk_A) = (k1_relat_1 @ sk_D))
% 1.88/2.08          | ~ (r1_tarski @ X0 @ sk_B_1)
% 1.88/2.08          | ((X0) = (sk_B_1)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['80', '81'])).
% 1.88/2.08  thf('83', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         (((k1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ X0)) = (sk_B_1))
% 1.88/2.08          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['53', '82'])).
% 1.88/2.08  thf(t64_relat_1, axiom,
% 1.88/2.08    (![A:$i]:
% 1.88/2.08     ( ( v1_relat_1 @ A ) =>
% 1.88/2.08       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 1.88/2.08           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 1.88/2.08         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 1.88/2.08  thf('84', plain,
% 1.88/2.08      (![X23 : $i]:
% 1.88/2.08         (((k1_relat_1 @ X23) != (k1_xboole_0))
% 1.88/2.08          | ((X23) = (k1_xboole_0))
% 1.88/2.08          | ~ (v1_relat_1 @ X23))),
% 1.88/2.08      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.88/2.08  thf('85', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         (((sk_B_1) != (k1_xboole_0))
% 1.88/2.08          | ((sk_A) = (k1_relat_1 @ sk_D))
% 1.88/2.08          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ X0))
% 1.88/2.08          | ((k2_zfmisc_1 @ sk_B_1 @ X0) = (k1_xboole_0)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['83', '84'])).
% 1.88/2.08  thf('86', plain,
% 1.88/2.08      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 1.88/2.08      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.88/2.08  thf('87', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         (((sk_B_1) != (k1_xboole_0))
% 1.88/2.08          | ((sk_A) = (k1_relat_1 @ sk_D))
% 1.88/2.08          | ((k2_zfmisc_1 @ sk_B_1 @ X0) = (k1_xboole_0)))),
% 1.88/2.08      inference('demod', [status(thm)], ['85', '86'])).
% 1.88/2.08  thf('88', plain,
% 1.88/2.08      (![X39 : $i, X40 : $i]:
% 1.88/2.08         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.88/2.08  thf('89', plain,
% 1.88/2.08      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.88/2.08        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.88/2.08      inference('sup-', [status(thm)], ['58', '59'])).
% 1.88/2.08  thf('90', plain,
% 1.88/2.08      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 1.88/2.08      inference('sup-', [status(thm)], ['88', '89'])).
% 1.88/2.08  thf('91', plain,
% 1.88/2.08      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.88/2.08        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.88/2.08      inference('demod', [status(thm)], ['64', '67'])).
% 1.88/2.08  thf('92', plain,
% 1.88/2.08      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['90', '91'])).
% 1.88/2.08  thf('93', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         (((k2_zfmisc_1 @ sk_B_1 @ X0) = (k1_xboole_0))
% 1.88/2.08          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.88/2.08      inference('clc', [status(thm)], ['87', '92'])).
% 1.88/2.08  thf('94', plain,
% 1.88/2.08      (![X38 : $i]:
% 1.88/2.08         (m1_subset_1 @ (k6_relat_1 @ X38) @ 
% 1.88/2.08          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))),
% 1.88/2.08      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.88/2.08  thf('95', plain,
% 1.88/2.08      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.88/2.08         (~ (r2_hidden @ X14 @ X15)
% 1.88/2.08          | ~ (v1_xboole_0 @ X16)
% 1.88/2.08          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 1.88/2.08      inference('cnf', [status(esa)], [t5_subset])).
% 1.88/2.08  thf('96', plain,
% 1.88/2.08      (![X0 : $i, X1 : $i]:
% 1.88/2.08         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0))
% 1.88/2.08          | ~ (r2_hidden @ X1 @ (k6_relat_1 @ X0)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['94', '95'])).
% 1.88/2.08  thf('97', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.88/2.08          | ((sk_A) = (k1_relat_1 @ sk_D))
% 1.88/2.08          | ~ (r2_hidden @ X0 @ (k6_relat_1 @ sk_B_1)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['93', '96'])).
% 1.88/2.08  thf('98', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.88/2.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.88/2.08  thf('99', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         (((sk_A) = (k1_relat_1 @ sk_D))
% 1.88/2.08          | ~ (r2_hidden @ X0 @ (k6_relat_1 @ sk_B_1)))),
% 1.88/2.08      inference('demod', [status(thm)], ['97', '98'])).
% 1.88/2.08  thf('100', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         ((r1_tarski @ (k6_relat_1 @ sk_B_1) @ X0)
% 1.88/2.08          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['46', '99'])).
% 1.88/2.08  thf('101', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         (((sk_A) = (k1_relat_1 @ sk_D))
% 1.88/2.08          | ~ (r1_tarski @ X0 @ sk_B_1)
% 1.88/2.08          | ((X0) = (sk_B_1)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['80', '81'])).
% 1.88/2.08  thf('102', plain,
% 1.88/2.08      ((((sk_A) = (k1_relat_1 @ sk_D))
% 1.88/2.08        | ((k6_relat_1 @ sk_B_1) = (sk_B_1))
% 1.88/2.08        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['100', '101'])).
% 1.88/2.08  thf('103', plain,
% 1.88/2.08      ((((k6_relat_1 @ sk_B_1) = (sk_B_1)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.88/2.08      inference('simplify', [status(thm)], ['102'])).
% 1.88/2.08  thf('104', plain,
% 1.88/2.08      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['0', '6'])).
% 1.88/2.08  thf('105', plain,
% 1.88/2.08      (![X9 : $i, X10 : $i]:
% 1.88/2.08         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 1.88/2.08      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.88/2.08  thf('106', plain,
% 1.88/2.08      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 1.88/2.08      inference('simplify', [status(thm)], ['105'])).
% 1.88/2.08  thf('107', plain,
% 1.88/2.08      (![X0 : $i, X1 : $i]:
% 1.88/2.08         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.88/2.08      inference('sup+', [status(thm)], ['104', '106'])).
% 1.88/2.08  thf('108', plain,
% 1.88/2.08      (![X38 : $i]:
% 1.88/2.08         (m1_subset_1 @ (k6_relat_1 @ X38) @ 
% 1.88/2.08          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))),
% 1.88/2.08      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.88/2.08  thf('109', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         ((m1_subset_1 @ (k6_relat_1 @ X0) @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.88/2.08          | ~ (v1_xboole_0 @ X0))),
% 1.88/2.08      inference('sup+', [status(thm)], ['107', '108'])).
% 1.88/2.08  thf('110', plain,
% 1.88/2.08      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['0', '6'])).
% 1.88/2.08  thf('111', plain,
% 1.88/2.08      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 1.88/2.08      inference('simplify', [status(thm)], ['105'])).
% 1.88/2.08  thf('112', plain,
% 1.88/2.08      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.88/2.08         ((v4_relat_1 @ X26 @ X27)
% 1.88/2.08          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.88/2.08      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.88/2.08  thf('113', plain,
% 1.88/2.08      (![X1 : $i]:
% 1.88/2.08         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.88/2.08          | (v4_relat_1 @ X1 @ k1_xboole_0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['111', '112'])).
% 1.88/2.08  thf('114', plain,
% 1.88/2.08      (![X0 : $i, X1 : $i]:
% 1.88/2.08         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 1.88/2.08          | ~ (v1_xboole_0 @ X0)
% 1.88/2.08          | (v4_relat_1 @ X1 @ k1_xboole_0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['110', '113'])).
% 1.88/2.08  thf('115', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         (~ (v1_xboole_0 @ X0)
% 1.88/2.08          | (v4_relat_1 @ (k6_relat_1 @ X0) @ k1_xboole_0)
% 1.88/2.08          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['109', '114'])).
% 1.88/2.08  thf('116', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.88/2.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.88/2.08  thf('117', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         (~ (v1_xboole_0 @ X0) | (v4_relat_1 @ (k6_relat_1 @ X0) @ k1_xboole_0))),
% 1.88/2.08      inference('demod', [status(thm)], ['115', '116'])).
% 1.88/2.08  thf('118', plain,
% 1.88/2.08      (((v4_relat_1 @ sk_B_1 @ k1_xboole_0)
% 1.88/2.08        | ((sk_A) = (k1_relat_1 @ sk_D))
% 1.88/2.08        | ~ (v1_xboole_0 @ sk_B_1))),
% 1.88/2.08      inference('sup+', [status(thm)], ['103', '117'])).
% 1.88/2.08  thf('119', plain,
% 1.88/2.08      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['0', '6'])).
% 1.88/2.08  thf('120', plain,
% 1.88/2.08      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['0', '6'])).
% 1.88/2.08  thf('121', plain,
% 1.88/2.08      (![X0 : $i, X1 : $i]:
% 1.88/2.08         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.88/2.08      inference('sup+', [status(thm)], ['119', '120'])).
% 1.88/2.08  thf('122', plain, ((((sk_B_1) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.88/2.08  thf('123', plain,
% 1.88/2.08      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.88/2.08      inference('split', [status(esa)], ['122'])).
% 1.88/2.08  thf('124', plain,
% 1.88/2.08      ((![X0 : $i]:
% 1.88/2.08          (((X0) != (k1_xboole_0))
% 1.88/2.08           | ~ (v1_xboole_0 @ X0)
% 1.88/2.08           | ~ (v1_xboole_0 @ sk_B_1)))
% 1.88/2.08         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.88/2.08      inference('sup-', [status(thm)], ['121', '123'])).
% 1.88/2.08  thf('125', plain,
% 1.88/2.08      (((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.88/2.08         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.88/2.08      inference('simplify', [status(thm)], ['124'])).
% 1.88/2.08  thf('126', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.88/2.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.88/2.08  thf('127', plain,
% 1.88/2.08      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.88/2.08      inference('simplify_reflect+', [status(thm)], ['125', '126'])).
% 1.88/2.08  thf('128', plain, ((v1_funct_1 @ sk_D)),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.88/2.08  thf('129', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 1.88/2.08      inference('split', [status(esa)], ['43'])).
% 1.88/2.08  thf('130', plain, (((v1_funct_1 @ sk_D))),
% 1.88/2.08      inference('sup-', [status(thm)], ['128', '129'])).
% 1.88/2.08  thf('131', plain,
% 1.88/2.08      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.88/2.08      inference('demod', [status(thm)], ['33', '39'])).
% 1.88/2.08  thf('132', plain,
% 1.88/2.08      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 1.88/2.08      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.88/2.08  thf('133', plain,
% 1.88/2.08      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.88/2.08      inference('split', [status(esa)], ['122'])).
% 1.88/2.08  thf('134', plain,
% 1.88/2.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.88/2.08  thf('135', plain,
% 1.88/2.08      (((m1_subset_1 @ sk_D @ 
% 1.88/2.08         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 1.88/2.08         <= ((((sk_A) = (k1_xboole_0))))),
% 1.88/2.08      inference('sup+', [status(thm)], ['133', '134'])).
% 1.88/2.08  thf('136', plain,
% 1.88/2.08      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.88/2.08         (~ (r2_hidden @ X14 @ X15)
% 1.88/2.08          | ~ (v1_xboole_0 @ X16)
% 1.88/2.08          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 1.88/2.08      inference('cnf', [status(esa)], [t5_subset])).
% 1.88/2.08  thf('137', plain,
% 1.88/2.08      ((![X0 : $i]:
% 1.88/2.08          (~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 1.88/2.08           | ~ (r2_hidden @ X0 @ sk_D)))
% 1.88/2.08         <= ((((sk_A) = (k1_xboole_0))))),
% 1.88/2.08      inference('sup-', [status(thm)], ['135', '136'])).
% 1.88/2.08  thf('138', plain,
% 1.88/2.08      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 1.88/2.08      inference('simplify', [status(thm)], ['105'])).
% 1.88/2.08  thf('139', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.88/2.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.88/2.08  thf('140', plain,
% 1.88/2.08      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.88/2.08      inference('demod', [status(thm)], ['137', '138', '139'])).
% 1.88/2.08  thf('141', plain,
% 1.88/2.08      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.88/2.08      inference('sup-', [status(thm)], ['132', '140'])).
% 1.88/2.08  thf('142', plain,
% 1.88/2.08      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.88/2.08      inference('split', [status(esa)], ['122'])).
% 1.88/2.08  thf('143', plain,
% 1.88/2.08      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 1.88/2.08         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 1.88/2.08      inference('split', [status(esa)], ['43'])).
% 1.88/2.08  thf('144', plain,
% 1.88/2.08      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1))
% 1.88/2.08         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 1.88/2.08             (((sk_A) = (k1_xboole_0))))),
% 1.88/2.08      inference('sup-', [status(thm)], ['142', '143'])).
% 1.88/2.08  thf('145', plain,
% 1.88/2.08      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1))
% 1.88/2.08         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 1.88/2.08             (((sk_A) = (k1_xboole_0))))),
% 1.88/2.08      inference('sup-', [status(thm)], ['141', '144'])).
% 1.88/2.08  thf('146', plain,
% 1.88/2.08      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ (((sk_A) = (k1_xboole_0)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['131', '145'])).
% 1.88/2.08  thf('147', plain,
% 1.88/2.08      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 1.88/2.08      inference('simplify', [status(thm)], ['105'])).
% 1.88/2.08  thf('148', plain,
% 1.88/2.08      (((m1_subset_1 @ sk_D @ 
% 1.88/2.08         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 1.88/2.08         <= ((((sk_A) = (k1_xboole_0))))),
% 1.88/2.08      inference('sup+', [status(thm)], ['133', '134'])).
% 1.88/2.08  thf('149', plain,
% 1.88/2.08      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.88/2.08         <= ((((sk_A) = (k1_xboole_0))))),
% 1.88/2.08      inference('sup+', [status(thm)], ['147', '148'])).
% 1.88/2.08  thf('150', plain,
% 1.88/2.08      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 1.88/2.08      inference('simplify', [status(thm)], ['105'])).
% 1.88/2.08  thf('151', plain,
% 1.88/2.08      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.88/2.08      inference('split', [status(esa)], ['122'])).
% 1.88/2.08  thf('152', plain,
% 1.88/2.08      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 1.88/2.08         <= (~
% 1.88/2.08             ((m1_subset_1 @ sk_D @ 
% 1.88/2.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 1.88/2.08      inference('split', [status(esa)], ['43'])).
% 1.88/2.08  thf('153', plain,
% 1.88/2.08      ((~ (m1_subset_1 @ sk_D @ 
% 1.88/2.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 1.88/2.08         <= (~
% 1.88/2.08             ((m1_subset_1 @ sk_D @ 
% 1.88/2.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 1.88/2.08             (((sk_A) = (k1_xboole_0))))),
% 1.88/2.08      inference('sup-', [status(thm)], ['151', '152'])).
% 1.88/2.08  thf('154', plain,
% 1.88/2.08      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.88/2.08         <= (~
% 1.88/2.08             ((m1_subset_1 @ sk_D @ 
% 1.88/2.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 1.88/2.08             (((sk_A) = (k1_xboole_0))))),
% 1.88/2.08      inference('sup-', [status(thm)], ['150', '153'])).
% 1.88/2.08  thf('155', plain,
% 1.88/2.08      (~ (((sk_A) = (k1_xboole_0))) | 
% 1.88/2.08       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 1.88/2.08      inference('sup-', [status(thm)], ['149', '154'])).
% 1.88/2.08  thf('156', plain,
% 1.88/2.08      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 1.88/2.08       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ ((v1_funct_1 @ sk_D))),
% 1.88/2.08      inference('split', [status(esa)], ['43'])).
% 1.88/2.08  thf('157', plain,
% 1.88/2.08      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 1.88/2.08      inference('split', [status(esa)], ['122'])).
% 1.88/2.08  thf('158', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 1.88/2.08      inference('sat_resolution*', [status(thm)],
% 1.88/2.08                ['130', '146', '155', '156', '157'])).
% 1.88/2.08  thf('159', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.88/2.08      inference('simpl_trail', [status(thm)], ['127', '158'])).
% 1.88/2.08  thf('160', plain,
% 1.88/2.08      ((~ (v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.88/2.08      inference('clc', [status(thm)], ['118', '159'])).
% 1.88/2.08  thf('161', plain,
% 1.88/2.08      (![X39 : $i, X40 : $i]:
% 1.88/2.08         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.88/2.08  thf('162', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.88/2.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.88/2.08  thf('163', plain,
% 1.88/2.08      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.88/2.08      inference('sup+', [status(thm)], ['161', '162'])).
% 1.88/2.08  thf('164', plain,
% 1.88/2.08      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.88/2.08        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.88/2.08      inference('sup-', [status(thm)], ['58', '59'])).
% 1.88/2.08  thf('165', plain,
% 1.88/2.08      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 1.88/2.08      inference('sup-', [status(thm)], ['163', '164'])).
% 1.88/2.08  thf('166', plain,
% 1.88/2.08      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.88/2.08        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.88/2.08      inference('demod', [status(thm)], ['64', '67'])).
% 1.88/2.08  thf('167', plain,
% 1.88/2.08      (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['165', '166'])).
% 1.88/2.08  thf('168', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.88/2.08      inference('clc', [status(thm)], ['160', '167'])).
% 1.88/2.08  thf('169', plain,
% 1.88/2.08      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.88/2.08      inference('sup+', [status(thm)], ['71', '72'])).
% 1.88/2.08  thf('170', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.88/2.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.88/2.08  thf('171', plain,
% 1.88/2.08      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.88/2.08      inference('sup+', [status(thm)], ['169', '170'])).
% 1.88/2.08  thf('172', plain, (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_D))),
% 1.88/2.08      inference('sup+', [status(thm)], ['168', '171'])).
% 1.88/2.08  thf('173', plain,
% 1.88/2.08      ((~ (v1_xboole_0 @ sk_D)) <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 1.88/2.08      inference('clc', [status(thm)], ['45', '172'])).
% 1.88/2.08  thf('174', plain,
% 1.88/2.08      ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) @ sk_C_1)),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.88/2.08  thf('175', plain,
% 1.88/2.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.88/2.08  thf(redefinition_k2_relset_1, axiom,
% 1.88/2.08    (![A:$i,B:$i,C:$i]:
% 1.88/2.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.88/2.08       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.88/2.08  thf('176', plain,
% 1.88/2.08      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.88/2.08         (((k2_relset_1 @ X33 @ X34 @ X32) = (k2_relat_1 @ X32))
% 1.88/2.08          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 1.88/2.08      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.88/2.08  thf('177', plain,
% 1.88/2.08      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.88/2.08      inference('sup-', [status(thm)], ['175', '176'])).
% 1.88/2.08  thf('178', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)),
% 1.88/2.08      inference('demod', [status(thm)], ['174', '177'])).
% 1.88/2.08  thf('179', plain,
% 1.88/2.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.88/2.08  thf('180', plain,
% 1.88/2.08      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.88/2.08         ((v4_relat_1 @ X26 @ X27)
% 1.88/2.08          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.88/2.08      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.88/2.08  thf('181', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 1.88/2.08      inference('sup-', [status(thm)], ['179', '180'])).
% 1.88/2.08  thf('182', plain,
% 1.88/2.08      (![X19 : $i, X20 : $i]:
% 1.88/2.08         (~ (v4_relat_1 @ X19 @ X20)
% 1.88/2.08          | (r1_tarski @ (k1_relat_1 @ X19) @ X20)
% 1.88/2.08          | ~ (v1_relat_1 @ X19))),
% 1.88/2.08      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.88/2.08  thf('183', plain,
% 1.88/2.08      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A))),
% 1.88/2.08      inference('sup-', [status(thm)], ['181', '182'])).
% 1.88/2.08  thf('184', plain,
% 1.88/2.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.88/2.08  thf(cc2_relat_1, axiom,
% 1.88/2.08    (![A:$i]:
% 1.88/2.08     ( ( v1_relat_1 @ A ) =>
% 1.88/2.08       ( ![B:$i]:
% 1.88/2.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.88/2.08  thf('185', plain,
% 1.88/2.08      (![X17 : $i, X18 : $i]:
% 1.88/2.08         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 1.88/2.08          | (v1_relat_1 @ X17)
% 1.88/2.08          | ~ (v1_relat_1 @ X18))),
% 1.88/2.08      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.88/2.08  thf('186', plain,
% 1.88/2.08      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D))),
% 1.88/2.08      inference('sup-', [status(thm)], ['184', '185'])).
% 1.88/2.08  thf('187', plain,
% 1.88/2.08      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 1.88/2.08      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.88/2.08  thf('188', plain, ((v1_relat_1 @ sk_D)),
% 1.88/2.08      inference('demod', [status(thm)], ['186', '187'])).
% 1.88/2.08  thf('189', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A)),
% 1.88/2.08      inference('demod', [status(thm)], ['183', '188'])).
% 1.88/2.08  thf(t11_relset_1, axiom,
% 1.88/2.08    (![A:$i,B:$i,C:$i]:
% 1.88/2.08     ( ( v1_relat_1 @ C ) =>
% 1.88/2.08       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 1.88/2.08           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 1.88/2.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.88/2.08  thf('190', plain,
% 1.88/2.08      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.88/2.08         (~ (r1_tarski @ (k1_relat_1 @ X35) @ X36)
% 1.88/2.08          | ~ (r1_tarski @ (k2_relat_1 @ X35) @ X37)
% 1.88/2.08          | (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.88/2.08          | ~ (v1_relat_1 @ X35))),
% 1.88/2.08      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.88/2.08  thf('191', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         (~ (v1_relat_1 @ sk_D)
% 1.88/2.08          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.88/2.08          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['189', '190'])).
% 1.88/2.08  thf('192', plain, ((v1_relat_1 @ sk_D)),
% 1.88/2.08      inference('demod', [status(thm)], ['186', '187'])).
% 1.88/2.08  thf('193', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.88/2.08          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 1.88/2.08      inference('demod', [status(thm)], ['191', '192'])).
% 1.88/2.08  thf('194', plain,
% 1.88/2.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['178', '193'])).
% 1.88/2.08  thf('195', plain,
% 1.88/2.08      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 1.88/2.08         <= (~
% 1.88/2.08             ((m1_subset_1 @ sk_D @ 
% 1.88/2.08               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 1.88/2.08      inference('split', [status(esa)], ['43'])).
% 1.88/2.08  thf('196', plain,
% 1.88/2.08      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 1.88/2.08      inference('sup-', [status(thm)], ['194', '195'])).
% 1.88/2.08  thf('197', plain,
% 1.88/2.08      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | 
% 1.88/2.08       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 1.88/2.08       ~ ((v1_funct_1 @ sk_D))),
% 1.88/2.08      inference('split', [status(esa)], ['43'])).
% 1.88/2.08  thf('198', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 1.88/2.08      inference('sat_resolution*', [status(thm)], ['130', '196', '197'])).
% 1.88/2.08  thf('199', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.88/2.08      inference('simpl_trail', [status(thm)], ['173', '198'])).
% 1.88/2.08  thf('200', plain,
% 1.88/2.08      (![X39 : $i, X40 : $i]:
% 1.88/2.08         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.88/2.08  thf('201', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.88/2.08      inference('sup-', [status(thm)], ['9', '21'])).
% 1.88/2.08  thf('202', plain,
% 1.88/2.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.88/2.08         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 1.88/2.08      inference('sup+', [status(thm)], ['200', '201'])).
% 1.88/2.08  thf('203', plain,
% 1.88/2.08      ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) @ sk_C_1)),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.88/2.08  thf('204', plain,
% 1.88/2.08      (![X5 : $i, X7 : $i]:
% 1.88/2.08         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 1.88/2.08      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.88/2.08  thf('205', plain,
% 1.88/2.08      ((~ (r1_tarski @ sk_C_1 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D))
% 1.88/2.08        | ((sk_C_1) = (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['203', '204'])).
% 1.88/2.08  thf('206', plain,
% 1.88/2.08      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.88/2.08      inference('sup-', [status(thm)], ['175', '176'])).
% 1.88/2.08  thf('207', plain,
% 1.88/2.08      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.88/2.08      inference('sup-', [status(thm)], ['175', '176'])).
% 1.88/2.08  thf('208', plain,
% 1.88/2.08      ((~ (r1_tarski @ sk_C_1 @ (k2_relat_1 @ sk_D))
% 1.88/2.08        | ((sk_C_1) = (k2_relat_1 @ sk_D)))),
% 1.88/2.08      inference('demod', [status(thm)], ['205', '206', '207'])).
% 1.88/2.08  thf('209', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         ((zip_tseitin_0 @ sk_C_1 @ X0) | ((sk_C_1) = (k2_relat_1 @ sk_D)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['202', '208'])).
% 1.88/2.08  thf('210', plain,
% 1.88/2.08      (![X23 : $i]:
% 1.88/2.08         (((k2_relat_1 @ X23) != (k1_xboole_0))
% 1.88/2.08          | ((X23) = (k1_xboole_0))
% 1.88/2.08          | ~ (v1_relat_1 @ X23))),
% 1.88/2.08      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.88/2.08  thf('211', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         (((sk_C_1) != (k1_xboole_0))
% 1.88/2.08          | (zip_tseitin_0 @ sk_C_1 @ X0)
% 1.88/2.08          | ~ (v1_relat_1 @ sk_D)
% 1.88/2.08          | ((sk_D) = (k1_xboole_0)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['209', '210'])).
% 1.88/2.08  thf('212', plain, ((v1_relat_1 @ sk_D)),
% 1.88/2.08      inference('demod', [status(thm)], ['186', '187'])).
% 1.88/2.08  thf('213', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         (((sk_C_1) != (k1_xboole_0))
% 1.88/2.08          | (zip_tseitin_0 @ sk_C_1 @ X0)
% 1.88/2.08          | ((sk_D) = (k1_xboole_0)))),
% 1.88/2.08      inference('demod', [status(thm)], ['211', '212'])).
% 1.88/2.08  thf('214', plain,
% 1.88/2.08      (![X39 : $i, X40 : $i]:
% 1.88/2.08         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.88/2.08  thf('215', plain,
% 1.88/2.08      (![X0 : $i]: (((sk_D) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_C_1 @ X0))),
% 1.88/2.08      inference('clc', [status(thm)], ['213', '214'])).
% 1.88/2.08  thf('216', plain,
% 1.88/2.08      (![X0 : $i, X1 : $i]:
% 1.88/2.08         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.88/2.08      inference('sup-', [status(thm)], ['36', '37'])).
% 1.88/2.08  thf('217', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         (((sk_D) = (k1_xboole_0))
% 1.88/2.08          | (zip_tseitin_1 @ k1_xboole_0 @ sk_C_1 @ X0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['215', '216'])).
% 1.88/2.08  thf('218', plain,
% 1.88/2.08      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['0', '6'])).
% 1.88/2.08  thf('219', plain,
% 1.88/2.08      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.88/2.08         (((X44) != (k1_xboole_0))
% 1.88/2.08          | ((X45) = (k1_xboole_0))
% 1.88/2.08          | (v1_funct_2 @ X46 @ X45 @ X44)
% 1.88/2.08          | ((X46) != (k1_xboole_0))
% 1.88/2.08          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.88/2.08  thf('220', plain,
% 1.88/2.08      (![X45 : $i]:
% 1.88/2.08         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 1.88/2.08             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ k1_xboole_0)))
% 1.88/2.08          | (v1_funct_2 @ k1_xboole_0 @ X45 @ k1_xboole_0)
% 1.88/2.08          | ((X45) = (k1_xboole_0)))),
% 1.88/2.08      inference('simplify', [status(thm)], ['219'])).
% 1.88/2.08  thf('221', plain,
% 1.88/2.08      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 1.88/2.08      inference('simplify', [status(thm)], ['10'])).
% 1.88/2.08  thf('222', plain,
% 1.88/2.08      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['22', '23'])).
% 1.88/2.08  thf('223', plain,
% 1.88/2.08      (![X45 : $i]:
% 1.88/2.08         ((v1_funct_2 @ k1_xboole_0 @ X45 @ k1_xboole_0)
% 1.88/2.08          | ((X45) = (k1_xboole_0)))),
% 1.88/2.08      inference('demod', [status(thm)], ['220', '221', '222'])).
% 1.88/2.08  thf('224', plain,
% 1.88/2.08      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.88/2.08         (~ (v1_funct_2 @ X43 @ X41 @ X42)
% 1.88/2.08          | ((X41) = (k1_relset_1 @ X41 @ X42 @ X43))
% 1.88/2.08          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.88/2.08  thf('225', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         (((X0) = (k1_xboole_0))
% 1.88/2.08          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.88/2.08          | ((X0) = (k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['223', '224'])).
% 1.88/2.08  thf('226', plain,
% 1.88/2.08      (![X0 : $i, X1 : $i]:
% 1.88/2.08         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.88/2.08      inference('demod', [status(thm)], ['26', '29'])).
% 1.88/2.08  thf('227', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         (((X0) = (k1_xboole_0))
% 1.88/2.08          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.88/2.08          | ((X0) = (k1_xboole_0)))),
% 1.88/2.08      inference('demod', [status(thm)], ['225', '226'])).
% 1.88/2.08  thf('228', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.88/2.08          | ((X0) = (k1_xboole_0)))),
% 1.88/2.08      inference('simplify', [status(thm)], ['227'])).
% 1.88/2.08  thf('229', plain,
% 1.88/2.08      (![X0 : $i, X1 : $i]:
% 1.88/2.08         (~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.88/2.08          | ~ (v1_xboole_0 @ X0)
% 1.88/2.08          | ((X1) = (k1_xboole_0)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['218', '228'])).
% 1.88/2.08  thf('230', plain,
% 1.88/2.08      (![X0 : $i]:
% 1.88/2.08         (((sk_D) = (k1_xboole_0))
% 1.88/2.08          | ((X0) = (k1_xboole_0))
% 1.88/2.08          | ~ (v1_xboole_0 @ sk_C_1))),
% 1.88/2.08      inference('sup-', [status(thm)], ['217', '229'])).
% 1.88/2.08  thf('231', plain, ((((sk_D) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_C_1))),
% 1.88/2.08      inference('condensation', [status(thm)], ['230'])).
% 1.88/2.08  thf('232', plain,
% 1.88/2.08      (![X39 : $i, X40 : $i]:
% 1.88/2.08         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.88/2.08  thf('233', plain,
% 1.88/2.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['178', '193'])).
% 1.88/2.08  thf('234', plain,
% 1.88/2.08      (![X44 : $i, X45 : $i, X46 : $i]:
% 1.88/2.08         (~ (zip_tseitin_0 @ X44 @ X45)
% 1.88/2.08          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 1.88/2.08          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.88/2.08  thf('235', plain,
% 1.88/2.08      (((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 1.88/2.08        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_A))),
% 1.88/2.08      inference('sup-', [status(thm)], ['233', '234'])).
% 1.88/2.08  thf('236', plain,
% 1.88/2.08      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 1.88/2.08      inference('sup-', [status(thm)], ['178', '193'])).
% 1.88/2.08  thf('237', plain,
% 1.88/2.08      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.88/2.08         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 1.88/2.08          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 1.88/2.08      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.88/2.08  thf('238', plain,
% 1.88/2.08      (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.88/2.08      inference('sup-', [status(thm)], ['236', '237'])).
% 1.88/2.08  thf('239', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.88/2.08      inference('clc', [status(thm)], ['160', '167'])).
% 1.88/2.08  thf('240', plain, (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_D) = (sk_A))),
% 1.88/2.08      inference('demod', [status(thm)], ['238', '239'])).
% 1.88/2.08  thf('241', plain,
% 1.88/2.08      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.88/2.08         (((X41) != (k1_relset_1 @ X41 @ X42 @ X43))
% 1.88/2.08          | (v1_funct_2 @ X43 @ X41 @ X42)
% 1.88/2.08          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 1.88/2.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.88/2.08  thf('242', plain,
% 1.88/2.08      ((((sk_A) != (sk_A))
% 1.88/2.08        | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 1.88/2.08        | (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 1.88/2.08      inference('sup-', [status(thm)], ['240', '241'])).
% 1.88/2.08  thf('243', plain,
% 1.88/2.08      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 1.88/2.08        | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A))),
% 1.88/2.08      inference('simplify', [status(thm)], ['242'])).
% 1.88/2.08  thf('244', plain,
% 1.88/2.08      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 1.88/2.08         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 1.88/2.08      inference('split', [status(esa)], ['43'])).
% 1.88/2.08  thf('245', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 1.88/2.08      inference('sat_resolution*', [status(thm)], ['130', '196', '197'])).
% 1.88/2.08  thf('246', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)),
% 1.88/2.08      inference('simpl_trail', [status(thm)], ['244', '245'])).
% 1.88/2.08  thf('247', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)),
% 1.88/2.08      inference('clc', [status(thm)], ['243', '246'])).
% 1.88/2.08  thf('248', plain, (~ (zip_tseitin_0 @ sk_C_1 @ sk_A)),
% 1.88/2.08      inference('clc', [status(thm)], ['235', '247'])).
% 1.88/2.08  thf('249', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.88/2.08      inference('sup-', [status(thm)], ['232', '248'])).
% 1.88/2.08  thf('250', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.88/2.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.88/2.08  thf('251', plain, (((sk_D) = (k1_xboole_0))),
% 1.88/2.08      inference('demod', [status(thm)], ['231', '249', '250'])).
% 1.88/2.08  thf('252', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.88/2.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.88/2.08  thf('253', plain, ($false),
% 1.88/2.08      inference('demod', [status(thm)], ['199', '251', '252'])).
% 1.88/2.08  
% 1.88/2.08  % SZS output end Refutation
% 1.88/2.08  
% 1.88/2.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
