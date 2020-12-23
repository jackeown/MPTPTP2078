%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tO9d1znfdG

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:07 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  293 (1607 expanded)
%              Number of leaves         :   50 ( 502 expanded)
%              Depth                    :   36
%              Number of atoms          : 2017 (16231 expanded)
%              Number of equality atoms :  187 (1201 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('0',plain,(
    ! [X38: $i] :
      ( ( X38 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X38 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('11',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('12',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('13',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
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
    ! [X38: $i] :
      ( ( X38 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X38 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

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
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
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
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
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
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45
       != ( k1_relset_1 @ X45 @ X46 @ X47 ) )
      | ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ~ ( zip_tseitin_1 @ X47 @ X46 @ X45 ) ) ),
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
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X43 @ X44 )
      | ( X44 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('35',plain,(
    ! [X43: $i] :
      ( zip_tseitin_0 @ X43 @ k1_xboole_0 ) ),
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
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( zip_tseitin_0 @ X48 @ X49 )
      | ( zip_tseitin_1 @ X50 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ) ),
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
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('47',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('51',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('53',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('55',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('58',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X43 @ X44 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('59',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('62',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( zip_tseitin_0 @ X48 @ X49 )
      | ( zip_tseitin_1 @ X50 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('63',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k6_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('66',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ( X45
        = ( k1_relset_1 @ X45 @ X46 @ X47 ) )
      | ~ ( zip_tseitin_1 @ X47 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('69',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('70',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,
    ( ( ( k6_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['64','71'])).

thf('73',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('75',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['27','28'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['72','79'])).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['57','82'])).

thf('84',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( r1_tarski @ X0 @ sk_B_1 )
      | ( X0 = sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ X0 ) )
        = sk_B_1 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['56','85'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('87',plain,(
    ! [X22: $i] :
      ( ( ( k1_relat_1 @ X22 )
       != k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ X0 ) )
      | ( ( k2_zfmisc_1 @ sk_B_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( ( k2_zfmisc_1 @ sk_B_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X43 @ X44 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('92',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('93',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('95',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B_1 @ X0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['90','95'])).

thf('97',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('98',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( k6_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k6_relat_1 @ sk_B_1 ) @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['49','102'])).

thf('104',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( m1_subset_1 @ ( k6_relat_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relset_1 @ X1 @ X0 @ ( k6_relat_1 @ sk_B_1 ) )
        = ( k1_relat_1 @ ( k6_relat_1 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relset_1 @ X1 @ X0 @ ( k6_relat_1 @ sk_B_1 ) )
        = sk_B_1 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
        = sk_B_1 )
      | ~ ( v1_xboole_0 @ sk_B_1 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['48','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('112',plain,
    ( ( k1_xboole_0 = sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('114',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['113'])).

thf('115',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('116',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['43'])).

thf('117',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['33','39'])).

thf('119',plain,(
    ! [X38: $i] :
      ( ( X38 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X38 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf('120',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['113'])).

thf('121',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('122',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('124',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('126',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('128',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['124','126','127'])).

thf('129',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['119','128'])).

thf('130',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['113'])).

thf('131',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['43'])).

thf('132',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1 )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['129','132'])).

thf('134',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['118','133'])).

thf('135',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['125'])).

thf('136',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('137',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['125'])).

thf('139',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['113'])).

thf('140',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['43'])).

thf('141',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1 ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['138','141'])).

thf('143',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['137','142'])).

thf('144',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['43'])).

thf('145',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['113'])).

thf('146',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['117','134','143','144','145'])).

thf('147',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['114','146'])).

thf('148',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['112','147'])).

thf('149',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X43 @ X44 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('150',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('153',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('155',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['148','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('158',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['157','158'])).

thf('160',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['156','159'])).

thf('161',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['45','160'])).

thf('162',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('163',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('164',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('165',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C_1 ),
    inference(demod,[status(thm)],['162','165'])).

thf('167',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('168',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('169',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v4_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('171',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('173',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('174',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X20: $i,X21: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('176',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['171','176'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('178',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X34 ) @ X35 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X34 ) @ X36 )
      | ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('179',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['174','175'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['166','181'])).

thf('183',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['43'])).

thf('184',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['43'])).

thf('186',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['117','184','185'])).

thf('187',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['161','186'])).

thf('188',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X43 @ X44 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('189',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['9','21'])).

thf('190',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['188','189'])).

thf('191',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('192',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('193',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) )
    | ( sk_C_1
      = ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('195',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('196',plain,
    ( ~ ( r1_tarski @ sk_C_1 @ ( k2_relat_1 @ sk_D ) )
    | ( sk_C_1
      = ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['193','194','195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C_1 @ X0 )
      | ( sk_C_1
        = ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['190','196'])).

thf('198',plain,(
    ! [X22: $i] :
      ( ( ( k2_relat_1 @ X22 )
       != k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( sk_D = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['174','175'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( sk_C_1 != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X0 )
      | ( sk_D = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X43 @ X44 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('207',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( X48 != k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ( v1_funct_2 @ X50 @ X49 @ X48 )
      | ( X50 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('208',plain,(
    ! [X49: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X49 @ k1_xboole_0 )
      | ( X49 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('210',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('211',plain,(
    ! [X49: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X49 @ k1_xboole_0 )
      | ( X49 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['208','209','210'])).

thf('212',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ( X45
        = ( k1_relset_1 @ X45 @ X46 @ X47 ) )
      | ~ ( zip_tseitin_1 @ X47 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0
        = ( k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','29'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['206','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['205','217'])).

thf('219',plain,
    ( ( sk_D = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(condensation,[status(thm)],['218'])).

thf('220',plain,(
    ! [X43: $i,X44: $i] :
      ( ( zip_tseitin_0 @ X43 @ X44 )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('221',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['166','181'])).

thf('222',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( zip_tseitin_0 @ X48 @ X49 )
      | ( zip_tseitin_1 @ X50 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('223',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['166','181'])).

thf('225',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('226',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['148','155'])).

thf('228',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['226','227'])).

thf('229',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45
       != ( k1_relset_1 @ X45 @ X46 @ X47 ) )
      | ( v1_funct_2 @ X47 @ X45 @ X46 )
      | ~ ( zip_tseitin_1 @ X47 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['230'])).

thf('232',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['43'])).

thf('233',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['117','184','185'])).

thf('234',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['232','233'])).

thf('235',plain,(
    ~ ( zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['231','234'])).

thf('236',plain,(
    ~ ( zip_tseitin_0 @ sk_C_1 @ sk_A ) ),
    inference(clc,[status(thm)],['223','235'])).

thf('237',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['220','236'])).

thf('238',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('239',plain,(
    sk_D = k1_xboole_0 ),
    inference(demod,[status(thm)],['219','237','238'])).

thf('240',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('241',plain,(
    $false ),
    inference(demod,[status(thm)],['187','239','240'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tO9d1znfdG
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:54:33 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.81/2.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.81/2.03  % Solved by: fo/fo7.sh
% 1.81/2.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.81/2.03  % done 2130 iterations in 1.571s
% 1.81/2.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.81/2.03  % SZS output start Refutation
% 1.81/2.03  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.81/2.03  thf(sk_D_type, type, sk_D: $i).
% 1.81/2.03  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.81/2.03  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.81/2.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.81/2.03  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.81/2.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.81/2.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.81/2.03  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.81/2.03  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.81/2.03  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 1.81/2.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.81/2.03  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.81/2.03  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.81/2.03  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.81/2.03  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.81/2.03  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.81/2.03  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.81/2.03  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.81/2.03  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.81/2.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.81/2.03  thf(sk_A_type, type, sk_A: $i).
% 1.81/2.03  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.81/2.03  thf(sk_B_type, type, sk_B: $i > $i).
% 1.81/2.03  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.81/2.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.81/2.03  thf(t34_mcart_1, axiom,
% 1.81/2.03    (![A:$i]:
% 1.81/2.03     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.81/2.03          ( ![B:$i]:
% 1.81/2.03            ( ~( ( r2_hidden @ B @ A ) & 
% 1.81/2.03                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 1.81/2.03                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 1.81/2.03                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 1.81/2.03  thf('0', plain,
% 1.81/2.03      (![X38 : $i]:
% 1.81/2.03         (((X38) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X38) @ X38))),
% 1.81/2.03      inference('cnf', [status(esa)], [t34_mcart_1])).
% 1.81/2.03  thf(d10_xboole_0, axiom,
% 1.81/2.03    (![A:$i,B:$i]:
% 1.81/2.03     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.81/2.03  thf('1', plain,
% 1.81/2.03      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 1.81/2.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.81/2.03  thf('2', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.81/2.03      inference('simplify', [status(thm)], ['1'])).
% 1.81/2.03  thf(t3_subset, axiom,
% 1.81/2.03    (![A:$i,B:$i]:
% 1.81/2.03     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.81/2.03  thf('3', plain,
% 1.81/2.03      (![X10 : $i, X12 : $i]:
% 1.81/2.03         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 1.81/2.03      inference('cnf', [status(esa)], [t3_subset])).
% 1.81/2.03  thf('4', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.81/2.03      inference('sup-', [status(thm)], ['2', '3'])).
% 1.81/2.03  thf(t5_subset, axiom,
% 1.81/2.03    (![A:$i,B:$i,C:$i]:
% 1.81/2.03     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.81/2.03          ( v1_xboole_0 @ C ) ) ))).
% 1.81/2.03  thf('5', plain,
% 1.81/2.03      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.81/2.03         (~ (r2_hidden @ X13 @ X14)
% 1.81/2.03          | ~ (v1_xboole_0 @ X15)
% 1.81/2.03          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 1.81/2.03      inference('cnf', [status(esa)], [t5_subset])).
% 1.81/2.03  thf('6', plain,
% 1.81/2.03      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 1.81/2.03      inference('sup-', [status(thm)], ['4', '5'])).
% 1.81/2.03  thf('7', plain,
% 1.81/2.03      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.81/2.03      inference('sup-', [status(thm)], ['0', '6'])).
% 1.81/2.03  thf('8', plain,
% 1.81/2.03      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.81/2.03      inference('sup-', [status(thm)], ['0', '6'])).
% 1.81/2.03  thf(d3_tarski, axiom,
% 1.81/2.03    (![A:$i,B:$i]:
% 1.81/2.03     ( ( r1_tarski @ A @ B ) <=>
% 1.81/2.03       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.81/2.03  thf('9', plain,
% 1.81/2.03      (![X1 : $i, X3 : $i]:
% 1.81/2.03         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.81/2.03      inference('cnf', [status(esa)], [d3_tarski])).
% 1.81/2.03  thf(t113_zfmisc_1, axiom,
% 1.81/2.03    (![A:$i,B:$i]:
% 1.81/2.03     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.81/2.03       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.81/2.03  thf('10', plain,
% 1.81/2.03      (![X8 : $i, X9 : $i]:
% 1.81/2.03         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 1.81/2.03      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.81/2.03  thf('11', plain,
% 1.81/2.03      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 1.81/2.03      inference('simplify', [status(thm)], ['10'])).
% 1.81/2.03  thf(t29_relset_1, axiom,
% 1.81/2.03    (![A:$i]:
% 1.81/2.03     ( m1_subset_1 @
% 1.81/2.03       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.81/2.03  thf('12', plain,
% 1.81/2.03      (![X37 : $i]:
% 1.81/2.03         (m1_subset_1 @ (k6_relat_1 @ X37) @ 
% 1.81/2.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 1.81/2.03      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.81/2.03  thf('13', plain,
% 1.81/2.03      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 1.81/2.03      inference('sup+', [status(thm)], ['11', '12'])).
% 1.81/2.03  thf('14', plain,
% 1.81/2.03      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.81/2.03         (~ (r2_hidden @ X13 @ X14)
% 1.81/2.03          | ~ (v1_xboole_0 @ X15)
% 1.81/2.03          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 1.81/2.03      inference('cnf', [status(esa)], [t5_subset])).
% 1.81/2.03  thf('15', plain,
% 1.81/2.03      (![X0 : $i]:
% 1.81/2.03         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.81/2.03          | ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0)))),
% 1.81/2.03      inference('sup-', [status(thm)], ['13', '14'])).
% 1.81/2.03  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.81/2.03  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.81/2.03      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.81/2.03  thf('17', plain,
% 1.81/2.03      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0))),
% 1.81/2.03      inference('demod', [status(thm)], ['15', '16'])).
% 1.81/2.03  thf('18', plain,
% 1.81/2.03      (![X38 : $i]:
% 1.81/2.03         (((X38) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X38) @ X38))),
% 1.81/2.03      inference('cnf', [status(esa)], [t34_mcart_1])).
% 1.81/2.03  thf('19', plain,
% 1.81/2.03      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k6_relat_1 @ k1_xboole_0))),
% 1.81/2.03      inference('demod', [status(thm)], ['15', '16'])).
% 1.81/2.03  thf('20', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.81/2.03      inference('sup-', [status(thm)], ['18', '19'])).
% 1.81/2.03  thf('21', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.81/2.03      inference('demod', [status(thm)], ['17', '20'])).
% 1.81/2.03  thf('22', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.81/2.03      inference('sup-', [status(thm)], ['9', '21'])).
% 1.81/2.03  thf('23', plain,
% 1.81/2.03      (![X10 : $i, X12 : $i]:
% 1.81/2.03         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 1.81/2.03      inference('cnf', [status(esa)], [t3_subset])).
% 1.81/2.03  thf('24', plain,
% 1.81/2.03      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.81/2.03      inference('sup-', [status(thm)], ['22', '23'])).
% 1.81/2.03  thf(redefinition_k1_relset_1, axiom,
% 1.81/2.03    (![A:$i,B:$i,C:$i]:
% 1.81/2.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.81/2.03       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.81/2.03  thf('25', plain,
% 1.81/2.03      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.81/2.03         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 1.81/2.03          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.81/2.03      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.81/2.03  thf('26', plain,
% 1.81/2.03      (![X0 : $i, X1 : $i]:
% 1.81/2.03         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 1.81/2.03      inference('sup-', [status(thm)], ['24', '25'])).
% 1.81/2.03  thf('27', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.81/2.03      inference('sup-', [status(thm)], ['18', '19'])).
% 1.81/2.03  thf(t71_relat_1, axiom,
% 1.81/2.03    (![A:$i]:
% 1.81/2.03     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.81/2.03       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.81/2.03  thf('28', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 1.81/2.03      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.81/2.03  thf('29', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.81/2.03      inference('sup+', [status(thm)], ['27', '28'])).
% 1.81/2.03  thf('30', plain,
% 1.81/2.03      (![X0 : $i, X1 : $i]:
% 1.81/2.03         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.81/2.03      inference('demod', [status(thm)], ['26', '29'])).
% 1.81/2.03  thf(d1_funct_2, axiom,
% 1.81/2.03    (![A:$i,B:$i,C:$i]:
% 1.81/2.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.81/2.03       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.81/2.03           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.81/2.03             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.81/2.03         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.81/2.03           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.81/2.03             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.81/2.03  thf(zf_stmt_0, axiom,
% 1.81/2.03    (![C:$i,B:$i,A:$i]:
% 1.81/2.03     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.81/2.03       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.81/2.03  thf('31', plain,
% 1.81/2.03      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.81/2.03         (((X45) != (k1_relset_1 @ X45 @ X46 @ X47))
% 1.81/2.03          | (v1_funct_2 @ X47 @ X45 @ X46)
% 1.81/2.03          | ~ (zip_tseitin_1 @ X47 @ X46 @ X45))),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.03  thf('32', plain,
% 1.81/2.03      (![X0 : $i, X1 : $i]:
% 1.81/2.03         (((X1) != (k1_xboole_0))
% 1.81/2.03          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.81/2.03          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 1.81/2.03      inference('sup-', [status(thm)], ['30', '31'])).
% 1.81/2.03  thf('33', plain,
% 1.81/2.03      (![X0 : $i]:
% 1.81/2.03         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.81/2.03          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.81/2.03      inference('simplify', [status(thm)], ['32'])).
% 1.81/2.03  thf(zf_stmt_1, axiom,
% 1.81/2.03    (![B:$i,A:$i]:
% 1.81/2.03     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.81/2.03       ( zip_tseitin_0 @ B @ A ) ))).
% 1.81/2.03  thf('34', plain,
% 1.81/2.03      (![X43 : $i, X44 : $i]:
% 1.81/2.03         ((zip_tseitin_0 @ X43 @ X44) | ((X44) != (k1_xboole_0)))),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.81/2.03  thf('35', plain, (![X43 : $i]: (zip_tseitin_0 @ X43 @ k1_xboole_0)),
% 1.81/2.03      inference('simplify', [status(thm)], ['34'])).
% 1.81/2.03  thf('36', plain,
% 1.81/2.03      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.81/2.03      inference('sup-', [status(thm)], ['22', '23'])).
% 1.81/2.03  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.81/2.03  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.81/2.03  thf(zf_stmt_4, axiom,
% 1.81/2.03    (![A:$i,B:$i,C:$i]:
% 1.81/2.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.81/2.03       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.81/2.03         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.81/2.03           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.81/2.03             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.81/2.03  thf('37', plain,
% 1.81/2.03      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.81/2.03         (~ (zip_tseitin_0 @ X48 @ X49)
% 1.81/2.03          | (zip_tseitin_1 @ X50 @ X48 @ X49)
% 1.81/2.03          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48))))),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.81/2.03  thf('38', plain,
% 1.81/2.03      (![X0 : $i, X1 : $i]:
% 1.81/2.03         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.81/2.03      inference('sup-', [status(thm)], ['36', '37'])).
% 1.81/2.03  thf('39', plain,
% 1.81/2.03      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.81/2.03      inference('sup-', [status(thm)], ['35', '38'])).
% 1.81/2.03  thf('40', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.81/2.03      inference('demod', [status(thm)], ['33', '39'])).
% 1.81/2.03  thf('41', plain,
% 1.81/2.03      (![X0 : $i, X1 : $i]:
% 1.81/2.03         ((v1_funct_2 @ X0 @ k1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.81/2.03      inference('sup+', [status(thm)], ['8', '40'])).
% 1.81/2.03  thf('42', plain,
% 1.81/2.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.81/2.03         ((v1_funct_2 @ X2 @ X0 @ X1)
% 1.81/2.03          | ~ (v1_xboole_0 @ X0)
% 1.81/2.03          | ~ (v1_xboole_0 @ X2))),
% 1.81/2.03      inference('sup+', [status(thm)], ['7', '41'])).
% 1.81/2.03  thf(t8_funct_2, conjecture,
% 1.81/2.03    (![A:$i,B:$i,C:$i,D:$i]:
% 1.81/2.03     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.81/2.03         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.81/2.03       ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 1.81/2.03         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.81/2.03           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.81/2.03             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 1.81/2.03  thf(zf_stmt_5, negated_conjecture,
% 1.81/2.03    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.81/2.03        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.81/2.03            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.81/2.03          ( ( r1_tarski @ ( k2_relset_1 @ A @ B @ D ) @ C ) =>
% 1.81/2.03            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 1.81/2.03              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 1.81/2.03                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 1.81/2.03    inference('cnf.neg', [status(esa)], [t8_funct_2])).
% 1.81/2.03  thf('43', plain,
% 1.81/2.03      ((~ (v1_funct_1 @ sk_D)
% 1.81/2.03        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 1.81/2.03        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.81/2.03  thf('44', plain,
% 1.81/2.03      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 1.81/2.03         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 1.81/2.03      inference('split', [status(esa)], ['43'])).
% 1.81/2.03  thf('45', plain,
% 1.81/2.03      (((~ (v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A)))
% 1.81/2.03         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 1.81/2.03      inference('sup-', [status(thm)], ['42', '44'])).
% 1.81/2.03  thf('46', plain,
% 1.81/2.03      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.81/2.03      inference('sup-', [status(thm)], ['0', '6'])).
% 1.81/2.03  thf('47', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.81/2.03      inference('sup-', [status(thm)], ['18', '19'])).
% 1.81/2.03  thf('48', plain,
% 1.81/2.03      (![X0 : $i]: (((k6_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.81/2.03      inference('sup+', [status(thm)], ['46', '47'])).
% 1.81/2.03  thf('49', plain,
% 1.81/2.03      (![X1 : $i, X3 : $i]:
% 1.81/2.03         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.81/2.03      inference('cnf', [status(esa)], [d3_tarski])).
% 1.81/2.03  thf('50', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.81/2.03      inference('sup-', [status(thm)], ['2', '3'])).
% 1.81/2.03  thf(cc2_relset_1, axiom,
% 1.81/2.03    (![A:$i,B:$i,C:$i]:
% 1.81/2.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.81/2.03       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.81/2.03  thf('51', plain,
% 1.81/2.03      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.81/2.03         ((v4_relat_1 @ X25 @ X26)
% 1.81/2.03          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.81/2.03      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.81/2.03  thf('52', plain,
% 1.81/2.03      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 1.81/2.03      inference('sup-', [status(thm)], ['50', '51'])).
% 1.81/2.03  thf(d18_relat_1, axiom,
% 1.81/2.03    (![A:$i,B:$i]:
% 1.81/2.03     ( ( v1_relat_1 @ B ) =>
% 1.81/2.03       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.81/2.03  thf('53', plain,
% 1.81/2.03      (![X18 : $i, X19 : $i]:
% 1.81/2.03         (~ (v4_relat_1 @ X18 @ X19)
% 1.81/2.03          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 1.81/2.03          | ~ (v1_relat_1 @ X18))),
% 1.81/2.03      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.81/2.03  thf('54', plain,
% 1.81/2.03      (![X0 : $i, X1 : $i]:
% 1.81/2.03         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))
% 1.81/2.03          | (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0))),
% 1.81/2.03      inference('sup-', [status(thm)], ['52', '53'])).
% 1.81/2.03  thf(fc6_relat_1, axiom,
% 1.81/2.03    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.81/2.03  thf('55', plain,
% 1.81/2.03      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 1.81/2.03      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.81/2.03  thf('56', plain,
% 1.81/2.03      (![X0 : $i, X1 : $i]:
% 1.81/2.03         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)),
% 1.81/2.03      inference('demod', [status(thm)], ['54', '55'])).
% 1.81/2.03  thf('57', plain,
% 1.81/2.03      (![X1 : $i, X3 : $i]:
% 1.81/2.03         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.81/2.03      inference('cnf', [status(esa)], [d3_tarski])).
% 1.81/2.03  thf('58', plain,
% 1.81/2.03      (![X43 : $i, X44 : $i]:
% 1.81/2.03         ((zip_tseitin_0 @ X43 @ X44) | ((X43) = (k1_xboole_0)))),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.81/2.03  thf('59', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.81/2.03      inference('sup-', [status(thm)], ['18', '19'])).
% 1.81/2.03  thf('60', plain,
% 1.81/2.03      (![X0 : $i, X1 : $i]:
% 1.81/2.03         (((k6_relat_1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X1))),
% 1.81/2.03      inference('sup+', [status(thm)], ['58', '59'])).
% 1.81/2.03  thf('61', plain,
% 1.81/2.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.81/2.03  thf('62', plain,
% 1.81/2.03      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.81/2.03         (~ (zip_tseitin_0 @ X48 @ X49)
% 1.81/2.03          | (zip_tseitin_1 @ X50 @ X48 @ X49)
% 1.81/2.03          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48))))),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.81/2.03  thf('63', plain,
% 1.81/2.03      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.81/2.03        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.81/2.03      inference('sup-', [status(thm)], ['61', '62'])).
% 1.81/2.03  thf('64', plain,
% 1.81/2.03      ((((k6_relat_1 @ sk_B_1) = (k1_xboole_0))
% 1.81/2.03        | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 1.81/2.03      inference('sup-', [status(thm)], ['60', '63'])).
% 1.81/2.03  thf('65', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.81/2.03  thf('66', plain,
% 1.81/2.03      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.81/2.03         (~ (v1_funct_2 @ X47 @ X45 @ X46)
% 1.81/2.03          | ((X45) = (k1_relset_1 @ X45 @ X46 @ X47))
% 1.81/2.03          | ~ (zip_tseitin_1 @ X47 @ X46 @ X45))),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.03  thf('67', plain,
% 1.81/2.03      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.81/2.03        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 1.81/2.03      inference('sup-', [status(thm)], ['65', '66'])).
% 1.81/2.03  thf('68', plain,
% 1.81/2.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.81/2.03  thf('69', plain,
% 1.81/2.03      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.81/2.03         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 1.81/2.03          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.81/2.03      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.81/2.03  thf('70', plain,
% 1.81/2.03      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.81/2.03      inference('sup-', [status(thm)], ['68', '69'])).
% 1.81/2.03  thf('71', plain,
% 1.81/2.03      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.81/2.03        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.81/2.03      inference('demod', [status(thm)], ['67', '70'])).
% 1.81/2.03  thf('72', plain,
% 1.81/2.03      ((((k6_relat_1 @ sk_B_1) = (k1_xboole_0))
% 1.81/2.03        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.81/2.03      inference('sup-', [status(thm)], ['64', '71'])).
% 1.81/2.03  thf('73', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 1.81/2.03      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.81/2.03  thf('74', plain,
% 1.81/2.03      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.81/2.03      inference('sup-', [status(thm)], ['0', '6'])).
% 1.81/2.03  thf('75', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.81/2.03      inference('sup+', [status(thm)], ['27', '28'])).
% 1.81/2.03  thf('76', plain,
% 1.81/2.03      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.81/2.03      inference('sup+', [status(thm)], ['74', '75'])).
% 1.81/2.03  thf('77', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.81/2.03      inference('demod', [status(thm)], ['17', '20'])).
% 1.81/2.03  thf('78', plain,
% 1.81/2.03      (![X0 : $i, X1 : $i]:
% 1.81/2.03         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.81/2.03      inference('sup-', [status(thm)], ['76', '77'])).
% 1.81/2.03  thf('79', plain,
% 1.81/2.03      (![X0 : $i, X1 : $i]:
% 1.81/2.03         (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ (k6_relat_1 @ X0)))),
% 1.81/2.03      inference('sup-', [status(thm)], ['73', '78'])).
% 1.81/2.03  thf('80', plain,
% 1.81/2.03      (![X0 : $i]:
% 1.81/2.03         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.81/2.03          | ((sk_A) = (k1_relat_1 @ sk_D))
% 1.81/2.03          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.81/2.03      inference('sup-', [status(thm)], ['72', '79'])).
% 1.81/2.03  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.81/2.03      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.81/2.03  thf('82', plain,
% 1.81/2.03      (![X0 : $i]:
% 1.81/2.03         (((sk_A) = (k1_relat_1 @ sk_D)) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.81/2.03      inference('demod', [status(thm)], ['80', '81'])).
% 1.81/2.03  thf('83', plain,
% 1.81/2.03      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.81/2.03      inference('sup-', [status(thm)], ['57', '82'])).
% 1.81/2.03  thf('84', plain,
% 1.81/2.03      (![X4 : $i, X6 : $i]:
% 1.81/2.03         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.81/2.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.81/2.03  thf('85', plain,
% 1.81/2.03      (![X0 : $i]:
% 1.81/2.03         (((sk_A) = (k1_relat_1 @ sk_D))
% 1.81/2.03          | ~ (r1_tarski @ X0 @ sk_B_1)
% 1.81/2.03          | ((X0) = (sk_B_1)))),
% 1.81/2.03      inference('sup-', [status(thm)], ['83', '84'])).
% 1.81/2.03  thf('86', plain,
% 1.81/2.03      (![X0 : $i]:
% 1.81/2.03         (((k1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ X0)) = (sk_B_1))
% 1.81/2.03          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.81/2.03      inference('sup-', [status(thm)], ['56', '85'])).
% 1.81/2.03  thf(t64_relat_1, axiom,
% 1.81/2.03    (![A:$i]:
% 1.81/2.03     ( ( v1_relat_1 @ A ) =>
% 1.81/2.03       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 1.81/2.03           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 1.81/2.03         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 1.81/2.03  thf('87', plain,
% 1.81/2.03      (![X22 : $i]:
% 1.81/2.03         (((k1_relat_1 @ X22) != (k1_xboole_0))
% 1.81/2.03          | ((X22) = (k1_xboole_0))
% 1.81/2.03          | ~ (v1_relat_1 @ X22))),
% 1.81/2.03      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.81/2.03  thf('88', plain,
% 1.81/2.03      (![X0 : $i]:
% 1.81/2.03         (((sk_B_1) != (k1_xboole_0))
% 1.81/2.03          | ((sk_A) = (k1_relat_1 @ sk_D))
% 1.81/2.03          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ X0))
% 1.81/2.03          | ((k2_zfmisc_1 @ sk_B_1 @ X0) = (k1_xboole_0)))),
% 1.81/2.03      inference('sup-', [status(thm)], ['86', '87'])).
% 1.81/2.03  thf('89', plain,
% 1.81/2.03      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 1.81/2.03      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.81/2.03  thf('90', plain,
% 1.81/2.03      (![X0 : $i]:
% 1.81/2.03         (((sk_B_1) != (k1_xboole_0))
% 1.81/2.03          | ((sk_A) = (k1_relat_1 @ sk_D))
% 1.81/2.03          | ((k2_zfmisc_1 @ sk_B_1 @ X0) = (k1_xboole_0)))),
% 1.81/2.03      inference('demod', [status(thm)], ['88', '89'])).
% 1.81/2.03  thf('91', plain,
% 1.81/2.03      (![X43 : $i, X44 : $i]:
% 1.81/2.03         ((zip_tseitin_0 @ X43 @ X44) | ((X43) = (k1_xboole_0)))),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.81/2.03  thf('92', plain,
% 1.81/2.03      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.81/2.03        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.81/2.03      inference('sup-', [status(thm)], ['61', '62'])).
% 1.81/2.03  thf('93', plain,
% 1.81/2.03      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 1.81/2.03      inference('sup-', [status(thm)], ['91', '92'])).
% 1.81/2.03  thf('94', plain,
% 1.81/2.03      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.81/2.03        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.81/2.03      inference('demod', [status(thm)], ['67', '70'])).
% 1.81/2.03  thf('95', plain,
% 1.81/2.03      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.81/2.03      inference('sup-', [status(thm)], ['93', '94'])).
% 1.81/2.03  thf('96', plain,
% 1.81/2.03      (![X0 : $i]:
% 1.81/2.03         (((k2_zfmisc_1 @ sk_B_1 @ X0) = (k1_xboole_0))
% 1.81/2.03          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.81/2.03      inference('clc', [status(thm)], ['90', '95'])).
% 1.81/2.03  thf('97', plain,
% 1.81/2.03      (![X37 : $i]:
% 1.81/2.03         (m1_subset_1 @ (k6_relat_1 @ X37) @ 
% 1.81/2.03          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 1.81/2.03      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.81/2.03  thf('98', plain,
% 1.81/2.03      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.81/2.03         (~ (r2_hidden @ X13 @ X14)
% 1.81/2.03          | ~ (v1_xboole_0 @ X15)
% 1.81/2.03          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 1.81/2.03      inference('cnf', [status(esa)], [t5_subset])).
% 1.81/2.03  thf('99', plain,
% 1.81/2.03      (![X0 : $i, X1 : $i]:
% 1.81/2.03         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0))
% 1.81/2.03          | ~ (r2_hidden @ X1 @ (k6_relat_1 @ X0)))),
% 1.81/2.03      inference('sup-', [status(thm)], ['97', '98'])).
% 1.81/2.03  thf('100', plain,
% 1.81/2.03      (![X0 : $i]:
% 1.81/2.03         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.81/2.03          | ((sk_A) = (k1_relat_1 @ sk_D))
% 1.81/2.03          | ~ (r2_hidden @ X0 @ (k6_relat_1 @ sk_B_1)))),
% 1.81/2.03      inference('sup-', [status(thm)], ['96', '99'])).
% 1.81/2.03  thf('101', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.81/2.03      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.81/2.03  thf('102', plain,
% 1.81/2.03      (![X0 : $i]:
% 1.81/2.03         (((sk_A) = (k1_relat_1 @ sk_D))
% 1.81/2.03          | ~ (r2_hidden @ X0 @ (k6_relat_1 @ sk_B_1)))),
% 1.81/2.03      inference('demod', [status(thm)], ['100', '101'])).
% 1.81/2.03  thf('103', plain,
% 1.81/2.03      (![X0 : $i]:
% 1.81/2.03         ((r1_tarski @ (k6_relat_1 @ sk_B_1) @ X0)
% 1.81/2.03          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.81/2.03      inference('sup-', [status(thm)], ['49', '102'])).
% 1.81/2.03  thf('104', plain,
% 1.81/2.03      (![X10 : $i, X12 : $i]:
% 1.81/2.03         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 1.81/2.03      inference('cnf', [status(esa)], [t3_subset])).
% 1.81/2.03  thf('105', plain,
% 1.81/2.03      (![X0 : $i]:
% 1.81/2.03         (((sk_A) = (k1_relat_1 @ sk_D))
% 1.81/2.03          | (m1_subset_1 @ (k6_relat_1 @ sk_B_1) @ (k1_zfmisc_1 @ X0)))),
% 1.81/2.03      inference('sup-', [status(thm)], ['103', '104'])).
% 1.81/2.03  thf('106', plain,
% 1.81/2.03      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.81/2.03         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 1.81/2.03          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.81/2.03      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.81/2.03  thf('107', plain,
% 1.81/2.03      (![X0 : $i, X1 : $i]:
% 1.81/2.03         (((sk_A) = (k1_relat_1 @ sk_D))
% 1.81/2.03          | ((k1_relset_1 @ X1 @ X0 @ (k6_relat_1 @ sk_B_1))
% 1.81/2.03              = (k1_relat_1 @ (k6_relat_1 @ sk_B_1))))),
% 1.81/2.03      inference('sup-', [status(thm)], ['105', '106'])).
% 1.81/2.03  thf('108', plain, (![X23 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X23)) = (X23))),
% 1.81/2.03      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.81/2.03  thf('109', plain,
% 1.81/2.03      (![X0 : $i, X1 : $i]:
% 1.81/2.03         (((sk_A) = (k1_relat_1 @ sk_D))
% 1.81/2.03          | ((k1_relset_1 @ X1 @ X0 @ (k6_relat_1 @ sk_B_1)) = (sk_B_1)))),
% 1.81/2.03      inference('demod', [status(thm)], ['107', '108'])).
% 1.81/2.03  thf('110', plain,
% 1.81/2.03      (![X0 : $i, X1 : $i]:
% 1.81/2.03         (((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (sk_B_1))
% 1.81/2.03          | ~ (v1_xboole_0 @ sk_B_1)
% 1.81/2.03          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.81/2.03      inference('sup+', [status(thm)], ['48', '109'])).
% 1.81/2.03  thf('111', plain,
% 1.81/2.03      (![X0 : $i, X1 : $i]:
% 1.81/2.03         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.81/2.03      inference('demod', [status(thm)], ['26', '29'])).
% 1.81/2.03  thf('112', plain,
% 1.81/2.03      ((((k1_xboole_0) = (sk_B_1))
% 1.81/2.03        | ~ (v1_xboole_0 @ sk_B_1)
% 1.81/2.03        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.81/2.03      inference('demod', [status(thm)], ['110', '111'])).
% 1.81/2.03  thf('113', plain, ((((sk_B_1) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.81/2.03  thf('114', plain,
% 1.81/2.03      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.81/2.03      inference('split', [status(esa)], ['113'])).
% 1.81/2.03  thf('115', plain, ((v1_funct_1 @ sk_D)),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.81/2.03  thf('116', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 1.81/2.03      inference('split', [status(esa)], ['43'])).
% 1.81/2.03  thf('117', plain, (((v1_funct_1 @ sk_D))),
% 1.81/2.03      inference('sup-', [status(thm)], ['115', '116'])).
% 1.81/2.03  thf('118', plain,
% 1.81/2.03      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.81/2.03      inference('demod', [status(thm)], ['33', '39'])).
% 1.81/2.03  thf('119', plain,
% 1.81/2.03      (![X38 : $i]:
% 1.81/2.03         (((X38) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X38) @ X38))),
% 1.81/2.03      inference('cnf', [status(esa)], [t34_mcart_1])).
% 1.81/2.03  thf('120', plain,
% 1.81/2.03      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.81/2.03      inference('split', [status(esa)], ['113'])).
% 1.81/2.03  thf('121', plain,
% 1.81/2.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.81/2.03  thf('122', plain,
% 1.81/2.03      (((m1_subset_1 @ sk_D @ 
% 1.81/2.03         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 1.81/2.03         <= ((((sk_A) = (k1_xboole_0))))),
% 1.81/2.03      inference('sup+', [status(thm)], ['120', '121'])).
% 1.81/2.03  thf('123', plain,
% 1.81/2.03      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.81/2.03         (~ (r2_hidden @ X13 @ X14)
% 1.81/2.03          | ~ (v1_xboole_0 @ X15)
% 1.81/2.03          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 1.81/2.03      inference('cnf', [status(esa)], [t5_subset])).
% 1.81/2.03  thf('124', plain,
% 1.81/2.03      ((![X0 : $i]:
% 1.81/2.03          (~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 1.81/2.03           | ~ (r2_hidden @ X0 @ sk_D)))
% 1.81/2.03         <= ((((sk_A) = (k1_xboole_0))))),
% 1.81/2.03      inference('sup-', [status(thm)], ['122', '123'])).
% 1.81/2.03  thf('125', plain,
% 1.81/2.03      (![X8 : $i, X9 : $i]:
% 1.81/2.03         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 1.81/2.03      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.81/2.03  thf('126', plain,
% 1.81/2.03      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 1.81/2.03      inference('simplify', [status(thm)], ['125'])).
% 1.81/2.03  thf('127', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.81/2.03      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.81/2.03  thf('128', plain,
% 1.81/2.03      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 1.81/2.03      inference('demod', [status(thm)], ['124', '126', '127'])).
% 1.81/2.03  thf('129', plain,
% 1.81/2.03      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.81/2.03      inference('sup-', [status(thm)], ['119', '128'])).
% 1.81/2.03  thf('130', plain,
% 1.81/2.03      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.81/2.03      inference('split', [status(esa)], ['113'])).
% 1.81/2.03  thf('131', plain,
% 1.81/2.03      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 1.81/2.03         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 1.81/2.03      inference('split', [status(esa)], ['43'])).
% 1.81/2.03  thf('132', plain,
% 1.81/2.03      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C_1))
% 1.81/2.03         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 1.81/2.03             (((sk_A) = (k1_xboole_0))))),
% 1.81/2.03      inference('sup-', [status(thm)], ['130', '131'])).
% 1.81/2.03  thf('133', plain,
% 1.81/2.03      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_C_1))
% 1.81/2.03         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) & 
% 1.81/2.03             (((sk_A) = (k1_xboole_0))))),
% 1.81/2.03      inference('sup-', [status(thm)], ['129', '132'])).
% 1.81/2.03  thf('134', plain,
% 1.81/2.03      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ (((sk_A) = (k1_xboole_0)))),
% 1.81/2.03      inference('sup-', [status(thm)], ['118', '133'])).
% 1.81/2.03  thf('135', plain,
% 1.81/2.03      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 1.81/2.03      inference('simplify', [status(thm)], ['125'])).
% 1.81/2.03  thf('136', plain,
% 1.81/2.03      (((m1_subset_1 @ sk_D @ 
% 1.81/2.03         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 1.81/2.03         <= ((((sk_A) = (k1_xboole_0))))),
% 1.81/2.03      inference('sup+', [status(thm)], ['120', '121'])).
% 1.81/2.03  thf('137', plain,
% 1.81/2.03      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.81/2.03         <= ((((sk_A) = (k1_xboole_0))))),
% 1.81/2.03      inference('sup+', [status(thm)], ['135', '136'])).
% 1.81/2.03  thf('138', plain,
% 1.81/2.03      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 1.81/2.03      inference('simplify', [status(thm)], ['125'])).
% 1.81/2.03  thf('139', plain,
% 1.81/2.03      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 1.81/2.03      inference('split', [status(esa)], ['113'])).
% 1.81/2.03  thf('140', plain,
% 1.81/2.03      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 1.81/2.03         <= (~
% 1.81/2.03             ((m1_subset_1 @ sk_D @ 
% 1.81/2.03               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 1.81/2.03      inference('split', [status(esa)], ['43'])).
% 1.81/2.03  thf('141', plain,
% 1.81/2.03      ((~ (m1_subset_1 @ sk_D @ 
% 1.81/2.03           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C_1))))
% 1.81/2.03         <= (~
% 1.81/2.03             ((m1_subset_1 @ sk_D @ 
% 1.81/2.03               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 1.81/2.03             (((sk_A) = (k1_xboole_0))))),
% 1.81/2.03      inference('sup-', [status(thm)], ['139', '140'])).
% 1.81/2.03  thf('142', plain,
% 1.81/2.03      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 1.81/2.03         <= (~
% 1.81/2.03             ((m1_subset_1 @ sk_D @ 
% 1.81/2.03               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) & 
% 1.81/2.03             (((sk_A) = (k1_xboole_0))))),
% 1.81/2.03      inference('sup-', [status(thm)], ['138', '141'])).
% 1.81/2.03  thf('143', plain,
% 1.81/2.03      (~ (((sk_A) = (k1_xboole_0))) | 
% 1.81/2.03       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 1.81/2.03      inference('sup-', [status(thm)], ['137', '142'])).
% 1.81/2.03  thf('144', plain,
% 1.81/2.03      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 1.81/2.03       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | ~ ((v1_funct_1 @ sk_D))),
% 1.81/2.03      inference('split', [status(esa)], ['43'])).
% 1.81/2.03  thf('145', plain,
% 1.81/2.03      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 1.81/2.03      inference('split', [status(esa)], ['113'])).
% 1.81/2.03  thf('146', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 1.81/2.03      inference('sat_resolution*', [status(thm)],
% 1.81/2.03                ['117', '134', '143', '144', '145'])).
% 1.81/2.03  thf('147', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.81/2.03      inference('simpl_trail', [status(thm)], ['114', '146'])).
% 1.81/2.03  thf('148', plain,
% 1.81/2.03      ((~ (v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.81/2.03      inference('simplify_reflect-', [status(thm)], ['112', '147'])).
% 1.81/2.03  thf('149', plain,
% 1.81/2.03      (![X43 : $i, X44 : $i]:
% 1.81/2.03         ((zip_tseitin_0 @ X43 @ X44) | ((X43) = (k1_xboole_0)))),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.81/2.03  thf('150', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.81/2.03      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.81/2.03  thf('151', plain,
% 1.81/2.03      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.81/2.03      inference('sup+', [status(thm)], ['149', '150'])).
% 1.81/2.03  thf('152', plain,
% 1.81/2.03      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.81/2.03        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.81/2.03      inference('sup-', [status(thm)], ['61', '62'])).
% 1.81/2.03  thf('153', plain,
% 1.81/2.03      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 1.81/2.03      inference('sup-', [status(thm)], ['151', '152'])).
% 1.81/2.03  thf('154', plain,
% 1.81/2.03      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.81/2.03        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.81/2.03      inference('demod', [status(thm)], ['67', '70'])).
% 1.81/2.03  thf('155', plain,
% 1.81/2.03      (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.81/2.03      inference('sup-', [status(thm)], ['153', '154'])).
% 1.81/2.03  thf('156', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.81/2.03      inference('clc', [status(thm)], ['148', '155'])).
% 1.81/2.03  thf('157', plain,
% 1.81/2.03      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.81/2.03      inference('sup+', [status(thm)], ['74', '75'])).
% 1.81/2.03  thf('158', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.81/2.03      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.81/2.03  thf('159', plain,
% 1.81/2.03      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.81/2.03      inference('sup+', [status(thm)], ['157', '158'])).
% 1.81/2.03  thf('160', plain, (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_D))),
% 1.81/2.03      inference('sup+', [status(thm)], ['156', '159'])).
% 1.81/2.03  thf('161', plain,
% 1.81/2.03      ((~ (v1_xboole_0 @ sk_D)) <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 1.81/2.03      inference('clc', [status(thm)], ['45', '160'])).
% 1.81/2.03  thf('162', plain,
% 1.81/2.03      ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) @ sk_C_1)),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.81/2.03  thf('163', plain,
% 1.81/2.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.81/2.03  thf(redefinition_k2_relset_1, axiom,
% 1.81/2.03    (![A:$i,B:$i,C:$i]:
% 1.81/2.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.81/2.03       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.81/2.03  thf('164', plain,
% 1.81/2.03      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.81/2.03         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 1.81/2.03          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 1.81/2.03      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.81/2.03  thf('165', plain,
% 1.81/2.03      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.81/2.03      inference('sup-', [status(thm)], ['163', '164'])).
% 1.81/2.03  thf('166', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C_1)),
% 1.81/2.03      inference('demod', [status(thm)], ['162', '165'])).
% 1.81/2.03  thf('167', plain,
% 1.81/2.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.81/2.03  thf('168', plain,
% 1.81/2.03      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.81/2.03         ((v4_relat_1 @ X25 @ X26)
% 1.81/2.03          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.81/2.03      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.81/2.03  thf('169', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 1.81/2.03      inference('sup-', [status(thm)], ['167', '168'])).
% 1.81/2.03  thf('170', plain,
% 1.81/2.03      (![X18 : $i, X19 : $i]:
% 1.81/2.03         (~ (v4_relat_1 @ X18 @ X19)
% 1.81/2.03          | (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 1.81/2.03          | ~ (v1_relat_1 @ X18))),
% 1.81/2.03      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.81/2.03  thf('171', plain,
% 1.81/2.03      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A))),
% 1.81/2.03      inference('sup-', [status(thm)], ['169', '170'])).
% 1.81/2.03  thf('172', plain,
% 1.81/2.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.81/2.03  thf(cc2_relat_1, axiom,
% 1.81/2.03    (![A:$i]:
% 1.81/2.03     ( ( v1_relat_1 @ A ) =>
% 1.81/2.03       ( ![B:$i]:
% 1.81/2.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.81/2.03  thf('173', plain,
% 1.81/2.03      (![X16 : $i, X17 : $i]:
% 1.81/2.03         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 1.81/2.03          | (v1_relat_1 @ X16)
% 1.81/2.03          | ~ (v1_relat_1 @ X17))),
% 1.81/2.03      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.81/2.03  thf('174', plain,
% 1.81/2.03      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D))),
% 1.81/2.03      inference('sup-', [status(thm)], ['172', '173'])).
% 1.81/2.03  thf('175', plain,
% 1.81/2.03      (![X20 : $i, X21 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X20 @ X21))),
% 1.81/2.03      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.81/2.03  thf('176', plain, ((v1_relat_1 @ sk_D)),
% 1.81/2.03      inference('demod', [status(thm)], ['174', '175'])).
% 1.81/2.03  thf('177', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A)),
% 1.81/2.03      inference('demod', [status(thm)], ['171', '176'])).
% 1.81/2.03  thf(t11_relset_1, axiom,
% 1.81/2.03    (![A:$i,B:$i,C:$i]:
% 1.81/2.03     ( ( v1_relat_1 @ C ) =>
% 1.81/2.03       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 1.81/2.03           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 1.81/2.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.81/2.03  thf('178', plain,
% 1.81/2.03      (![X34 : $i, X35 : $i, X36 : $i]:
% 1.81/2.03         (~ (r1_tarski @ (k1_relat_1 @ X34) @ X35)
% 1.81/2.03          | ~ (r1_tarski @ (k2_relat_1 @ X34) @ X36)
% 1.81/2.03          | (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.81/2.03          | ~ (v1_relat_1 @ X34))),
% 1.81/2.03      inference('cnf', [status(esa)], [t11_relset_1])).
% 1.81/2.03  thf('179', plain,
% 1.81/2.03      (![X0 : $i]:
% 1.81/2.03         (~ (v1_relat_1 @ sk_D)
% 1.81/2.03          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.81/2.03          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 1.81/2.03      inference('sup-', [status(thm)], ['177', '178'])).
% 1.81/2.03  thf('180', plain, ((v1_relat_1 @ sk_D)),
% 1.81/2.03      inference('demod', [status(thm)], ['174', '175'])).
% 1.81/2.03  thf('181', plain,
% 1.81/2.03      (![X0 : $i]:
% 1.81/2.03         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.81/2.03          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 1.81/2.03      inference('demod', [status(thm)], ['179', '180'])).
% 1.81/2.03  thf('182', plain,
% 1.81/2.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 1.81/2.03      inference('sup-', [status(thm)], ['166', '181'])).
% 1.81/2.03  thf('183', plain,
% 1.81/2.03      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))
% 1.81/2.03         <= (~
% 1.81/2.03             ((m1_subset_1 @ sk_D @ 
% 1.81/2.03               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))))),
% 1.81/2.03      inference('split', [status(esa)], ['43'])).
% 1.81/2.03  thf('184', plain,
% 1.81/2.03      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1))))),
% 1.81/2.03      inference('sup-', [status(thm)], ['182', '183'])).
% 1.81/2.03  thf('185', plain,
% 1.81/2.03      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)) | 
% 1.81/2.03       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))) | 
% 1.81/2.03       ~ ((v1_funct_1 @ sk_D))),
% 1.81/2.03      inference('split', [status(esa)], ['43'])).
% 1.81/2.03  thf('186', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 1.81/2.03      inference('sat_resolution*', [status(thm)], ['117', '184', '185'])).
% 1.81/2.03  thf('187', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.81/2.03      inference('simpl_trail', [status(thm)], ['161', '186'])).
% 1.81/2.03  thf('188', plain,
% 1.81/2.03      (![X43 : $i, X44 : $i]:
% 1.81/2.03         ((zip_tseitin_0 @ X43 @ X44) | ((X43) = (k1_xboole_0)))),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.81/2.03  thf('189', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.81/2.03      inference('sup-', [status(thm)], ['9', '21'])).
% 1.81/2.03  thf('190', plain,
% 1.81/2.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.81/2.03         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 1.81/2.03      inference('sup+', [status(thm)], ['188', '189'])).
% 1.81/2.03  thf('191', plain,
% 1.81/2.03      ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) @ sk_C_1)),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.81/2.03  thf('192', plain,
% 1.81/2.03      (![X4 : $i, X6 : $i]:
% 1.81/2.03         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.81/2.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.81/2.03  thf('193', plain,
% 1.81/2.03      ((~ (r1_tarski @ sk_C_1 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D))
% 1.81/2.03        | ((sk_C_1) = (k2_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 1.81/2.03      inference('sup-', [status(thm)], ['191', '192'])).
% 1.81/2.03  thf('194', plain,
% 1.81/2.03      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.81/2.03      inference('sup-', [status(thm)], ['163', '164'])).
% 1.81/2.03  thf('195', plain,
% 1.81/2.03      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.81/2.03      inference('sup-', [status(thm)], ['163', '164'])).
% 1.81/2.03  thf('196', plain,
% 1.81/2.03      ((~ (r1_tarski @ sk_C_1 @ (k2_relat_1 @ sk_D))
% 1.81/2.03        | ((sk_C_1) = (k2_relat_1 @ sk_D)))),
% 1.81/2.03      inference('demod', [status(thm)], ['193', '194', '195'])).
% 1.81/2.03  thf('197', plain,
% 1.81/2.03      (![X0 : $i]:
% 1.81/2.03         ((zip_tseitin_0 @ sk_C_1 @ X0) | ((sk_C_1) = (k2_relat_1 @ sk_D)))),
% 1.81/2.03      inference('sup-', [status(thm)], ['190', '196'])).
% 1.81/2.03  thf('198', plain,
% 1.81/2.03      (![X22 : $i]:
% 1.81/2.03         (((k2_relat_1 @ X22) != (k1_xboole_0))
% 1.81/2.03          | ((X22) = (k1_xboole_0))
% 1.81/2.03          | ~ (v1_relat_1 @ X22))),
% 1.81/2.03      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.81/2.03  thf('199', plain,
% 1.81/2.03      (![X0 : $i]:
% 1.81/2.03         (((sk_C_1) != (k1_xboole_0))
% 1.81/2.03          | (zip_tseitin_0 @ sk_C_1 @ X0)
% 1.81/2.03          | ~ (v1_relat_1 @ sk_D)
% 1.81/2.03          | ((sk_D) = (k1_xboole_0)))),
% 1.81/2.03      inference('sup-', [status(thm)], ['197', '198'])).
% 1.81/2.03  thf('200', plain, ((v1_relat_1 @ sk_D)),
% 1.81/2.03      inference('demod', [status(thm)], ['174', '175'])).
% 1.81/2.03  thf('201', plain,
% 1.81/2.03      (![X0 : $i]:
% 1.81/2.03         (((sk_C_1) != (k1_xboole_0))
% 1.81/2.03          | (zip_tseitin_0 @ sk_C_1 @ X0)
% 1.81/2.03          | ((sk_D) = (k1_xboole_0)))),
% 1.81/2.03      inference('demod', [status(thm)], ['199', '200'])).
% 1.81/2.03  thf('202', plain,
% 1.81/2.03      (![X43 : $i, X44 : $i]:
% 1.81/2.03         ((zip_tseitin_0 @ X43 @ X44) | ((X43) = (k1_xboole_0)))),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.81/2.03  thf('203', plain,
% 1.81/2.03      (![X0 : $i]: (((sk_D) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_C_1 @ X0))),
% 1.81/2.03      inference('clc', [status(thm)], ['201', '202'])).
% 1.81/2.03  thf('204', plain,
% 1.81/2.03      (![X0 : $i, X1 : $i]:
% 1.81/2.03         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 1.81/2.03      inference('sup-', [status(thm)], ['36', '37'])).
% 1.81/2.03  thf('205', plain,
% 1.81/2.03      (![X0 : $i]:
% 1.81/2.03         (((sk_D) = (k1_xboole_0))
% 1.81/2.03          | (zip_tseitin_1 @ k1_xboole_0 @ sk_C_1 @ X0))),
% 1.81/2.03      inference('sup-', [status(thm)], ['203', '204'])).
% 1.81/2.03  thf('206', plain,
% 1.81/2.03      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.81/2.03      inference('sup-', [status(thm)], ['0', '6'])).
% 1.81/2.03  thf('207', plain,
% 1.81/2.03      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.81/2.03         (((X48) != (k1_xboole_0))
% 1.81/2.03          | ((X49) = (k1_xboole_0))
% 1.81/2.03          | (v1_funct_2 @ X50 @ X49 @ X48)
% 1.81/2.03          | ((X50) != (k1_xboole_0))
% 1.81/2.03          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48))))),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.81/2.03  thf('208', plain,
% 1.81/2.03      (![X49 : $i]:
% 1.81/2.03         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 1.81/2.03             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ k1_xboole_0)))
% 1.81/2.03          | (v1_funct_2 @ k1_xboole_0 @ X49 @ k1_xboole_0)
% 1.81/2.03          | ((X49) = (k1_xboole_0)))),
% 1.81/2.03      inference('simplify', [status(thm)], ['207'])).
% 1.81/2.03  thf('209', plain,
% 1.81/2.03      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 1.81/2.03      inference('simplify', [status(thm)], ['10'])).
% 1.81/2.03  thf('210', plain,
% 1.81/2.03      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.81/2.03      inference('sup-', [status(thm)], ['22', '23'])).
% 1.81/2.03  thf('211', plain,
% 1.81/2.03      (![X49 : $i]:
% 1.81/2.03         ((v1_funct_2 @ k1_xboole_0 @ X49 @ k1_xboole_0)
% 1.81/2.03          | ((X49) = (k1_xboole_0)))),
% 1.81/2.03      inference('demod', [status(thm)], ['208', '209', '210'])).
% 1.81/2.03  thf('212', plain,
% 1.81/2.03      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.81/2.03         (~ (v1_funct_2 @ X47 @ X45 @ X46)
% 1.81/2.03          | ((X45) = (k1_relset_1 @ X45 @ X46 @ X47))
% 1.81/2.03          | ~ (zip_tseitin_1 @ X47 @ X46 @ X45))),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.03  thf('213', plain,
% 1.81/2.03      (![X0 : $i]:
% 1.81/2.03         (((X0) = (k1_xboole_0))
% 1.81/2.03          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.81/2.03          | ((X0) = (k1_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)))),
% 1.81/2.03      inference('sup-', [status(thm)], ['211', '212'])).
% 1.81/2.03  thf('214', plain,
% 1.81/2.03      (![X0 : $i, X1 : $i]:
% 1.81/2.03         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.81/2.03      inference('demod', [status(thm)], ['26', '29'])).
% 1.81/2.03  thf('215', plain,
% 1.81/2.03      (![X0 : $i]:
% 1.81/2.03         (((X0) = (k1_xboole_0))
% 1.81/2.03          | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.81/2.03          | ((X0) = (k1_xboole_0)))),
% 1.81/2.03      inference('demod', [status(thm)], ['213', '214'])).
% 1.81/2.03  thf('216', plain,
% 1.81/2.03      (![X0 : $i]:
% 1.81/2.03         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 1.81/2.03          | ((X0) = (k1_xboole_0)))),
% 1.81/2.03      inference('simplify', [status(thm)], ['215'])).
% 1.81/2.03  thf('217', plain,
% 1.81/2.03      (![X0 : $i, X1 : $i]:
% 1.81/2.03         (~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 1.81/2.03          | ~ (v1_xboole_0 @ X0)
% 1.81/2.03          | ((X1) = (k1_xboole_0)))),
% 1.81/2.03      inference('sup-', [status(thm)], ['206', '216'])).
% 1.81/2.03  thf('218', plain,
% 1.81/2.03      (![X0 : $i]:
% 1.81/2.03         (((sk_D) = (k1_xboole_0))
% 1.81/2.03          | ((X0) = (k1_xboole_0))
% 1.81/2.03          | ~ (v1_xboole_0 @ sk_C_1))),
% 1.81/2.03      inference('sup-', [status(thm)], ['205', '217'])).
% 1.81/2.03  thf('219', plain, ((((sk_D) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_C_1))),
% 1.81/2.03      inference('condensation', [status(thm)], ['218'])).
% 1.81/2.03  thf('220', plain,
% 1.81/2.03      (![X43 : $i, X44 : $i]:
% 1.81/2.03         ((zip_tseitin_0 @ X43 @ X44) | ((X43) = (k1_xboole_0)))),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.81/2.03  thf('221', plain,
% 1.81/2.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 1.81/2.03      inference('sup-', [status(thm)], ['166', '181'])).
% 1.81/2.03  thf('222', plain,
% 1.81/2.03      (![X48 : $i, X49 : $i, X50 : $i]:
% 1.81/2.03         (~ (zip_tseitin_0 @ X48 @ X49)
% 1.81/2.03          | (zip_tseitin_1 @ X50 @ X48 @ X49)
% 1.81/2.03          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X48))))),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.81/2.03  thf('223', plain,
% 1.81/2.03      (((zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 1.81/2.03        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_A))),
% 1.81/2.03      inference('sup-', [status(thm)], ['221', '222'])).
% 1.81/2.03  thf('224', plain,
% 1.81/2.03      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C_1)))),
% 1.81/2.03      inference('sup-', [status(thm)], ['166', '181'])).
% 1.81/2.03  thf('225', plain,
% 1.81/2.03      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.81/2.03         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 1.81/2.03          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.81/2.03      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.81/2.03  thf('226', plain,
% 1.81/2.03      (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.81/2.03      inference('sup-', [status(thm)], ['224', '225'])).
% 1.81/2.03  thf('227', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.81/2.03      inference('clc', [status(thm)], ['148', '155'])).
% 1.81/2.03  thf('228', plain, (((k1_relset_1 @ sk_A @ sk_C_1 @ sk_D) = (sk_A))),
% 1.81/2.03      inference('demod', [status(thm)], ['226', '227'])).
% 1.81/2.03  thf('229', plain,
% 1.81/2.03      (![X45 : $i, X46 : $i, X47 : $i]:
% 1.81/2.03         (((X45) != (k1_relset_1 @ X45 @ X46 @ X47))
% 1.81/2.03          | (v1_funct_2 @ X47 @ X45 @ X46)
% 1.81/2.03          | ~ (zip_tseitin_1 @ X47 @ X46 @ X45))),
% 1.81/2.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.81/2.03  thf('230', plain,
% 1.81/2.03      ((((sk_A) != (sk_A))
% 1.81/2.03        | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)
% 1.81/2.03        | (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 1.81/2.03      inference('sup-', [status(thm)], ['228', '229'])).
% 1.81/2.03  thf('231', plain,
% 1.81/2.03      (((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)
% 1.81/2.03        | ~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A))),
% 1.81/2.03      inference('simplify', [status(thm)], ['230'])).
% 1.81/2.03  thf('232', plain,
% 1.81/2.03      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1))
% 1.81/2.03         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1)))),
% 1.81/2.03      inference('split', [status(esa)], ['43'])).
% 1.81/2.03  thf('233', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C_1))),
% 1.81/2.03      inference('sat_resolution*', [status(thm)], ['117', '184', '185'])).
% 1.81/2.03  thf('234', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C_1)),
% 1.81/2.03      inference('simpl_trail', [status(thm)], ['232', '233'])).
% 1.81/2.03  thf('235', plain, (~ (zip_tseitin_1 @ sk_D @ sk_C_1 @ sk_A)),
% 1.81/2.03      inference('clc', [status(thm)], ['231', '234'])).
% 1.81/2.03  thf('236', plain, (~ (zip_tseitin_0 @ sk_C_1 @ sk_A)),
% 1.81/2.03      inference('clc', [status(thm)], ['223', '235'])).
% 1.81/2.03  thf('237', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.81/2.03      inference('sup-', [status(thm)], ['220', '236'])).
% 1.81/2.03  thf('238', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.81/2.03      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.81/2.03  thf('239', plain, (((sk_D) = (k1_xboole_0))),
% 1.81/2.03      inference('demod', [status(thm)], ['219', '237', '238'])).
% 1.81/2.03  thf('240', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.81/2.03      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.81/2.03  thf('241', plain, ($false),
% 1.81/2.03      inference('demod', [status(thm)], ['187', '239', '240'])).
% 1.81/2.03  
% 1.81/2.03  % SZS output end Refutation
% 1.81/2.03  
% 1.81/2.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
