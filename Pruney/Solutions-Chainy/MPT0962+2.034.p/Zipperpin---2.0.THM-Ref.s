%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SE4mXlzeYj

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:53 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 866 expanded)
%              Number of leaves         :   38 ( 250 expanded)
%              Depth                    :   15
%              Number of atoms          :  732 (10084 expanded)
%              Number of equality atoms :   52 ( 265 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
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

thf('8',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X27 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X26: $i] :
      ( zip_tseitin_0 @ X26 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf(t4_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
         => ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_funct_2])).

thf('11',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('12',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('13',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X25 )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

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

thf('18',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('19',plain,
    ( ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28
       != ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
     != ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('27',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('29',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
   <= ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['26'])).

thf('30',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('32',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['26'])).

thf('33',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['26'])).

thf('35',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['30','33','34'])).

thf('36',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['27','35'])).

thf('37',plain,(
    ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['25','36'])).

thf('38',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['19','37'])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('41',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    r1_tarski @ sk_B_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('44',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) @ sk_B_1 )
    | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['19','37'])).

thf('47',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('48',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('49',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('51',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('52',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k6_subset_1 @ X12 @ X13 )
      = ( k4_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('53',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k6_subset_1 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('55',plain,(
    ! [X10: $i,X11: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('60',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('61',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference(demod,[status(thm)],['44','47','49','58','59','60'])).

thf('62',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['39','61'])).

thf('63',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X31 != k1_xboole_0 )
      | ( X32 = k1_xboole_0 )
      | ( v1_funct_2 @ X33 @ X32 @ X31 )
      | ( X33 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('64',plain,(
    ! [X32: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ k1_xboole_0 ) ) )
      | ( v1_funct_2 @ k1_xboole_0 @ X32 @ k1_xboole_0 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('66',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('67',plain,(
    ! [X32: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X32 @ k1_xboole_0 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['27','35'])).

thf('69',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('70',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference(demod,[status(thm)],['44','47','49','58','59','60'])).

thf('72',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference(demod,[status(thm)],['44','47','49','58','59','60'])).

thf('73',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['67','73'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('75',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['62','74','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SE4mXlzeYj
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:43:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.76/0.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.99  % Solved by: fo/fo7.sh
% 0.76/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.99  % done 1014 iterations in 0.524s
% 0.76/0.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.99  % SZS output start Refutation
% 0.76/0.99  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.76/0.99  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.76/0.99  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.76/0.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.99  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.76/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.99  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.76/0.99  thf(sk_B_type, type, sk_B: $i > $i).
% 0.76/0.99  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.76/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.99  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.76/0.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.99  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.99  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.76/0.99  thf(t7_xboole_0, axiom,
% 0.76/0.99    (![A:$i]:
% 0.76/0.99     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.76/0.99          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.76/0.99  thf('0', plain,
% 0.76/0.99      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.76/0.99      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.76/0.99  thf(d10_xboole_0, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.76/0.99  thf('1', plain,
% 0.76/0.99      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.76/0.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/0.99  thf('2', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.76/0.99      inference('simplify', [status(thm)], ['1'])).
% 0.76/0.99  thf(t3_subset, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.99  thf('3', plain,
% 0.76/0.99      (![X14 : $i, X16 : $i]:
% 0.76/0.99         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.76/0.99      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.99  thf('4', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.76/0.99      inference('sup-', [status(thm)], ['2', '3'])).
% 0.76/0.99  thf(t5_subset, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.76/0.99          ( v1_xboole_0 @ C ) ) ))).
% 0.76/0.99  thf('5', plain,
% 0.76/0.99      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.76/0.99         (~ (r2_hidden @ X17 @ X18)
% 0.76/0.99          | ~ (v1_xboole_0 @ X19)
% 0.76/0.99          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.76/0.99      inference('cnf', [status(esa)], [t5_subset])).
% 0.76/0.99  thf('6', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.76/0.99      inference('sup-', [status(thm)], ['4', '5'])).
% 0.76/0.99  thf('7', plain,
% 0.76/0.99      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.99      inference('sup-', [status(thm)], ['0', '6'])).
% 0.76/0.99  thf(d1_funct_2, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.99       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.76/0.99           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.76/0.99             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.76/0.99         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/0.99           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.76/0.99             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.76/0.99  thf(zf_stmt_0, axiom,
% 0.76/0.99    (![B:$i,A:$i]:
% 0.76/0.99     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/0.99       ( zip_tseitin_0 @ B @ A ) ))).
% 0.76/0.99  thf('8', plain,
% 0.76/0.99      (![X26 : $i, X27 : $i]:
% 0.76/0.99         ((zip_tseitin_0 @ X26 @ X27) | ((X27) != (k1_xboole_0)))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('9', plain, (![X26 : $i]: (zip_tseitin_0 @ X26 @ k1_xboole_0)),
% 0.76/0.99      inference('simplify', [status(thm)], ['8'])).
% 0.76/0.99  thf('10', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.99      inference('sup+', [status(thm)], ['7', '9'])).
% 0.76/0.99  thf(t4_funct_2, conjecture,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.76/0.99       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.76/0.99         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.76/0.99           ( m1_subset_1 @
% 0.76/0.99             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.76/0.99  thf(zf_stmt_1, negated_conjecture,
% 0.76/0.99    (~( ![A:$i,B:$i]:
% 0.76/0.99        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.76/0.99          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.76/0.99            ( ( v1_funct_1 @ B ) & 
% 0.76/0.99              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.76/0.99              ( m1_subset_1 @
% 0.76/0.99                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 0.76/0.99    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 0.76/0.99  thf('11', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.76/0.99  thf('12', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.76/0.99      inference('simplify', [status(thm)], ['1'])).
% 0.76/0.99  thf(t11_relset_1, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( v1_relat_1 @ C ) =>
% 0.76/0.99       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.76/0.99           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.76/0.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.76/0.99  thf('13', plain,
% 0.76/0.99      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.76/0.99         (~ (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 0.76/0.99          | ~ (r1_tarski @ (k2_relat_1 @ X23) @ X25)
% 0.76/0.99          | (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.76/0.99          | ~ (v1_relat_1 @ X23))),
% 0.76/0.99      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.76/0.99  thf('14', plain,
% 0.76/0.99      (![X0 : $i, X1 : $i]:
% 0.76/0.99         (~ (v1_relat_1 @ X0)
% 0.76/0.99          | (m1_subset_1 @ X0 @ 
% 0.76/0.99             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.76/0.99          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.76/0.99      inference('sup-', [status(thm)], ['12', '13'])).
% 0.76/0.99  thf('15', plain,
% 0.76/0.99      (((m1_subset_1 @ sk_B_1 @ 
% 0.76/0.99         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))
% 0.76/0.99        | ~ (v1_relat_1 @ sk_B_1))),
% 0.76/0.99      inference('sup-', [status(thm)], ['11', '14'])).
% 0.76/0.99  thf('16', plain, ((v1_relat_1 @ sk_B_1)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.76/0.99  thf('17', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_B_1 @ 
% 0.76/0.99        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.76/0.99      inference('demod', [status(thm)], ['15', '16'])).
% 0.76/0.99  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.76/0.99  thf(zf_stmt_3, axiom,
% 0.76/0.99    (![C:$i,B:$i,A:$i]:
% 0.76/0.99     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.76/0.99       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.76/0.99  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.76/0.99  thf(zf_stmt_5, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.99       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.76/0.99         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.76/0.99           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.76/0.99             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.76/0.99  thf('18', plain,
% 0.76/0.99      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.76/0.99         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.76/0.99          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.76/0.99          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.76/0.99  thf('19', plain,
% 0.76/0.99      (((zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 0.76/0.99        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['17', '18'])).
% 0.76/0.99  thf('20', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_B_1 @ 
% 0.76/0.99        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.76/0.99      inference('demod', [status(thm)], ['15', '16'])).
% 0.76/0.99  thf(redefinition_k1_relset_1, axiom,
% 0.76/0.99    (![A:$i,B:$i,C:$i]:
% 0.76/0.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.99       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.76/0.99  thf('21', plain,
% 0.76/0.99      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.76/0.99         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.76/0.99          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.76/0.99      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.76/0.99  thf('22', plain,
% 0.76/0.99      (((k1_relset_1 @ (k1_relat_1 @ sk_B_1) @ sk_A @ sk_B_1)
% 0.76/0.99         = (k1_relat_1 @ sk_B_1))),
% 0.76/0.99      inference('sup-', [status(thm)], ['20', '21'])).
% 0.76/0.99  thf('23', plain,
% 0.76/0.99      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.76/0.99         (((X28) != (k1_relset_1 @ X28 @ X29 @ X30))
% 0.76/0.99          | (v1_funct_2 @ X30 @ X28 @ X29)
% 0.76/0.99          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.76/0.99  thf('24', plain,
% 0.76/0.99      ((((k1_relat_1 @ sk_B_1) != (k1_relat_1 @ sk_B_1))
% 0.76/0.99        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 0.76/0.99        | (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.76/0.99      inference('sup-', [status(thm)], ['22', '23'])).
% 0.76/0.99  thf('25', plain,
% 0.76/0.99      (((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.76/0.99        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.76/0.99      inference('simplify', [status(thm)], ['24'])).
% 0.76/0.99  thf('26', plain,
% 0.76/0.99      ((~ (v1_funct_1 @ sk_B_1)
% 0.76/0.99        | ~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.76/0.99        | ~ (m1_subset_1 @ sk_B_1 @ 
% 0.76/0.99             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.76/0.99  thf('27', plain,
% 0.76/0.99      ((~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.76/0.99         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.76/0.99      inference('split', [status(esa)], ['26'])).
% 0.76/0.99  thf('28', plain, ((v1_funct_1 @ sk_B_1)),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.76/0.99  thf('29', plain, ((~ (v1_funct_1 @ sk_B_1)) <= (~ ((v1_funct_1 @ sk_B_1)))),
% 0.76/0.99      inference('split', [status(esa)], ['26'])).
% 0.76/0.99  thf('30', plain, (((v1_funct_1 @ sk_B_1))),
% 0.76/0.99      inference('sup-', [status(thm)], ['28', '29'])).
% 0.76/0.99  thf('31', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_B_1 @ 
% 0.76/0.99        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.76/0.99      inference('demod', [status(thm)], ['15', '16'])).
% 0.76/0.99  thf('32', plain,
% 0.76/0.99      ((~ (m1_subset_1 @ sk_B_1 @ 
% 0.76/0.99           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))
% 0.76/0.99         <= (~
% 0.76/0.99             ((m1_subset_1 @ sk_B_1 @ 
% 0.76/0.99               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))))),
% 0.76/0.99      inference('split', [status(esa)], ['26'])).
% 0.76/0.99  thf('33', plain,
% 0.76/0.99      (((m1_subset_1 @ sk_B_1 @ 
% 0.76/0.99         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 0.76/0.99      inference('sup-', [status(thm)], ['31', '32'])).
% 0.76/0.99  thf('34', plain,
% 0.76/0.99      (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.76/0.99       ~
% 0.76/0.99       ((m1_subset_1 @ sk_B_1 @ 
% 0.76/0.99         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))) | 
% 0.76/0.99       ~ ((v1_funct_1 @ sk_B_1))),
% 0.76/0.99      inference('split', [status(esa)], ['26'])).
% 0.76/0.99  thf('35', plain, (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.76/0.99      inference('sat_resolution*', [status(thm)], ['30', '33', '34'])).
% 0.76/0.99  thf('36', plain, (~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.76/0.99      inference('simpl_trail', [status(thm)], ['27', '35'])).
% 0.76/0.99  thf('37', plain, (~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.76/0.99      inference('clc', [status(thm)], ['25', '36'])).
% 0.76/0.99  thf('38', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.76/0.99      inference('clc', [status(thm)], ['19', '37'])).
% 0.76/0.99  thf('39', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_B_1))),
% 0.76/0.99      inference('sup-', [status(thm)], ['10', '38'])).
% 0.76/0.99  thf('40', plain,
% 0.76/0.99      ((m1_subset_1 @ sk_B_1 @ 
% 0.76/0.99        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.76/0.99      inference('demod', [status(thm)], ['15', '16'])).
% 0.76/0.99  thf('41', plain,
% 0.76/0.99      (![X14 : $i, X15 : $i]:
% 0.76/0.99         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.76/0.99      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.99  thf('42', plain,
% 0.76/0.99      ((r1_tarski @ sk_B_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.76/0.99      inference('sup-', [status(thm)], ['40', '41'])).
% 0.76/0.99  thf('43', plain,
% 0.76/0.99      (![X1 : $i, X3 : $i]:
% 0.76/0.99         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.76/0.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/0.99  thf('44', plain,
% 0.76/0.99      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A) @ sk_B_1)
% 0.76/0.99        | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A) = (sk_B_1)))),
% 0.76/0.99      inference('sup-', [status(thm)], ['42', '43'])).
% 0.76/0.99  thf('45', plain,
% 0.76/0.99      (![X26 : $i, X27 : $i]:
% 0.76/0.99         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.99  thf('46', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.76/0.99      inference('clc', [status(thm)], ['19', '37'])).
% 0.76/0.99  thf('47', plain, (((sk_A) = (k1_xboole_0))),
% 0.76/0.99      inference('sup-', [status(thm)], ['45', '46'])).
% 0.76/0.99  thf(t113_zfmisc_1, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.76/0.99       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.76/0.99  thf('48', plain,
% 0.76/0.99      (![X8 : $i, X9 : $i]:
% 0.76/0.99         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 0.76/0.99      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.76/0.99  thf('49', plain,
% 0.76/0.99      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.99      inference('simplify', [status(thm)], ['48'])).
% 0.76/0.99  thf('50', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.76/0.99      inference('simplify', [status(thm)], ['1'])).
% 0.76/0.99  thf(l32_xboole_1, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.99  thf('51', plain,
% 0.76/0.99      (![X4 : $i, X6 : $i]:
% 0.76/0.99         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.76/0.99      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.76/0.99  thf(redefinition_k6_subset_1, axiom,
% 0.76/0.99    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.76/0.99  thf('52', plain,
% 0.76/0.99      (![X12 : $i, X13 : $i]:
% 0.76/0.99         ((k6_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))),
% 0.76/0.99      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.76/0.99  thf('53', plain,
% 0.76/0.99      (![X4 : $i, X6 : $i]:
% 0.76/0.99         (((k6_subset_1 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.76/0.99      inference('demod', [status(thm)], ['51', '52'])).
% 0.76/0.99  thf('54', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.76/0.99      inference('sup-', [status(thm)], ['50', '53'])).
% 0.76/0.99  thf(dt_k6_subset_1, axiom,
% 0.76/0.99    (![A:$i,B:$i]:
% 0.76/0.99     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.76/0.99  thf('55', plain,
% 0.76/0.99      (![X10 : $i, X11 : $i]:
% 0.76/0.99         (m1_subset_1 @ (k6_subset_1 @ X10 @ X11) @ (k1_zfmisc_1 @ X10))),
% 0.76/0.99      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 0.76/0.99  thf('56', plain,
% 0.76/0.99      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.76/0.99      inference('sup+', [status(thm)], ['54', '55'])).
% 0.76/0.99  thf('57', plain,
% 0.76/0.99      (![X14 : $i, X15 : $i]:
% 0.76/0.99         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.76/0.99      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.99  thf('58', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.76/0.99      inference('sup-', [status(thm)], ['56', '57'])).
% 0.76/0.99  thf('59', plain, (((sk_A) = (k1_xboole_0))),
% 0.76/0.99      inference('sup-', [status(thm)], ['45', '46'])).
% 0.76/0.99  thf('60', plain,
% 0.76/0.99      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.99      inference('simplify', [status(thm)], ['48'])).
% 0.76/0.99  thf('61', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.76/0.99      inference('demod', [status(thm)], ['44', '47', '49', '58', '59', '60'])).
% 0.76/0.99  thf('62', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))),
% 0.76/0.99      inference('demod', [status(thm)], ['39', '61'])).
% 0.76/0.99  thf('63', plain,
% 0.76/0.99      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.76/0.99         (((X31) != (k1_xboole_0))
% 0.76/0.99          | ((X32) = (k1_xboole_0))
% 0.76/0.99          | (v1_funct_2 @ X33 @ X32 @ X31)
% 0.76/0.99          | ((X33) != (k1_xboole_0))
% 0.76/0.99          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.76/0.99      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.76/0.99  thf('64', plain,
% 0.76/0.99      (![X32 : $i]:
% 0.76/0.99         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 0.76/0.99             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ k1_xboole_0)))
% 0.76/0.99          | (v1_funct_2 @ k1_xboole_0 @ X32 @ k1_xboole_0)
% 0.76/0.99          | ((X32) = (k1_xboole_0)))),
% 0.76/0.99      inference('simplify', [status(thm)], ['63'])).
% 0.76/0.99  thf('65', plain,
% 0.76/0.99      (![X8 : $i]: ((k2_zfmisc_1 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.99      inference('simplify', [status(thm)], ['48'])).
% 0.76/0.99  thf('66', plain,
% 0.76/0.99      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.76/0.99      inference('sup+', [status(thm)], ['54', '55'])).
% 0.76/0.99  thf('67', plain,
% 0.76/0.99      (![X32 : $i]:
% 0.76/0.99         ((v1_funct_2 @ k1_xboole_0 @ X32 @ k1_xboole_0)
% 0.76/0.99          | ((X32) = (k1_xboole_0)))),
% 0.76/0.99      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.76/0.99  thf('68', plain, (~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.76/0.99      inference('simpl_trail', [status(thm)], ['27', '35'])).
% 0.76/0.99  thf('69', plain, (((sk_A) = (k1_xboole_0))),
% 0.76/0.99      inference('sup-', [status(thm)], ['45', '46'])).
% 0.76/0.99  thf('70', plain,
% 0.76/0.99      (~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ k1_xboole_0)),
% 0.76/0.99      inference('demod', [status(thm)], ['68', '69'])).
% 0.76/0.99  thf('71', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.76/0.99      inference('demod', [status(thm)], ['44', '47', '49', '58', '59', '60'])).
% 0.76/0.99  thf('72', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.76/0.99      inference('demod', [status(thm)], ['44', '47', '49', '58', '59', '60'])).
% 0.76/0.99  thf('73', plain,
% 0.76/0.99      (~ (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ k1_xboole_0)),
% 0.76/0.99      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.76/0.99  thf('74', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.99      inference('sup-', [status(thm)], ['67', '73'])).
% 0.76/0.99  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.76/0.99  thf('75', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.99      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.99  thf('76', plain, ($false),
% 0.76/0.99      inference('demod', [status(thm)], ['62', '74', '75'])).
% 0.76/0.99  
% 0.76/0.99  % SZS output end Refutation
% 0.76/0.99  
% 0.76/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
