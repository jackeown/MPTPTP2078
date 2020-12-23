%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qMNMP267aQ

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:19 EST 2020

% Result     : Theorem 1.91s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 218 expanded)
%              Number of leaves         :   41 (  83 expanded)
%              Depth                    :   25
%              Number of atoms          :  809 (2457 expanded)
%              Number of equality atoms :   48 ( 149 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

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

thf('1',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v5_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('8',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['5','8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ X0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) )
    | ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) @ sk_B ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('14',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('17',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X33: $i] :
      ( ~ ( r2_hidden @ X33 @ sk_B )
      | ( X33
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( sk_C @ X0 @ sk_B )
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X33: $i] :
      ( ~ ( r2_hidden @ X33 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X33 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
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

thf('27',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('28',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('31',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('34',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('35',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('37',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('41',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_C_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('45',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('47',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_B @ ( sk_C_1 @ k1_xboole_0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_relat_1 @ sk_C_2 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','47'])).

thf('49',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['14','17'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != sk_B )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('52',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['35','52'])).

thf('54',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['32','53'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('55',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X10 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X10 @ X9 ) @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('58',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['25','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('64',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['19','67'])).

thf('69',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('70',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['13','18'])).

thf('72',plain,
    ( sk_B
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['14','17'])).

thf('74',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qMNMP267aQ
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:24:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.91/2.09  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.91/2.09  % Solved by: fo/fo7.sh
% 1.91/2.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.91/2.09  % done 1033 iterations in 1.643s
% 1.91/2.09  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.91/2.09  % SZS output start Refutation
% 1.91/2.09  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.91/2.09  thf(sk_A_type, type, sk_A: $i).
% 1.91/2.09  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.91/2.09  thf(sk_B_type, type, sk_B: $i).
% 1.91/2.09  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.91/2.09  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.91/2.09  thf(sk_E_type, type, sk_E: $i > $i).
% 1.91/2.09  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.91/2.09  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.91/2.09  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.91/2.09  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.91/2.09  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.91/2.09  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.91/2.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.91/2.09  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.91/2.09  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.91/2.09  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.91/2.09  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.91/2.09  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.91/2.09  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.91/2.09  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.91/2.09  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.91/2.09  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.91/2.09  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.91/2.09  thf(t2_tarski, axiom,
% 1.91/2.09    (![A:$i,B:$i]:
% 1.91/2.09     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 1.91/2.09       ( ( A ) = ( B ) ) ))).
% 1.91/2.09  thf('0', plain,
% 1.91/2.09      (![X4 : $i, X5 : $i]:
% 1.91/2.09         (((X5) = (X4))
% 1.91/2.09          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 1.91/2.09          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 1.91/2.09      inference('cnf', [status(esa)], [t2_tarski])).
% 1.91/2.09  thf(t16_funct_2, conjecture,
% 1.91/2.09    (![A:$i,B:$i,C:$i]:
% 1.91/2.09     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.91/2.09         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.91/2.09       ( ( ![D:$i]:
% 1.91/2.09           ( ~( ( r2_hidden @ D @ B ) & 
% 1.91/2.09                ( ![E:$i]:
% 1.91/2.09                  ( ~( ( r2_hidden @ E @ A ) & 
% 1.91/2.09                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 1.91/2.09         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 1.91/2.09  thf(zf_stmt_0, negated_conjecture,
% 1.91/2.09    (~( ![A:$i,B:$i,C:$i]:
% 1.91/2.09        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.91/2.09            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.91/2.09          ( ( ![D:$i]:
% 1.91/2.09              ( ~( ( r2_hidden @ D @ B ) & 
% 1.91/2.09                   ( ![E:$i]:
% 1.91/2.09                     ( ~( ( r2_hidden @ E @ A ) & 
% 1.91/2.09                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 1.91/2.09            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 1.91/2.09    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 1.91/2.09  thf('1', plain,
% 1.91/2.09      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf(cc2_relset_1, axiom,
% 1.91/2.09    (![A:$i,B:$i,C:$i]:
% 1.91/2.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.91/2.09       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.91/2.09  thf('2', plain,
% 1.91/2.09      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.91/2.09         ((v5_relat_1 @ X16 @ X18)
% 1.91/2.09          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.91/2.09      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.91/2.09  thf('3', plain, ((v5_relat_1 @ sk_C_2 @ sk_B)),
% 1.91/2.09      inference('sup-', [status(thm)], ['1', '2'])).
% 1.91/2.09  thf(d19_relat_1, axiom,
% 1.91/2.09    (![A:$i,B:$i]:
% 1.91/2.09     ( ( v1_relat_1 @ B ) =>
% 1.91/2.09       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.91/2.09  thf('4', plain,
% 1.91/2.09      (![X7 : $i, X8 : $i]:
% 1.91/2.09         (~ (v5_relat_1 @ X7 @ X8)
% 1.91/2.09          | (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 1.91/2.09          | ~ (v1_relat_1 @ X7))),
% 1.91/2.09      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.91/2.09  thf('5', plain,
% 1.91/2.09      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B))),
% 1.91/2.09      inference('sup-', [status(thm)], ['3', '4'])).
% 1.91/2.09  thf('6', plain,
% 1.91/2.09      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf(cc1_relset_1, axiom,
% 1.91/2.09    (![A:$i,B:$i,C:$i]:
% 1.91/2.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.91/2.09       ( v1_relat_1 @ C ) ))).
% 1.91/2.09  thf('7', plain,
% 1.91/2.09      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.91/2.09         ((v1_relat_1 @ X13)
% 1.91/2.09          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.91/2.09      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.91/2.09  thf('8', plain, ((v1_relat_1 @ sk_C_2)),
% 1.91/2.09      inference('sup-', [status(thm)], ['6', '7'])).
% 1.91/2.09  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 1.91/2.09      inference('demod', [status(thm)], ['5', '8'])).
% 1.91/2.09  thf(d3_tarski, axiom,
% 1.91/2.09    (![A:$i,B:$i]:
% 1.91/2.09     ( ( r1_tarski @ A @ B ) <=>
% 1.91/2.09       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.91/2.09  thf('10', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.09         (~ (r2_hidden @ X0 @ X1)
% 1.91/2.09          | (r2_hidden @ X0 @ X2)
% 1.91/2.09          | ~ (r1_tarski @ X1 @ X2))),
% 1.91/2.09      inference('cnf', [status(esa)], [d3_tarski])).
% 1.91/2.09  thf('11', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['9', '10'])).
% 1.91/2.09  thf('12', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         ((r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ X0) @ X0)
% 1.91/2.09          | ((X0) = (k2_relat_1 @ sk_C_2))
% 1.91/2.09          | (r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ X0) @ sk_B))),
% 1.91/2.09      inference('sup-', [status(thm)], ['0', '11'])).
% 1.91/2.09  thf('13', plain,
% 1.91/2.09      ((((sk_B) = (k2_relat_1 @ sk_C_2))
% 1.91/2.09        | (r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B) @ sk_B))),
% 1.91/2.09      inference('eq_fact', [status(thm)], ['12'])).
% 1.91/2.09  thf('14', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('15', plain,
% 1.91/2.09      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf(redefinition_k2_relset_1, axiom,
% 1.91/2.09    (![A:$i,B:$i,C:$i]:
% 1.91/2.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.91/2.09       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.91/2.09  thf('16', plain,
% 1.91/2.09      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.91/2.09         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 1.91/2.09          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 1.91/2.09      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.91/2.09  thf('17', plain,
% 1.91/2.09      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 1.91/2.09      inference('sup-', [status(thm)], ['15', '16'])).
% 1.91/2.09  thf('18', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 1.91/2.09      inference('demod', [status(thm)], ['14', '17'])).
% 1.91/2.09  thf('19', plain,
% 1.91/2.09      ((r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B) @ sk_B)),
% 1.91/2.09      inference('simplify_reflect-', [status(thm)], ['13', '18'])).
% 1.91/2.09  thf('20', plain,
% 1.91/2.09      (![X1 : $i, X3 : $i]:
% 1.91/2.09         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.91/2.09      inference('cnf', [status(esa)], [d3_tarski])).
% 1.91/2.09  thf('21', plain,
% 1.91/2.09      (![X33 : $i]:
% 1.91/2.09         (~ (r2_hidden @ X33 @ sk_B)
% 1.91/2.09          | ((X33) = (k1_funct_1 @ sk_C_2 @ (sk_E @ X33))))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('22', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         ((r1_tarski @ sk_B @ X0)
% 1.91/2.09          | ((sk_C @ X0 @ sk_B)
% 1.91/2.09              = (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B)))))),
% 1.91/2.09      inference('sup-', [status(thm)], ['20', '21'])).
% 1.91/2.09  thf('23', plain,
% 1.91/2.09      (![X1 : $i, X3 : $i]:
% 1.91/2.09         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.91/2.09      inference('cnf', [status(esa)], [d3_tarski])).
% 1.91/2.09  thf('24', plain,
% 1.91/2.09      (![X33 : $i]:
% 1.91/2.09         (~ (r2_hidden @ X33 @ sk_B) | (r2_hidden @ (sk_E @ X33) @ sk_A))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('25', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         ((r1_tarski @ sk_B @ X0)
% 1.91/2.09          | (r2_hidden @ (sk_E @ (sk_C @ X0 @ sk_B)) @ sk_A))),
% 1.91/2.09      inference('sup-', [status(thm)], ['23', '24'])).
% 1.91/2.09  thf('26', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf(d1_funct_2, axiom,
% 1.91/2.09    (![A:$i,B:$i,C:$i]:
% 1.91/2.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.91/2.09       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.91/2.09           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.91/2.09             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.91/2.09         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.91/2.09           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.91/2.09             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.91/2.09  thf(zf_stmt_1, axiom,
% 1.91/2.09    (![C:$i,B:$i,A:$i]:
% 1.91/2.09     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.91/2.09       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.91/2.09  thf('27', plain,
% 1.91/2.09      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.91/2.09         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 1.91/2.09          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 1.91/2.09          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.91/2.09  thf('28', plain,
% 1.91/2.09      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 1.91/2.09        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_2)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['26', '27'])).
% 1.91/2.09  thf('29', plain,
% 1.91/2.09      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf(redefinition_k1_relset_1, axiom,
% 1.91/2.09    (![A:$i,B:$i,C:$i]:
% 1.91/2.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.91/2.09       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.91/2.09  thf('30', plain,
% 1.91/2.09      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.91/2.09         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 1.91/2.09          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.91/2.09      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.91/2.09  thf('31', plain,
% 1.91/2.09      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 1.91/2.09      inference('sup-', [status(thm)], ['29', '30'])).
% 1.91/2.09  thf('32', plain,
% 1.91/2.09      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 1.91/2.09        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 1.91/2.09      inference('demod', [status(thm)], ['28', '31'])).
% 1.91/2.09  thf('33', plain,
% 1.91/2.09      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.91/2.09  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.91/2.09  thf(zf_stmt_4, axiom,
% 1.91/2.09    (![B:$i,A:$i]:
% 1.91/2.09     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.91/2.09       ( zip_tseitin_0 @ B @ A ) ))).
% 1.91/2.09  thf(zf_stmt_5, axiom,
% 1.91/2.09    (![A:$i,B:$i,C:$i]:
% 1.91/2.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.91/2.09       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.91/2.09         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.91/2.09           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.91/2.09             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.91/2.09  thf('34', plain,
% 1.91/2.09      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.91/2.09         (~ (zip_tseitin_0 @ X30 @ X31)
% 1.91/2.09          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 1.91/2.09          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.91/2.09  thf('35', plain,
% 1.91/2.09      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)
% 1.91/2.09        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 1.91/2.09      inference('sup-', [status(thm)], ['33', '34'])).
% 1.91/2.09  thf('36', plain,
% 1.91/2.09      (![X25 : $i, X26 : $i]:
% 1.91/2.09         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.91/2.09  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.91/2.09  thf('37', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 1.91/2.09      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.91/2.09  thf('38', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.09         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 1.91/2.09      inference('sup+', [status(thm)], ['36', '37'])).
% 1.91/2.09  thf('39', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 1.91/2.09      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.91/2.09  thf('40', plain,
% 1.91/2.09      (![X4 : $i, X5 : $i]:
% 1.91/2.09         (((X5) = (X4))
% 1.91/2.09          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 1.91/2.09          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 1.91/2.09      inference('cnf', [status(esa)], [t2_tarski])).
% 1.91/2.09  thf(t7_ordinal1, axiom,
% 1.91/2.09    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.91/2.09  thf('41', plain,
% 1.91/2.09      (![X11 : $i, X12 : $i]:
% 1.91/2.09         (~ (r2_hidden @ X11 @ X12) | ~ (r1_tarski @ X12 @ X11))),
% 1.91/2.09      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.91/2.09  thf('42', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i]:
% 1.91/2.09         ((r2_hidden @ (sk_C_1 @ X0 @ X1) @ X1)
% 1.91/2.09          | ((X1) = (X0))
% 1.91/2.09          | ~ (r1_tarski @ X0 @ (sk_C_1 @ X0 @ X1)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['40', '41'])).
% 1.91/2.09  thf('43', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (((X0) = (k1_xboole_0))
% 1.91/2.09          | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0))),
% 1.91/2.09      inference('sup-', [status(thm)], ['39', '42'])).
% 1.91/2.09  thf('44', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['9', '10'])).
% 1.91/2.09  thf('45', plain,
% 1.91/2.09      ((((k2_relat_1 @ sk_C_2) = (k1_xboole_0))
% 1.91/2.09        | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ (k2_relat_1 @ sk_C_2)) @ sk_B))),
% 1.91/2.09      inference('sup-', [status(thm)], ['43', '44'])).
% 1.91/2.09  thf('46', plain,
% 1.91/2.09      (![X11 : $i, X12 : $i]:
% 1.91/2.09         (~ (r2_hidden @ X11 @ X12) | ~ (r1_tarski @ X12 @ X11))),
% 1.91/2.09      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.91/2.09  thf('47', plain,
% 1.91/2.09      ((((k2_relat_1 @ sk_C_2) = (k1_xboole_0))
% 1.91/2.09        | ~ (r1_tarski @ sk_B @ (sk_C_1 @ k1_xboole_0 @ (k2_relat_1 @ sk_C_2))))),
% 1.91/2.09      inference('sup-', [status(thm)], ['45', '46'])).
% 1.91/2.09  thf('48', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['38', '47'])).
% 1.91/2.09  thf('49', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 1.91/2.09      inference('demod', [status(thm)], ['14', '17'])).
% 1.91/2.09  thf('50', plain,
% 1.91/2.09      (![X0 : $i]: (((k1_xboole_0) != (sk_B)) | (zip_tseitin_0 @ sk_B @ X0))),
% 1.91/2.09      inference('sup-', [status(thm)], ['48', '49'])).
% 1.91/2.09  thf('51', plain,
% 1.91/2.09      (![X25 : $i, X26 : $i]:
% 1.91/2.09         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.91/2.09  thf('52', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 1.91/2.09      inference('clc', [status(thm)], ['50', '51'])).
% 1.91/2.09  thf('53', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B @ sk_A)),
% 1.91/2.09      inference('demod', [status(thm)], ['35', '52'])).
% 1.91/2.09  thf('54', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 1.91/2.09      inference('demod', [status(thm)], ['32', '53'])).
% 1.91/2.09  thf(t12_funct_1, axiom,
% 1.91/2.09    (![A:$i,B:$i]:
% 1.91/2.09     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.91/2.09       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 1.91/2.09         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 1.91/2.09  thf('55', plain,
% 1.91/2.09      (![X9 : $i, X10 : $i]:
% 1.91/2.09         (~ (r2_hidden @ X9 @ (k1_relat_1 @ X10))
% 1.91/2.09          | (r2_hidden @ (k1_funct_1 @ X10 @ X9) @ (k2_relat_1 @ X10))
% 1.91/2.09          | ~ (v1_funct_1 @ X10)
% 1.91/2.09          | ~ (v1_relat_1 @ X10))),
% 1.91/2.09      inference('cnf', [status(esa)], [t12_funct_1])).
% 1.91/2.09  thf('56', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (~ (r2_hidden @ X0 @ sk_A)
% 1.91/2.09          | ~ (v1_relat_1 @ sk_C_2)
% 1.91/2.09          | ~ (v1_funct_1 @ sk_C_2)
% 1.91/2.09          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['54', '55'])).
% 1.91/2.09  thf('57', plain, ((v1_relat_1 @ sk_C_2)),
% 1.91/2.09      inference('sup-', [status(thm)], ['6', '7'])).
% 1.91/2.09  thf('58', plain, ((v1_funct_1 @ sk_C_2)),
% 1.91/2.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.91/2.09  thf('59', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         (~ (r2_hidden @ X0 @ sk_A)
% 1.91/2.09          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2)))),
% 1.91/2.09      inference('demod', [status(thm)], ['56', '57', '58'])).
% 1.91/2.09  thf('60', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         ((r1_tarski @ sk_B @ X0)
% 1.91/2.09          | (r2_hidden @ (k1_funct_1 @ sk_C_2 @ (sk_E @ (sk_C @ X0 @ sk_B))) @ 
% 1.91/2.09             (k2_relat_1 @ sk_C_2)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['25', '59'])).
% 1.91/2.09  thf('61', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2))
% 1.91/2.09          | (r1_tarski @ sk_B @ X0)
% 1.91/2.09          | (r1_tarski @ sk_B @ X0))),
% 1.91/2.09      inference('sup+', [status(thm)], ['22', '60'])).
% 1.91/2.09  thf('62', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         ((r1_tarski @ sk_B @ X0)
% 1.91/2.09          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2)))),
% 1.91/2.09      inference('simplify', [status(thm)], ['61'])).
% 1.91/2.09  thf('63', plain,
% 1.91/2.09      (![X1 : $i, X3 : $i]:
% 1.91/2.09         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.91/2.09      inference('cnf', [status(esa)], [d3_tarski])).
% 1.91/2.09  thf('64', plain,
% 1.91/2.09      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 1.91/2.09        | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['62', '63'])).
% 1.91/2.09  thf('65', plain, ((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))),
% 1.91/2.09      inference('simplify', [status(thm)], ['64'])).
% 1.91/2.09  thf('66', plain,
% 1.91/2.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.91/2.09         (~ (r2_hidden @ X0 @ X1)
% 1.91/2.09          | (r2_hidden @ X0 @ X2)
% 1.91/2.09          | ~ (r1_tarski @ X1 @ X2))),
% 1.91/2.09      inference('cnf', [status(esa)], [d3_tarski])).
% 1.91/2.09  thf('67', plain,
% 1.91/2.09      (![X0 : $i]:
% 1.91/2.09         ((r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)) | ~ (r2_hidden @ X0 @ sk_B))),
% 1.91/2.09      inference('sup-', [status(thm)], ['65', '66'])).
% 1.91/2.09  thf('68', plain,
% 1.91/2.09      ((r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B) @ 
% 1.91/2.09        (k2_relat_1 @ sk_C_2))),
% 1.91/2.09      inference('sup-', [status(thm)], ['19', '67'])).
% 1.91/2.09  thf('69', plain,
% 1.91/2.09      (![X4 : $i, X5 : $i]:
% 1.91/2.09         (((X5) = (X4))
% 1.91/2.09          | ~ (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 1.91/2.09          | ~ (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 1.91/2.09      inference('cnf', [status(esa)], [t2_tarski])).
% 1.91/2.09  thf('70', plain,
% 1.91/2.09      ((~ (r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B) @ sk_B)
% 1.91/2.09        | ((sk_B) = (k2_relat_1 @ sk_C_2)))),
% 1.91/2.09      inference('sup-', [status(thm)], ['68', '69'])).
% 1.91/2.09  thf('71', plain,
% 1.91/2.09      ((r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B) @ sk_B)),
% 1.91/2.09      inference('simplify_reflect-', [status(thm)], ['13', '18'])).
% 1.91/2.09  thf('72', plain, (((sk_B) = (k2_relat_1 @ sk_C_2))),
% 1.91/2.09      inference('demod', [status(thm)], ['70', '71'])).
% 1.91/2.09  thf('73', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 1.91/2.09      inference('demod', [status(thm)], ['14', '17'])).
% 1.91/2.09  thf('74', plain, ($false),
% 1.91/2.09      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 1.91/2.09  
% 1.91/2.09  % SZS output end Refutation
% 1.91/2.09  
% 1.91/2.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
