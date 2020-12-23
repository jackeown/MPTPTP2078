%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tyjF4VRP5d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:57 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 306 expanded)
%              Number of leaves         :   37 (  96 expanded)
%              Depth                    :   15
%              Number of atoms          :  640 (3932 expanded)
%              Number of equality atoms :   53 ( 184 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(t130_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( k1_relset_1 @ A @ B @ C )
          = A )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( k1_relset_1 @ A @ B @ C )
            = A )
         => ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ B )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('1',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('2',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X27
       != ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,
    ( ( sk_A != sk_A )
    | ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A )
    | ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
   <= ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('11',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['7'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('16',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['11','14','15'])).

thf('17',plain,(
    ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['8','16'])).

thf('18',plain,(
    ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['6','17'])).

thf('19',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['2','18'])).

thf('20',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('21',plain,(
    ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['2','18'])).

thf('22',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('26',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v5_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('30',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('31',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['28','31'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('34',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = sk_B )
    | ( r2_xboole_0 @ ( k2_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('36',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = sk_B )
    | ( r2_hidden @ ( sk_C @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('38',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('39',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ~ ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['37','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_C_1 )
        = sk_B )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('44',plain,(
    ! [X12: $i] :
      ( ( ( k2_relat_1 @ X12 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X12 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( sk_B != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( ( k1_relat_1 @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( sk_B != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k1_relat_1 @ sk_C_1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('49',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('50',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( sk_B != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( zip_tseitin_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('59',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('61',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X26 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('62',plain,(
    ! [X25: $i] :
      ( zip_tseitin_0 @ X25 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['60','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['23','59','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tyjF4VRP5d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:52:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.39/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.60  % Solved by: fo/fo7.sh
% 0.39/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.60  % done 236 iterations in 0.129s
% 0.39/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.60  % SZS output start Refutation
% 0.39/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.39/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.39/0.60  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.60  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.39/0.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.39/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.39/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.60  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.39/0.60  thf(t130_funct_2, conjecture,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.60       ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.39/0.60         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.60           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.39/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.60        ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.60            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.60          ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.39/0.60            ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.60              ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )),
% 0.39/0.60    inference('cnf.neg', [status(esa)], [t130_funct_2])).
% 0.39/0.60  thf('0', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(d1_funct_2, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.60       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.60           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.39/0.60             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.39/0.60         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.60           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.39/0.60             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.39/0.60  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.39/0.60  thf(zf_stmt_2, axiom,
% 0.39/0.60    (![C:$i,B:$i,A:$i]:
% 0.39/0.60     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.39/0.60       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.39/0.60  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.39/0.60  thf(zf_stmt_4, axiom,
% 0.39/0.60    (![B:$i,A:$i]:
% 0.39/0.60     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.60       ( zip_tseitin_0 @ B @ A ) ))).
% 0.39/0.60  thf(zf_stmt_5, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.60       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.39/0.60         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.60           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.39/0.60             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.39/0.60  thf('1', plain,
% 0.39/0.60      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.39/0.60         (~ (zip_tseitin_0 @ X30 @ X31)
% 0.39/0.60          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 0.39/0.60          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.60  thf('2', plain,
% 0.39/0.60      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.39/0.60        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.39/0.60      inference('sup-', [status(thm)], ['0', '1'])).
% 0.39/0.60  thf('3', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_A))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('4', plain,
% 0.39/0.60      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.39/0.60         (((X27) != (k1_relset_1 @ X27 @ X28 @ X29))
% 0.39/0.60          | (v1_funct_2 @ X29 @ X27 @ X28)
% 0.39/0.60          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.60  thf('5', plain,
% 0.39/0.60      ((((sk_A) != (sk_A))
% 0.39/0.60        | ~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)
% 0.39/0.60        | (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.39/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.39/0.60  thf('6', plain,
% 0.39/0.60      (((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.39/0.60        | ~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A))),
% 0.39/0.60      inference('simplify', [status(thm)], ['5'])).
% 0.39/0.60  thf('7', plain,
% 0.39/0.60      ((~ (v1_funct_1 @ sk_C_1)
% 0.39/0.60        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)
% 0.39/0.60        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('8', plain,
% 0.39/0.60      ((~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B))
% 0.39/0.60         <= (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('split', [status(esa)], ['7'])).
% 0.39/0.60  thf('9', plain, ((v1_funct_1 @ sk_C_1)),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('10', plain, ((~ (v1_funct_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ sk_C_1)))),
% 0.39/0.60      inference('split', [status(esa)], ['7'])).
% 0.39/0.60  thf('11', plain, (((v1_funct_1 @ sk_C_1))),
% 0.39/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.60  thf('12', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('13', plain,
% 0.39/0.60      ((~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.39/0.60         <= (~
% 0.39/0.60             ((m1_subset_1 @ sk_C_1 @ 
% 0.39/0.60               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))))),
% 0.39/0.60      inference('split', [status(esa)], ['7'])).
% 0.39/0.60  thf('14', plain,
% 0.39/0.60      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 0.39/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.60  thf('15', plain,
% 0.39/0.60      (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)) | 
% 0.39/0.60       ~ ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))) | 
% 0.39/0.60       ~ ((v1_funct_1 @ sk_C_1))),
% 0.39/0.60      inference('split', [status(esa)], ['7'])).
% 0.39/0.60  thf('16', plain, (~ ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B))),
% 0.39/0.60      inference('sat_resolution*', [status(thm)], ['11', '14', '15'])).
% 0.39/0.60  thf('17', plain, (~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.39/0.60      inference('simpl_trail', [status(thm)], ['8', '16'])).
% 0.39/0.60  thf('18', plain, (~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ sk_A)),
% 0.39/0.60      inference('clc', [status(thm)], ['6', '17'])).
% 0.39/0.60  thf('19', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A)),
% 0.39/0.60      inference('clc', [status(thm)], ['2', '18'])).
% 0.39/0.60  thf('20', plain,
% 0.39/0.60      (![X25 : $i, X26 : $i]:
% 0.39/0.60         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.39/0.60  thf('21', plain, (~ (zip_tseitin_0 @ sk_B @ sk_A)),
% 0.39/0.60      inference('clc', [status(thm)], ['2', '18'])).
% 0.39/0.60  thf('22', plain, (((sk_B) = (k1_xboole_0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.60  thf('23', plain, (~ (zip_tseitin_0 @ k1_xboole_0 @ sk_A)),
% 0.39/0.60      inference('demod', [status(thm)], ['19', '22'])).
% 0.39/0.60  thf('24', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(cc2_relset_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.39/0.60  thf('25', plain,
% 0.39/0.60      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.60         ((v5_relat_1 @ X17 @ X19)
% 0.39/0.60          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.39/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.60  thf('26', plain, ((v5_relat_1 @ sk_C_1 @ sk_B)),
% 0.39/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.60  thf(d19_relat_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( v1_relat_1 @ B ) =>
% 0.39/0.60       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.39/0.60  thf('27', plain,
% 0.39/0.60      (![X10 : $i, X11 : $i]:
% 0.39/0.60         (~ (v5_relat_1 @ X10 @ X11)
% 0.39/0.60          | (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 0.39/0.60          | ~ (v1_relat_1 @ X10))),
% 0.39/0.60      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.39/0.60  thf('28', plain,
% 0.39/0.60      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B))),
% 0.39/0.60      inference('sup-', [status(thm)], ['26', '27'])).
% 0.39/0.60  thf('29', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(cc1_relset_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.60       ( v1_relat_1 @ C ) ))).
% 0.39/0.60  thf('30', plain,
% 0.39/0.60      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.39/0.60         ((v1_relat_1 @ X14)
% 0.39/0.60          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.39/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.39/0.60  thf('31', plain, ((v1_relat_1 @ sk_C_1)),
% 0.39/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.39/0.60  thf('32', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B)),
% 0.39/0.60      inference('demod', [status(thm)], ['28', '31'])).
% 0.39/0.60  thf(d8_xboole_0, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.39/0.60       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.39/0.60  thf('33', plain,
% 0.39/0.60      (![X0 : $i, X2 : $i]:
% 0.39/0.60         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.39/0.60      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.39/0.60  thf('34', plain,
% 0.39/0.60      ((((k2_relat_1 @ sk_C_1) = (sk_B))
% 0.39/0.60        | (r2_xboole_0 @ (k2_relat_1 @ sk_C_1) @ sk_B))),
% 0.39/0.60      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.60  thf(t6_xboole_0, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.39/0.60          ( ![C:$i]:
% 0.39/0.60            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.39/0.60  thf('35', plain,
% 0.39/0.60      (![X3 : $i, X4 : $i]:
% 0.39/0.60         (~ (r2_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.39/0.60      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.39/0.60  thf('36', plain,
% 0.39/0.60      ((((k2_relat_1 @ sk_C_1) = (sk_B))
% 0.39/0.60        | (r2_hidden @ (sk_C @ sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B))),
% 0.39/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.39/0.60  thf('37', plain,
% 0.39/0.60      (![X25 : $i, X26 : $i]:
% 0.39/0.60         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.39/0.60  thf(t113_zfmisc_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]:
% 0.39/0.60     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.39/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.60  thf('38', plain,
% 0.39/0.60      (![X6 : $i, X7 : $i]:
% 0.39/0.60         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.39/0.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.39/0.60  thf('39', plain,
% 0.39/0.60      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.60      inference('simplify', [status(thm)], ['38'])).
% 0.39/0.60  thf(t152_zfmisc_1, axiom,
% 0.39/0.60    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.39/0.60  thf('40', plain,
% 0.39/0.60      (![X8 : $i, X9 : $i]: ~ (r2_hidden @ X8 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.39/0.60      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.39/0.60  thf('41', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.39/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.39/0.60  thf('42', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.60         (~ (r2_hidden @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.39/0.60      inference('sup-', [status(thm)], ['37', '41'])).
% 0.39/0.60  thf('43', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (((k2_relat_1 @ sk_C_1) = (sk_B)) | (zip_tseitin_0 @ sk_B @ X0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['36', '42'])).
% 0.39/0.60  thf(t65_relat_1, axiom,
% 0.39/0.60    (![A:$i]:
% 0.39/0.60     ( ( v1_relat_1 @ A ) =>
% 0.39/0.60       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.39/0.60         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.60  thf('44', plain,
% 0.39/0.60      (![X12 : $i]:
% 0.39/0.60         (((k2_relat_1 @ X12) != (k1_xboole_0))
% 0.39/0.60          | ((k1_relat_1 @ X12) = (k1_xboole_0))
% 0.39/0.60          | ~ (v1_relat_1 @ X12))),
% 0.39/0.60      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.39/0.60  thf('45', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (((sk_B) != (k1_xboole_0))
% 0.39/0.60          | (zip_tseitin_0 @ sk_B @ X0)
% 0.39/0.60          | ~ (v1_relat_1 @ sk_C_1)
% 0.39/0.60          | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.39/0.60      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.60  thf('46', plain, ((v1_relat_1 @ sk_C_1)),
% 0.39/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.39/0.60  thf('47', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (((sk_B) != (k1_xboole_0))
% 0.39/0.60          | (zip_tseitin_0 @ sk_B @ X0)
% 0.39/0.60          | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.39/0.60      inference('demod', [status(thm)], ['45', '46'])).
% 0.39/0.60  thf('48', plain,
% 0.39/0.60      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf(redefinition_k1_relset_1, axiom,
% 0.39/0.60    (![A:$i,B:$i,C:$i]:
% 0.39/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.60       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.39/0.60  thf('49', plain,
% 0.39/0.60      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.39/0.60         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.39/0.60          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.39/0.60      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.60  thf('50', plain,
% 0.39/0.60      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.39/0.60      inference('sup-', [status(thm)], ['48', '49'])).
% 0.39/0.60  thf('51', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_A))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.60  thf('52', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.39/0.60      inference('sup+', [status(thm)], ['50', '51'])).
% 0.39/0.60  thf('53', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (((sk_B) != (k1_xboole_0))
% 0.39/0.60          | (zip_tseitin_0 @ sk_B @ X0)
% 0.39/0.60          | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.60      inference('demod', [status(thm)], ['47', '52'])).
% 0.39/0.60  thf('54', plain,
% 0.39/0.60      (![X25 : $i, X26 : $i]:
% 0.39/0.60         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.39/0.60  thf('55', plain,
% 0.39/0.60      (![X0 : $i]: (((sk_A) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_B @ X0))),
% 0.39/0.60      inference('clc', [status(thm)], ['53', '54'])).
% 0.39/0.60  thf('56', plain, (((sk_B) = (k1_xboole_0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.60  thf('57', plain,
% 0.39/0.60      (![X0 : $i]:
% 0.39/0.60         (((sk_A) = (k1_xboole_0)) | (zip_tseitin_0 @ k1_xboole_0 @ X0))),
% 0.39/0.60      inference('demod', [status(thm)], ['55', '56'])).
% 0.39/0.60  thf('58', plain, (~ (zip_tseitin_0 @ k1_xboole_0 @ sk_A)),
% 0.39/0.60      inference('demod', [status(thm)], ['19', '22'])).
% 0.39/0.60  thf('59', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.60      inference('sup-', [status(thm)], ['57', '58'])).
% 0.39/0.60  thf('60', plain,
% 0.39/0.60      (![X25 : $i, X26 : $i]:
% 0.39/0.60         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.39/0.60  thf('61', plain,
% 0.39/0.60      (![X25 : $i, X26 : $i]:
% 0.39/0.60         ((zip_tseitin_0 @ X25 @ X26) | ((X26) != (k1_xboole_0)))),
% 0.39/0.60      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.39/0.60  thf('62', plain, (![X25 : $i]: (zip_tseitin_0 @ X25 @ k1_xboole_0)),
% 0.39/0.60      inference('simplify', [status(thm)], ['61'])).
% 0.39/0.60  thf('63', plain,
% 0.39/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.60         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.39/0.60      inference('sup+', [status(thm)], ['60', '62'])).
% 0.39/0.60  thf('64', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.39/0.60      inference('eq_fact', [status(thm)], ['63'])).
% 0.39/0.60  thf('65', plain, ($false),
% 0.39/0.60      inference('demod', [status(thm)], ['23', '59', '64'])).
% 0.39/0.60  
% 0.39/0.60  % SZS output end Refutation
% 0.39/0.60  
% 0.39/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
