%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L7PHzcc5R3

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:34 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  283 (1938 expanded)
%              Number of leaves         :   63 ( 637 expanded)
%              Depth                    :   28
%              Number of atoms          : 1873 (24420 expanded)
%              Number of equality atoms :  128 (1188 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X6 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( ( k2_subset_1 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('3',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_C_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( v1_relat_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('15',plain,(
    ! [X28: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_funct_1 @ X28 )
        = ( k4_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k2_funct_1 @ sk_C_1 )
      = ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ~ ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('22',plain,(
    ! [X29: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X29 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('23',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['9'])).

thf('24',plain,
    ( ( ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('28',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('29',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('30',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('31',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('32',plain,(
    ! [X53: $i] :
      ( v1_partfun1 @ ( k6_partfun1 @ X53 ) @ X53 ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('33',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('36',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('37',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('38',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('39',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X24 ) )
      = X24 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['36','39'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('41',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v4_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('44',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('45',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('46',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X30 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( v4_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','48'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['43','46'])).

thf('55',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['36','39'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('59',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_partfun1 @ X50 @ X51 )
      | ( v1_funct_2 @ X50 @ X51 @ X52 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('62',plain,(
    ! [X31: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('63',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('64',plain,(
    ! [X31: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X31 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_partfun1 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['60','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','66'])).

thf('68',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('69',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('70',plain,(
    ! [X25: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('71',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('72',plain,(
    ! [X25: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X25 ) )
      = X25 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('73',plain,(
    ! [X26: $i] :
      ( ( ( k5_relat_1 @ X26 @ ( k6_relat_1 @ ( k2_relat_1 @ X26 ) ) )
        = X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('74',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('75',plain,(
    ! [X26: $i] :
      ( ( ( k5_relat_1 @ X26 @ ( k6_partfun1 @ ( k2_relat_1 @ X26 ) ) )
        = X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X30 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf(t63_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('79',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X39 )
      | ~ ( v1_funct_1 @ X39 )
      | ( X39
        = ( k2_funct_1 @ X40 ) )
      | ( ( k5_relat_1 @ X40 @ X39 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X40 ) ) )
      | ( ( k2_relat_1 @ X40 )
       != ( k1_relat_1 @ X39 ) )
      | ~ ( v2_funct_1 @ X40 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('80',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('81',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( v1_relat_1 @ X39 )
      | ~ ( v1_funct_1 @ X39 )
      | ( X39
        = ( k2_funct_1 @ X40 ) )
      | ( ( k5_relat_1 @ X40 @ X39 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X40 ) ) )
      | ( ( k2_relat_1 @ X40 )
       != ( k1_relat_1 @ X39 ) )
      | ~ ( v2_funct_1 @ X40 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k6_partfun1 @ X0 ) )
       != ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) )
      | ( ( k6_partfun1 @ X0 )
        = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X24 ) )
      = X24 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('84',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X30 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('85',plain,(
    ! [X31: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X31 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf(t53_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ? [B: $i] :
            ( ( ( k5_relat_1 @ A @ B )
              = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
            & ( v1_funct_1 @ B )
            & ( v1_relat_1 @ B ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf('87',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ~ ( v1_funct_1 @ X36 )
      | ( ( k5_relat_1 @ X37 @ X36 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X37 ) ) )
      | ( v2_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t53_funct_1])).

thf('88',plain,(
    ! [X55: $i] :
      ( ( k6_partfun1 @ X55 )
      = ( k6_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('89',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ~ ( v1_funct_1 @ X36 )
      | ( ( k5_relat_1 @ X37 @ X36 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X37 ) ) )
      | ( v2_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X24 ) )
      = X24 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('92',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X30 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('93',plain,(
    ! [X31: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X31 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('94',plain,(
    ! [X31: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X31 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('95',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X30 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['90','91','92','93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X25: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X25 ) )
      = X25 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('99',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X24 ) )
      = X24 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('100',plain,(
    ! [X31: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X31 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('101',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X30 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ X0 ) )
      | ( X0 != X0 )
      | ( ( k6_partfun1 @ X0 )
        = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['82','83','84','85','97','98','99','100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k6_partfun1 @ X0 )
      = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = ( k2_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','103'])).

thf('105',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('106',plain,
    ( k1_xboole_0
    = ( k2_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','106'])).

thf('108',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('109',plain,
    ( ( ~ ( v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A )
      | ~ ( v1_xboole_0 @ sk_C_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ sk_C_1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('112',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( ( k2_relset_1 @ X48 @ X49 @ X47 )
        = ( k2_relat_1 @ X47 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('113',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['113','114'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('116',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('117',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('119',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['110','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('122',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( v4_relat_1 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('123',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('125',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('127',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('129',plain,(
    ! [X38: $i] :
      ( ~ ( v2_funct_1 @ X38 )
      | ( ( k2_relat_1 @ X38 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('130',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('132',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['130','131','132','133'])).

thf('135',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['113','114'])).

thf('136',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('137',plain,(
    ! [X56: $i] :
      ( ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) ) ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('138',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('140',plain,(
    ! [X38: $i] :
      ( ~ ( v2_funct_1 @ X38 )
      | ( ( k1_relat_1 @ X38 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('141',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('143',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['141','142','143','144'])).

thf('146',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('147',plain,(
    ! [X29: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X29 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('148',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('150',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('153',plain,(
    ! [X29: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X29 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('154',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('156',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('158',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['138','145','151','157'])).

thf(t9_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ( ( r1_tarski @ B @ C )
       => ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
            & ( v1_funct_2 @ D @ A @ C )
            & ( v1_funct_1 @ D ) )
          | ( ( A != k1_xboole_0 )
            & ( B = k1_xboole_0 ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_1 @ B @ A )
     => ( ( B = k1_xboole_0 )
        & ( A != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ A )
     => ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ B @ C )
       => ( ( zip_tseitin_1 @ B @ A )
          | ( zip_tseitin_0 @ D @ C @ A ) ) ) ) )).

thf('159',plain,(
    ! [X62: $i,X63: $i,X64: $i,X65: $i] :
      ( ~ ( r1_tarski @ X62 @ X63 )
      | ( zip_tseitin_1 @ X62 @ X64 )
      | ~ ( v1_funct_1 @ X65 )
      | ~ ( v1_funct_2 @ X65 @ X64 @ X62 )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X64 @ X62 ) ) )
      | ( zip_tseitin_0 @ X65 @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k4_relat_1 @ sk_C_1 ) @ X0 @ sk_B )
      | ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B @ ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('162',plain,(
    ! [X56: $i] :
      ( ( v1_funct_2 @ X56 @ ( k1_relat_1 @ X56 ) @ ( k2_relat_1 @ X56 ) )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('163',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['141','142','143','144'])).

thf('165',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('166',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('167',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['163','164','165','166'])).

thf('168',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k4_relat_1 @ sk_C_1 ) @ X0 @ sk_B )
      | ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['160','167','168'])).

thf('170',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
    | ( zip_tseitin_0 @ ( k4_relat_1 @ sk_C_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['127','169'])).

thf('171',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( v1_funct_2 @ X57 @ X59 @ X58 )
      | ~ ( zip_tseitin_0 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('172',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
    | ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('174',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('175',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C_1 ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['172','175'])).

thf('177',plain,(
    ! [X60: $i,X61: $i] :
      ( ( X60 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('178',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('179',plain,(
    ! [X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X23 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('180',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( ( k2_relat_1 @ sk_C_1 )
        = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('182',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = sk_B ),
    inference('sup+',[status(thm)],['113','114'])).

thf('183',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['180','181','182'])).

thf('184',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['183'])).

thf('185',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('186',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['120','184','185'])).

thf('187',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['9'])).

thf('188',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['27','186','187'])).

thf('189',plain,(
    ~ ( v1_xboole_0 @ ( k4_relat_1 @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['20','188'])).

thf('190',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
    | ( zip_tseitin_0 @ ( k4_relat_1 @ sk_C_1 ) @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['127','169'])).

thf('191',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X58 ) ) )
      | ~ ( zip_tseitin_0 @ X57 @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('192',plain,
    ( ( zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
    | ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['9'])).

thf('194',plain,
    ( ( k2_funct_1 @ sk_C_1 )
    = ( k4_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('195',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['27','186','187'])).

thf('197',plain,(
    ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['195','196'])).

thf('198',plain,(
    zip_tseitin_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(clc,[status(thm)],['192','197'])).

thf('199',plain,(
    ! [X60: $i,X61: $i] :
      ( ( X60 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('200',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['198','199'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('201',plain,(
    ! [X22: $i] :
      ( ( ( k1_relat_1 @ X22 )
       != k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('202',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('204',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['202','203'])).

thf('205',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,
    ( k1_xboole_0
    = ( k2_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('207',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['43','46'])).

thf('208',plain,(
    ! [X28: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_funct_1 @ X28 )
        = ( k4_relat_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('209',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( ( k2_funct_1 @ k1_xboole_0 )
      = ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v2_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['207','208'])).

thf('210',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['61','64'])).

thf('211',plain,
    ( ( ( k2_funct_1 @ k1_xboole_0 )
      = ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v2_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['209','210'])).

thf('212',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('213',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('214',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['212','213'])).

thf('215',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['211','214'])).

thf('216',plain,
    ( k1_xboole_0
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['206','215'])).

thf('217',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('218',plain,(
    $false ),
    inference(demod,[status(thm)],['189','205','216','217'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L7PHzcc5R3
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:23:03 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.77/0.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.77/0.97  % Solved by: fo/fo7.sh
% 0.77/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.97  % done 1027 iterations in 0.507s
% 0.77/0.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.77/0.97  % SZS output start Refutation
% 0.77/0.97  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.77/0.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.77/0.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.77/0.97  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.77/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/0.97  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.77/0.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/0.97  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.77/0.97  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.77/0.97  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.77/0.97  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.77/0.97  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.77/0.97  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.77/0.97  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.77/0.97  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.77/0.97  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.77/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.97  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.77/0.97  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.77/0.97  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.77/0.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.97  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.77/0.97  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.77/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.97  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.77/0.97  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.77/0.97  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.77/0.97  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.77/0.97  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.77/0.97  thf(d3_tarski, axiom,
% 0.77/0.97    (![A:$i,B:$i]:
% 0.77/0.97     ( ( r1_tarski @ A @ B ) <=>
% 0.77/0.97       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.77/0.97  thf('0', plain,
% 0.77/0.97      (![X1 : $i, X3 : $i]:
% 0.77/0.97         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.77/0.97      inference('cnf', [status(esa)], [d3_tarski])).
% 0.77/0.97  thf(dt_k2_subset_1, axiom,
% 0.77/0.97    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.77/0.97  thf('1', plain,
% 0.77/0.97      (![X6 : $i]: (m1_subset_1 @ (k2_subset_1 @ X6) @ (k1_zfmisc_1 @ X6))),
% 0.77/0.97      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.77/0.97  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.77/0.97  thf('2', plain, (![X5 : $i]: ((k2_subset_1 @ X5) = (X5))),
% 0.77/0.97      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.77/0.97  thf('3', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.77/0.97      inference('demod', [status(thm)], ['1', '2'])).
% 0.77/0.97  thf(t5_subset, axiom,
% 0.77/0.97    (![A:$i,B:$i,C:$i]:
% 0.77/0.97     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.77/0.97          ( v1_xboole_0 @ C ) ) ))).
% 0.77/0.97  thf('4', plain,
% 0.77/0.97      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.77/0.97         (~ (r2_hidden @ X10 @ X11)
% 0.77/0.97          | ~ (v1_xboole_0 @ X12)
% 0.77/0.97          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.77/0.97      inference('cnf', [status(esa)], [t5_subset])).
% 0.77/0.97  thf('5', plain,
% 0.77/0.97      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.77/0.97      inference('sup-', [status(thm)], ['3', '4'])).
% 0.77/0.97  thf('6', plain,
% 0.77/0.97      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.77/0.97      inference('sup-', [status(thm)], ['0', '5'])).
% 0.77/0.97  thf(t3_subset, axiom,
% 0.77/0.97    (![A:$i,B:$i]:
% 0.77/0.97     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.77/0.97  thf('7', plain,
% 0.77/0.97      (![X7 : $i, X9 : $i]:
% 0.77/0.97         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.77/0.97      inference('cnf', [status(esa)], [t3_subset])).
% 0.77/0.97  thf('8', plain,
% 0.77/0.97      (![X0 : $i, X1 : $i]:
% 0.77/0.97         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['6', '7'])).
% 0.77/0.97  thf(t31_funct_2, conjecture,
% 0.77/0.97    (![A:$i,B:$i,C:$i]:
% 0.77/0.97     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.77/0.97         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.77/0.97       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.77/0.97         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.77/0.97           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.77/0.97           ( m1_subset_1 @
% 0.77/0.97             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.77/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.97    (~( ![A:$i,B:$i,C:$i]:
% 0.77/0.97        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.77/0.97            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.77/0.97          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.77/0.97            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.77/0.97              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.77/0.97              ( m1_subset_1 @
% 0.77/0.97                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.77/0.97    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.77/0.97  thf('9', plain,
% 0.77/0.97      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 0.77/0.97        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)
% 0.77/0.97        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.77/0.97             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.97  thf('10', plain,
% 0.77/0.97      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.77/0.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.77/0.97         <= (~
% 0.77/0.97             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.77/0.97               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.77/0.97      inference('split', [status(esa)], ['9'])).
% 0.77/0.97  thf('11', plain,
% 0.77/0.97      ((~ (v1_xboole_0 @ (k2_funct_1 @ sk_C_1)))
% 0.77/0.97         <= (~
% 0.77/0.97             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.77/0.97               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.77/0.97      inference('sup-', [status(thm)], ['8', '10'])).
% 0.77/0.97  thf('12', plain,
% 0.77/0.97      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.97  thf(cc1_relset_1, axiom,
% 0.77/0.97    (![A:$i,B:$i,C:$i]:
% 0.77/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.97       ( v1_relat_1 @ C ) ))).
% 0.77/0.97  thf('13', plain,
% 0.77/0.97      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.77/0.97         ((v1_relat_1 @ X41)
% 0.77/0.97          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 0.77/0.97      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.77/0.97  thf('14', plain, ((v1_relat_1 @ sk_C_1)),
% 0.77/0.97      inference('sup-', [status(thm)], ['12', '13'])).
% 0.77/0.97  thf(d9_funct_1, axiom,
% 0.77/0.97    (![A:$i]:
% 0.77/0.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.77/0.97       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.77/0.97  thf('15', plain,
% 0.77/0.97      (![X28 : $i]:
% 0.77/0.97         (~ (v2_funct_1 @ X28)
% 0.77/0.97          | ((k2_funct_1 @ X28) = (k4_relat_1 @ X28))
% 0.77/0.97          | ~ (v1_funct_1 @ X28)
% 0.77/0.97          | ~ (v1_relat_1 @ X28))),
% 0.77/0.97      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.77/0.97  thf('16', plain,
% 0.77/0.97      ((~ (v1_funct_1 @ sk_C_1)
% 0.77/0.97        | ((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))
% 0.77/0.97        | ~ (v2_funct_1 @ sk_C_1))),
% 0.77/0.97      inference('sup-', [status(thm)], ['14', '15'])).
% 0.77/0.97  thf('17', plain, ((v1_funct_1 @ sk_C_1)),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.97  thf('18', plain, ((v2_funct_1 @ sk_C_1)),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.97  thf('19', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.77/0.97      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.77/0.97  thf('20', plain,
% 0.77/0.97      ((~ (v1_xboole_0 @ (k4_relat_1 @ sk_C_1)))
% 0.77/0.97         <= (~
% 0.77/0.97             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.77/0.97               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.77/0.97      inference('demod', [status(thm)], ['11', '19'])).
% 0.77/0.97  thf('21', plain, ((v1_relat_1 @ sk_C_1)),
% 0.77/0.97      inference('sup-', [status(thm)], ['12', '13'])).
% 0.77/0.97  thf(dt_k2_funct_1, axiom,
% 0.77/0.97    (![A:$i]:
% 0.77/0.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.77/0.97       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.77/0.97         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.77/0.97  thf('22', plain,
% 0.77/0.97      (![X29 : $i]:
% 0.77/0.97         ((v1_funct_1 @ (k2_funct_1 @ X29))
% 0.77/0.97          | ~ (v1_funct_1 @ X29)
% 0.77/0.97          | ~ (v1_relat_1 @ X29))),
% 0.77/0.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.77/0.97  thf('23', plain,
% 0.77/0.97      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 0.77/0.97         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.77/0.97      inference('split', [status(esa)], ['9'])).
% 0.77/0.97  thf('24', plain,
% 0.77/0.97      (((~ (v1_relat_1 @ sk_C_1) | ~ (v1_funct_1 @ sk_C_1)))
% 0.77/0.97         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.77/0.97      inference('sup-', [status(thm)], ['22', '23'])).
% 0.77/0.97  thf('25', plain, ((v1_funct_1 @ sk_C_1)),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.97  thf('26', plain,
% 0.77/0.97      ((~ (v1_relat_1 @ sk_C_1)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 0.77/0.97      inference('demod', [status(thm)], ['24', '25'])).
% 0.77/0.97  thf('27', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['21', '26'])).
% 0.77/0.97  thf(l13_xboole_0, axiom,
% 0.77/0.97    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.77/0.97  thf('28', plain,
% 0.77/0.97      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.77/0.97      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.77/0.97  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.77/0.97  thf('29', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.97      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.77/0.97  thf(redefinition_k6_partfun1, axiom,
% 0.77/0.97    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.77/0.97  thf('30', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 0.77/0.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.77/0.97  thf('31', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.97      inference('demod', [status(thm)], ['29', '30'])).
% 0.77/0.97  thf(dt_k6_partfun1, axiom,
% 0.77/0.97    (![A:$i]:
% 0.77/0.97     ( ( m1_subset_1 @
% 0.77/0.97         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.77/0.97       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.77/0.97  thf('32', plain, (![X53 : $i]: (v1_partfun1 @ (k6_partfun1 @ X53) @ X53)),
% 0.77/0.97      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.77/0.97  thf('33', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.77/0.97      inference('sup+', [status(thm)], ['31', '32'])).
% 0.77/0.97  thf('34', plain,
% 0.77/0.97      (![X0 : $i]: ((v1_partfun1 @ k1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.77/0.97      inference('sup+', [status(thm)], ['28', '33'])).
% 0.77/0.97  thf('35', plain,
% 0.77/0.97      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.77/0.97      inference('sup-', [status(thm)], ['0', '5'])).
% 0.77/0.97  thf('36', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.97      inference('demod', [status(thm)], ['29', '30'])).
% 0.77/0.97  thf(t71_relat_1, axiom,
% 0.77/0.97    (![A:$i]:
% 0.77/0.97     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.77/0.97       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.77/0.97  thf('37', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 0.77/0.97      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.77/0.97  thf('38', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 0.77/0.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.77/0.97  thf('39', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X24)) = (X24))),
% 0.77/0.97      inference('demod', [status(thm)], ['37', '38'])).
% 0.77/0.97  thf('40', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.97      inference('sup+', [status(thm)], ['36', '39'])).
% 0.77/0.97  thf(d18_relat_1, axiom,
% 0.77/0.97    (![A:$i,B:$i]:
% 0.77/0.97     ( ( v1_relat_1 @ B ) =>
% 0.77/0.97       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.77/0.97  thf('41', plain,
% 0.77/0.97      (![X13 : $i, X14 : $i]:
% 0.77/0.97         (~ (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.77/0.97          | (v4_relat_1 @ X13 @ X14)
% 0.77/0.97          | ~ (v1_relat_1 @ X13))),
% 0.77/0.97      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.77/0.97  thf('42', plain,
% 0.77/0.97      (![X0 : $i]:
% 0.77/0.97         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.77/0.97          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.77/0.97          | (v4_relat_1 @ k1_xboole_0 @ X0))),
% 0.77/0.97      inference('sup-', [status(thm)], ['40', '41'])).
% 0.77/0.97  thf('43', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.97      inference('demod', [status(thm)], ['29', '30'])).
% 0.77/0.97  thf(fc3_funct_1, axiom,
% 0.77/0.97    (![A:$i]:
% 0.77/0.97     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.77/0.97       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.77/0.97  thf('44', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.77/0.97      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.77/0.97  thf('45', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 0.77/0.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.77/0.97  thf('46', plain, (![X30 : $i]: (v1_relat_1 @ (k6_partfun1 @ X30))),
% 0.77/0.97      inference('demod', [status(thm)], ['44', '45'])).
% 0.77/0.97  thf('47', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.77/0.97      inference('sup+', [status(thm)], ['43', '46'])).
% 0.77/0.97  thf('48', plain,
% 0.77/0.97      (![X0 : $i]:
% 0.77/0.97         (~ (r1_tarski @ k1_xboole_0 @ X0) | (v4_relat_1 @ k1_xboole_0 @ X0))),
% 0.77/0.97      inference('demod', [status(thm)], ['42', '47'])).
% 0.77/0.97  thf('49', plain,
% 0.77/0.97      (![X0 : $i]:
% 0.77/0.97         (~ (v1_xboole_0 @ k1_xboole_0) | (v4_relat_1 @ k1_xboole_0 @ X0))),
% 0.77/0.97      inference('sup-', [status(thm)], ['35', '48'])).
% 0.77/0.97  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.77/0.97  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.77/0.97      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.77/0.97  thf('51', plain, (![X0 : $i]: (v4_relat_1 @ k1_xboole_0 @ X0)),
% 0.77/0.97      inference('demod', [status(thm)], ['49', '50'])).
% 0.77/0.97  thf('52', plain,
% 0.77/0.97      (![X13 : $i, X14 : $i]:
% 0.77/0.97         (~ (v4_relat_1 @ X13 @ X14)
% 0.77/0.97          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.77/0.97          | ~ (v1_relat_1 @ X13))),
% 0.77/0.97      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.77/0.97  thf('53', plain,
% 0.77/0.97      (![X0 : $i]:
% 0.77/0.97         (~ (v1_relat_1 @ k1_xboole_0)
% 0.77/0.97          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.77/0.97      inference('sup-', [status(thm)], ['51', '52'])).
% 0.77/0.97  thf('54', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.77/0.97      inference('sup+', [status(thm)], ['43', '46'])).
% 0.77/0.97  thf('55', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.97      inference('sup+', [status(thm)], ['36', '39'])).
% 0.77/0.97  thf('56', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.77/0.97      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.77/0.97  thf('57', plain,
% 0.77/0.97      (![X7 : $i, X9 : $i]:
% 0.77/0.97         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.77/0.97      inference('cnf', [status(esa)], [t3_subset])).
% 0.77/0.97  thf('58', plain,
% 0.77/0.97      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.77/0.97      inference('sup-', [status(thm)], ['56', '57'])).
% 0.77/0.97  thf(cc1_funct_2, axiom,
% 0.77/0.97    (![A:$i,B:$i,C:$i]:
% 0.77/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.97       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.77/0.97         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.77/0.97  thf('59', plain,
% 0.77/0.97      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.77/0.97         (~ (v1_funct_1 @ X50)
% 0.77/0.97          | ~ (v1_partfun1 @ X50 @ X51)
% 0.77/0.97          | (v1_funct_2 @ X50 @ X51 @ X52)
% 0.77/0.97          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52))))),
% 0.77/0.97      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.77/0.97  thf('60', plain,
% 0.77/0.97      (![X0 : $i, X1 : $i]:
% 0.77/0.97         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 0.77/0.97          | ~ (v1_partfun1 @ k1_xboole_0 @ X1)
% 0.77/0.97          | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.77/0.97      inference('sup-', [status(thm)], ['58', '59'])).
% 0.77/0.97  thf('61', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.97      inference('demod', [status(thm)], ['29', '30'])).
% 0.77/0.97  thf('62', plain, (![X31 : $i]: (v1_funct_1 @ (k6_relat_1 @ X31))),
% 0.77/0.97      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.77/0.97  thf('63', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 0.77/0.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.77/0.97  thf('64', plain, (![X31 : $i]: (v1_funct_1 @ (k6_partfun1 @ X31))),
% 0.77/0.97      inference('demod', [status(thm)], ['62', '63'])).
% 0.77/0.97  thf('65', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.77/0.97      inference('sup+', [status(thm)], ['61', '64'])).
% 0.77/0.97  thf('66', plain,
% 0.77/0.97      (![X0 : $i, X1 : $i]:
% 0.77/0.97         ((v1_funct_2 @ k1_xboole_0 @ X1 @ X0)
% 0.77/0.97          | ~ (v1_partfun1 @ k1_xboole_0 @ X1))),
% 0.77/0.97      inference('demod', [status(thm)], ['60', '65'])).
% 0.77/0.97  thf('67', plain,
% 0.77/0.97      (![X0 : $i, X1 : $i]:
% 0.77/0.97         (~ (v1_xboole_0 @ X0) | (v1_funct_2 @ k1_xboole_0 @ X0 @ X1))),
% 0.77/0.97      inference('sup-', [status(thm)], ['34', '66'])).
% 0.77/0.97  thf('68', plain,
% 0.77/0.97      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.77/0.97      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.77/0.97  thf('69', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.97      inference('demod', [status(thm)], ['29', '30'])).
% 0.77/0.97  thf('70', plain, (![X25 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 0.77/0.97      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.77/0.97  thf('71', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 0.77/0.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.77/0.97  thf('72', plain, (![X25 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X25)) = (X25))),
% 0.77/0.97      inference('demod', [status(thm)], ['70', '71'])).
% 0.77/0.97  thf(t80_relat_1, axiom,
% 0.77/0.97    (![A:$i]:
% 0.77/0.97     ( ( v1_relat_1 @ A ) =>
% 0.77/0.97       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.77/0.97  thf('73', plain,
% 0.77/0.97      (![X26 : $i]:
% 0.77/0.97         (((k5_relat_1 @ X26 @ (k6_relat_1 @ (k2_relat_1 @ X26))) = (X26))
% 0.77/0.97          | ~ (v1_relat_1 @ X26))),
% 0.77/0.97      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.77/0.97  thf('74', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 0.77/0.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.77/0.97  thf('75', plain,
% 0.77/0.97      (![X26 : $i]:
% 0.77/0.97         (((k5_relat_1 @ X26 @ (k6_partfun1 @ (k2_relat_1 @ X26))) = (X26))
% 0.77/0.97          | ~ (v1_relat_1 @ X26))),
% 0.77/0.97      inference('demod', [status(thm)], ['73', '74'])).
% 0.77/0.97  thf('76', plain,
% 0.77/0.97      (![X0 : $i]:
% 0.77/0.97         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 0.77/0.97            = (k6_partfun1 @ X0))
% 0.77/0.97          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.77/0.97      inference('sup+', [status(thm)], ['72', '75'])).
% 0.77/0.97  thf('77', plain, (![X30 : $i]: (v1_relat_1 @ (k6_partfun1 @ X30))),
% 0.77/0.97      inference('demod', [status(thm)], ['44', '45'])).
% 0.77/0.97  thf('78', plain,
% 0.77/0.97      (![X0 : $i]:
% 0.77/0.97         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 0.77/0.97           = (k6_partfun1 @ X0))),
% 0.77/0.97      inference('demod', [status(thm)], ['76', '77'])).
% 0.77/0.97  thf(t63_funct_1, axiom,
% 0.77/0.97    (![A:$i]:
% 0.77/0.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.77/0.97       ( ![B:$i]:
% 0.77/0.97         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.77/0.97           ( ( ( v2_funct_1 @ A ) & 
% 0.77/0.97               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.77/0.97               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.77/0.97             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.77/0.97  thf('79', plain,
% 0.77/0.97      (![X39 : $i, X40 : $i]:
% 0.77/0.97         (~ (v1_relat_1 @ X39)
% 0.77/0.97          | ~ (v1_funct_1 @ X39)
% 0.77/0.97          | ((X39) = (k2_funct_1 @ X40))
% 0.77/0.97          | ((k5_relat_1 @ X40 @ X39) != (k6_relat_1 @ (k1_relat_1 @ X40)))
% 0.77/0.97          | ((k2_relat_1 @ X40) != (k1_relat_1 @ X39))
% 0.77/0.97          | ~ (v2_funct_1 @ X40)
% 0.77/0.97          | ~ (v1_funct_1 @ X40)
% 0.77/0.97          | ~ (v1_relat_1 @ X40))),
% 0.77/0.97      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.77/0.97  thf('80', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 0.77/0.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.77/0.97  thf('81', plain,
% 0.77/0.97      (![X39 : $i, X40 : $i]:
% 0.77/0.97         (~ (v1_relat_1 @ X39)
% 0.77/0.97          | ~ (v1_funct_1 @ X39)
% 0.77/0.97          | ((X39) = (k2_funct_1 @ X40))
% 0.77/0.97          | ((k5_relat_1 @ X40 @ X39) != (k6_partfun1 @ (k1_relat_1 @ X40)))
% 0.77/0.97          | ((k2_relat_1 @ X40) != (k1_relat_1 @ X39))
% 0.77/0.97          | ~ (v2_funct_1 @ X40)
% 0.77/0.97          | ~ (v1_funct_1 @ X40)
% 0.77/0.97          | ~ (v1_relat_1 @ X40))),
% 0.77/0.97      inference('demod', [status(thm)], ['79', '80'])).
% 0.77/0.97  thf('82', plain,
% 0.77/0.97      (![X0 : $i]:
% 0.77/0.97         (((k6_partfun1 @ X0)
% 0.77/0.97            != (k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ X0))))
% 0.77/0.97          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.77/0.97          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.77/0.97          | ~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 0.77/0.97          | ((k2_relat_1 @ (k6_partfun1 @ X0))
% 0.77/0.97              != (k1_relat_1 @ (k6_partfun1 @ X0)))
% 0.77/0.97          | ((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0)))
% 0.77/0.97          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.77/0.97          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['78', '81'])).
% 0.77/0.97  thf('83', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X24)) = (X24))),
% 0.77/0.97      inference('demod', [status(thm)], ['37', '38'])).
% 0.77/0.97  thf('84', plain, (![X30 : $i]: (v1_relat_1 @ (k6_partfun1 @ X30))),
% 0.77/0.97      inference('demod', [status(thm)], ['44', '45'])).
% 0.77/0.97  thf('85', plain, (![X31 : $i]: (v1_funct_1 @ (k6_partfun1 @ X31))),
% 0.77/0.97      inference('demod', [status(thm)], ['62', '63'])).
% 0.77/0.97  thf('86', plain,
% 0.77/0.97      (![X0 : $i]:
% 0.77/0.97         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 0.77/0.97           = (k6_partfun1 @ X0))),
% 0.77/0.97      inference('demod', [status(thm)], ['76', '77'])).
% 0.77/0.97  thf(t53_funct_1, axiom,
% 0.77/0.97    (![A:$i]:
% 0.77/0.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.77/0.97       ( ( ?[B:$i]:
% 0.77/0.97           ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.77/0.97             ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 0.77/0.97         ( v2_funct_1 @ A ) ) ))).
% 0.77/0.97  thf('87', plain,
% 0.77/0.97      (![X36 : $i, X37 : $i]:
% 0.77/0.97         (~ (v1_relat_1 @ X36)
% 0.77/0.97          | ~ (v1_funct_1 @ X36)
% 0.77/0.97          | ((k5_relat_1 @ X37 @ X36) != (k6_relat_1 @ (k1_relat_1 @ X37)))
% 0.77/0.97          | (v2_funct_1 @ X37)
% 0.77/0.97          | ~ (v1_funct_1 @ X37)
% 0.77/0.97          | ~ (v1_relat_1 @ X37))),
% 0.77/0.97      inference('cnf', [status(esa)], [t53_funct_1])).
% 0.77/0.97  thf('88', plain, (![X55 : $i]: ((k6_partfun1 @ X55) = (k6_relat_1 @ X55))),
% 0.77/0.97      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.77/0.97  thf('89', plain,
% 0.77/0.97      (![X36 : $i, X37 : $i]:
% 0.77/0.97         (~ (v1_relat_1 @ X36)
% 0.77/0.97          | ~ (v1_funct_1 @ X36)
% 0.77/0.97          | ((k5_relat_1 @ X37 @ X36) != (k6_partfun1 @ (k1_relat_1 @ X37)))
% 0.77/0.97          | (v2_funct_1 @ X37)
% 0.77/0.97          | ~ (v1_funct_1 @ X37)
% 0.77/0.97          | ~ (v1_relat_1 @ X37))),
% 0.77/0.97      inference('demod', [status(thm)], ['87', '88'])).
% 0.77/0.97  thf('90', plain,
% 0.77/0.97      (![X0 : $i]:
% 0.77/0.97         (((k6_partfun1 @ X0)
% 0.77/0.97            != (k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ X0))))
% 0.77/0.97          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 0.77/0.97          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.77/0.97          | (v2_funct_1 @ (k6_partfun1 @ X0))
% 0.77/0.97          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 0.77/0.97          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['86', '89'])).
% 0.77/0.97  thf('91', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X24)) = (X24))),
% 0.77/0.97      inference('demod', [status(thm)], ['37', '38'])).
% 0.77/0.97  thf('92', plain, (![X30 : $i]: (v1_relat_1 @ (k6_partfun1 @ X30))),
% 0.77/0.97      inference('demod', [status(thm)], ['44', '45'])).
% 0.77/0.97  thf('93', plain, (![X31 : $i]: (v1_funct_1 @ (k6_partfun1 @ X31))),
% 0.77/0.97      inference('demod', [status(thm)], ['62', '63'])).
% 0.77/0.97  thf('94', plain, (![X31 : $i]: (v1_funct_1 @ (k6_partfun1 @ X31))),
% 0.77/0.97      inference('demod', [status(thm)], ['62', '63'])).
% 0.77/0.97  thf('95', plain, (![X30 : $i]: (v1_relat_1 @ (k6_partfun1 @ X30))),
% 0.77/0.97      inference('demod', [status(thm)], ['44', '45'])).
% 0.77/0.97  thf('96', plain,
% 0.77/0.97      (![X0 : $i]:
% 0.77/0.97         (((k6_partfun1 @ X0) != (k6_partfun1 @ X0))
% 0.77/0.97          | (v2_funct_1 @ (k6_partfun1 @ X0)))),
% 0.77/0.97      inference('demod', [status(thm)], ['90', '91', '92', '93', '94', '95'])).
% 0.77/0.97  thf('97', plain, (![X0 : $i]: (v2_funct_1 @ (k6_partfun1 @ X0))),
% 0.77/0.97      inference('simplify', [status(thm)], ['96'])).
% 0.77/0.97  thf('98', plain, (![X25 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X25)) = (X25))),
% 0.77/0.97      inference('demod', [status(thm)], ['70', '71'])).
% 0.77/0.97  thf('99', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X24)) = (X24))),
% 0.77/0.97      inference('demod', [status(thm)], ['37', '38'])).
% 0.77/0.97  thf('100', plain, (![X31 : $i]: (v1_funct_1 @ (k6_partfun1 @ X31))),
% 0.77/0.97      inference('demod', [status(thm)], ['62', '63'])).
% 0.77/0.97  thf('101', plain, (![X30 : $i]: (v1_relat_1 @ (k6_partfun1 @ X30))),
% 0.77/0.97      inference('demod', [status(thm)], ['44', '45'])).
% 0.77/0.97  thf('102', plain,
% 0.77/0.97      (![X0 : $i]:
% 0.77/0.97         (((k6_partfun1 @ X0) != (k6_partfun1 @ X0))
% 0.77/0.97          | ((X0) != (X0))
% 0.77/0.97          | ((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0))))),
% 0.77/0.97      inference('demod', [status(thm)],
% 0.77/0.97                ['82', '83', '84', '85', '97', '98', '99', '100', '101'])).
% 0.77/0.97  thf('103', plain,
% 0.77/0.97      (![X0 : $i]: ((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0)))),
% 0.77/0.97      inference('simplify', [status(thm)], ['102'])).
% 0.77/0.97  thf('104', plain,
% 0.77/0.97      (((k6_partfun1 @ k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))),
% 0.77/0.97      inference('sup+', [status(thm)], ['69', '103'])).
% 0.77/0.97  thf('105', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.97      inference('demod', [status(thm)], ['29', '30'])).
% 0.77/0.97  thf('106', plain, (((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))),
% 0.77/0.97      inference('demod', [status(thm)], ['104', '105'])).
% 0.77/0.97  thf('107', plain,
% 0.77/0.97      (![X0 : $i]: (((k1_xboole_0) = (k2_funct_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.77/0.97      inference('sup+', [status(thm)], ['68', '106'])).
% 0.77/0.97  thf('108', plain,
% 0.77/0.97      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 0.77/0.97         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.77/0.97      inference('split', [status(esa)], ['9'])).
% 0.77/0.97  thf('109', plain,
% 0.77/0.97      (((~ (v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A) | ~ (v1_xboole_0 @ sk_C_1)))
% 0.77/0.97         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['107', '108'])).
% 0.77/0.97  thf('110', plain,
% 0.77/0.97      (((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ sk_C_1)))
% 0.77/0.97         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['67', '109'])).
% 0.77/0.97  thf('111', plain,
% 0.77/0.97      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.97  thf(redefinition_k2_relset_1, axiom,
% 0.77/0.97    (![A:$i,B:$i,C:$i]:
% 0.77/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.97       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.77/0.97  thf('112', plain,
% 0.77/0.97      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.77/0.97         (((k2_relset_1 @ X48 @ X49 @ X47) = (k2_relat_1 @ X47))
% 0.77/0.97          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49))))),
% 0.77/0.97      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.77/0.97  thf('113', plain,
% 0.77/0.97      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.77/0.97      inference('sup-', [status(thm)], ['111', '112'])).
% 0.77/0.97  thf('114', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.97  thf('115', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.77/0.97      inference('sup+', [status(thm)], ['113', '114'])).
% 0.77/0.97  thf(fc9_relat_1, axiom,
% 0.77/0.97    (![A:$i]:
% 0.77/0.97     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.77/0.97       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.77/0.97  thf('116', plain,
% 0.77/0.97      (![X16 : $i]:
% 0.77/0.97         (~ (v1_xboole_0 @ (k2_relat_1 @ X16))
% 0.77/0.97          | ~ (v1_relat_1 @ X16)
% 0.77/0.97          | (v1_xboole_0 @ X16))),
% 0.77/0.97      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.77/0.97  thf('117', plain,
% 0.77/0.97      ((~ (v1_xboole_0 @ sk_B)
% 0.77/0.97        | (v1_xboole_0 @ sk_C_1)
% 0.77/0.97        | ~ (v1_relat_1 @ sk_C_1))),
% 0.77/0.97      inference('sup-', [status(thm)], ['115', '116'])).
% 0.77/0.97  thf('118', plain, ((v1_relat_1 @ sk_C_1)),
% 0.77/0.97      inference('sup-', [status(thm)], ['12', '13'])).
% 0.77/0.97  thf('119', plain, ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C_1))),
% 0.77/0.97      inference('demod', [status(thm)], ['117', '118'])).
% 0.77/0.97  thf('120', plain,
% 0.77/0.97      ((~ (v1_xboole_0 @ sk_B))
% 0.77/0.97         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.77/0.97      inference('clc', [status(thm)], ['110', '119'])).
% 0.77/0.97  thf('121', plain,
% 0.77/0.97      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.97  thf(cc2_relset_1, axiom,
% 0.77/0.97    (![A:$i,B:$i,C:$i]:
% 0.77/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.97       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.77/0.97  thf('122', plain,
% 0.77/0.97      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.77/0.97         ((v4_relat_1 @ X44 @ X45)
% 0.77/0.97          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46))))),
% 0.77/0.97      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.77/0.97  thf('123', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 0.77/0.97      inference('sup-', [status(thm)], ['121', '122'])).
% 0.77/0.97  thf('124', plain,
% 0.77/0.97      (![X13 : $i, X14 : $i]:
% 0.77/0.97         (~ (v4_relat_1 @ X13 @ X14)
% 0.77/0.97          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.77/0.97          | ~ (v1_relat_1 @ X13))),
% 0.77/0.97      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.77/0.97  thf('125', plain,
% 0.77/0.97      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 0.77/0.97      inference('sup-', [status(thm)], ['123', '124'])).
% 0.77/0.97  thf('126', plain, ((v1_relat_1 @ sk_C_1)),
% 0.77/0.97      inference('sup-', [status(thm)], ['12', '13'])).
% 0.77/0.97  thf('127', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 0.77/0.97      inference('demod', [status(thm)], ['125', '126'])).
% 0.77/0.97  thf('128', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.77/0.97      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.77/0.97  thf(t55_funct_1, axiom,
% 0.77/0.97    (![A:$i]:
% 0.77/0.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.77/0.97       ( ( v2_funct_1 @ A ) =>
% 0.77/0.97         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.77/0.97           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.77/0.97  thf('129', plain,
% 0.77/0.97      (![X38 : $i]:
% 0.77/0.97         (~ (v2_funct_1 @ X38)
% 0.77/0.97          | ((k2_relat_1 @ X38) = (k1_relat_1 @ (k2_funct_1 @ X38)))
% 0.77/0.97          | ~ (v1_funct_1 @ X38)
% 0.77/0.97          | ~ (v1_relat_1 @ X38))),
% 0.77/0.97      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.77/0.97  thf('130', plain,
% 0.77/0.97      ((((k2_relat_1 @ sk_C_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 0.77/0.97        | ~ (v1_relat_1 @ sk_C_1)
% 0.77/0.97        | ~ (v1_funct_1 @ sk_C_1)
% 0.77/0.97        | ~ (v2_funct_1 @ sk_C_1))),
% 0.77/0.97      inference('sup+', [status(thm)], ['128', '129'])).
% 0.77/0.97  thf('131', plain, ((v1_relat_1 @ sk_C_1)),
% 0.77/0.97      inference('sup-', [status(thm)], ['12', '13'])).
% 0.77/0.97  thf('132', plain, ((v1_funct_1 @ sk_C_1)),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.97  thf('133', plain, ((v2_funct_1 @ sk_C_1)),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.97  thf('134', plain,
% 0.77/0.97      (((k2_relat_1 @ sk_C_1) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.77/0.97      inference('demod', [status(thm)], ['130', '131', '132', '133'])).
% 0.77/0.97  thf('135', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.77/0.97      inference('sup+', [status(thm)], ['113', '114'])).
% 0.77/0.97  thf('136', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.77/0.97      inference('demod', [status(thm)], ['134', '135'])).
% 0.77/0.97  thf(t3_funct_2, axiom,
% 0.77/0.97    (![A:$i]:
% 0.77/0.97     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.77/0.97       ( ( v1_funct_1 @ A ) & 
% 0.77/0.97         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.77/0.97         ( m1_subset_1 @
% 0.77/0.97           A @ 
% 0.77/0.97           ( k1_zfmisc_1 @
% 0.77/0.97             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.77/0.97  thf('137', plain,
% 0.77/0.97      (![X56 : $i]:
% 0.77/0.97         ((m1_subset_1 @ X56 @ 
% 0.77/0.97           (k1_zfmisc_1 @ 
% 0.77/0.97            (k2_zfmisc_1 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56))))
% 0.77/0.97          | ~ (v1_funct_1 @ X56)
% 0.77/0.97          | ~ (v1_relat_1 @ X56))),
% 0.77/0.97      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.77/0.97  thf('138', plain,
% 0.77/0.97      (((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 0.77/0.97         (k1_zfmisc_1 @ 
% 0.77/0.97          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))))
% 0.77/0.97        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 0.77/0.97        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.77/0.97      inference('sup+', [status(thm)], ['136', '137'])).
% 0.77/0.97  thf('139', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.77/0.97      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.77/0.97  thf('140', plain,
% 0.77/0.97      (![X38 : $i]:
% 0.77/0.97         (~ (v2_funct_1 @ X38)
% 0.77/0.97          | ((k1_relat_1 @ X38) = (k2_relat_1 @ (k2_funct_1 @ X38)))
% 0.77/0.97          | ~ (v1_funct_1 @ X38)
% 0.77/0.97          | ~ (v1_relat_1 @ X38))),
% 0.77/0.97      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.77/0.97  thf('141', plain,
% 0.77/0.97      ((((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 0.77/0.97        | ~ (v1_relat_1 @ sk_C_1)
% 0.77/0.97        | ~ (v1_funct_1 @ sk_C_1)
% 0.77/0.97        | ~ (v2_funct_1 @ sk_C_1))),
% 0.77/0.97      inference('sup+', [status(thm)], ['139', '140'])).
% 0.77/0.97  thf('142', plain, ((v1_relat_1 @ sk_C_1)),
% 0.77/0.97      inference('sup-', [status(thm)], ['12', '13'])).
% 0.77/0.97  thf('143', plain, ((v1_funct_1 @ sk_C_1)),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.97  thf('144', plain, ((v2_funct_1 @ sk_C_1)),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.97  thf('145', plain,
% 0.77/0.97      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.77/0.97      inference('demod', [status(thm)], ['141', '142', '143', '144'])).
% 0.77/0.97  thf('146', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.77/0.97      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.77/0.97  thf('147', plain,
% 0.77/0.97      (![X29 : $i]:
% 0.77/0.97         ((v1_relat_1 @ (k2_funct_1 @ X29))
% 0.77/0.97          | ~ (v1_funct_1 @ X29)
% 0.77/0.97          | ~ (v1_relat_1 @ X29))),
% 0.77/0.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.77/0.97  thf('148', plain,
% 0.77/0.97      (((v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 0.77/0.97        | ~ (v1_relat_1 @ sk_C_1)
% 0.77/0.97        | ~ (v1_funct_1 @ sk_C_1))),
% 0.77/0.97      inference('sup+', [status(thm)], ['146', '147'])).
% 0.77/0.97  thf('149', plain, ((v1_relat_1 @ sk_C_1)),
% 0.77/0.97      inference('sup-', [status(thm)], ['12', '13'])).
% 0.77/0.97  thf('150', plain, ((v1_funct_1 @ sk_C_1)),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.97  thf('151', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 0.77/0.97      inference('demod', [status(thm)], ['148', '149', '150'])).
% 0.77/0.97  thf('152', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.77/0.97      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.77/0.97  thf('153', plain,
% 0.77/0.97      (![X29 : $i]:
% 0.77/0.97         ((v1_funct_1 @ (k2_funct_1 @ X29))
% 0.77/0.97          | ~ (v1_funct_1 @ X29)
% 0.77/0.97          | ~ (v1_relat_1 @ X29))),
% 0.77/0.97      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.77/0.97  thf('154', plain,
% 0.77/0.97      (((v1_funct_1 @ (k4_relat_1 @ sk_C_1))
% 0.77/0.97        | ~ (v1_relat_1 @ sk_C_1)
% 0.77/0.97        | ~ (v1_funct_1 @ sk_C_1))),
% 0.77/0.97      inference('sup+', [status(thm)], ['152', '153'])).
% 0.77/0.97  thf('155', plain, ((v1_relat_1 @ sk_C_1)),
% 0.77/0.97      inference('sup-', [status(thm)], ['12', '13'])).
% 0.77/0.97  thf('156', plain, ((v1_funct_1 @ sk_C_1)),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.97  thf('157', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C_1))),
% 0.77/0.97      inference('demod', [status(thm)], ['154', '155', '156'])).
% 0.77/0.97  thf('158', plain,
% 0.77/0.97      ((m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 0.77/0.97        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C_1))))),
% 0.77/0.97      inference('demod', [status(thm)], ['138', '145', '151', '157'])).
% 0.77/0.97  thf(t9_funct_2, axiom,
% 0.77/0.97    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.97     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.77/0.97         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.77/0.97       ( ( r1_tarski @ B @ C ) =>
% 0.77/0.97         ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 0.77/0.97             ( v1_funct_2 @ D @ A @ C ) & ( v1_funct_1 @ D ) ) | 
% 0.77/0.97           ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.77/0.97  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 0.77/0.97  thf(zf_stmt_2, axiom,
% 0.77/0.97    (![B:$i,A:$i]:
% 0.77/0.97     ( ( zip_tseitin_1 @ B @ A ) =>
% 0.77/0.97       ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) ))).
% 0.77/0.97  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.77/0.97  thf(zf_stmt_4, axiom,
% 0.77/0.97    (![D:$i,C:$i,A:$i]:
% 0.77/0.97     ( ( zip_tseitin_0 @ D @ C @ A ) =>
% 0.77/0.97       ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.77/0.97         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.77/0.97  thf(zf_stmt_5, axiom,
% 0.77/0.97    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.97     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.77/0.97         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.77/0.97       ( ( r1_tarski @ B @ C ) =>
% 0.77/0.97         ( ( zip_tseitin_1 @ B @ A ) | ( zip_tseitin_0 @ D @ C @ A ) ) ) ))).
% 0.77/0.97  thf('159', plain,
% 0.77/0.97      (![X62 : $i, X63 : $i, X64 : $i, X65 : $i]:
% 0.77/0.97         (~ (r1_tarski @ X62 @ X63)
% 0.77/0.97          | (zip_tseitin_1 @ X62 @ X64)
% 0.77/0.97          | ~ (v1_funct_1 @ X65)
% 0.77/0.97          | ~ (v1_funct_2 @ X65 @ X64 @ X62)
% 0.77/0.97          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X64 @ X62)))
% 0.77/0.97          | (zip_tseitin_0 @ X65 @ X63 @ X64))),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.77/0.97  thf('160', plain,
% 0.77/0.97      (![X0 : $i]:
% 0.77/0.97         ((zip_tseitin_0 @ (k4_relat_1 @ sk_C_1) @ X0 @ sk_B)
% 0.77/0.97          | ~ (v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B @ 
% 0.77/0.97               (k1_relat_1 @ sk_C_1))
% 0.77/0.97          | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C_1))
% 0.77/0.97          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.77/0.97          | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0))),
% 0.77/0.97      inference('sup-', [status(thm)], ['158', '159'])).
% 0.77/0.97  thf('161', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.77/0.97      inference('demod', [status(thm)], ['134', '135'])).
% 0.77/0.97  thf('162', plain,
% 0.77/0.97      (![X56 : $i]:
% 0.77/0.97         ((v1_funct_2 @ X56 @ (k1_relat_1 @ X56) @ (k2_relat_1 @ X56))
% 0.77/0.97          | ~ (v1_funct_1 @ X56)
% 0.77/0.97          | ~ (v1_relat_1 @ X56))),
% 0.77/0.97      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.77/0.97  thf('163', plain,
% 0.77/0.97      (((v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B @ 
% 0.77/0.97         (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))
% 0.77/0.97        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C_1))
% 0.77/0.97        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.77/0.97      inference('sup+', [status(thm)], ['161', '162'])).
% 0.77/0.97  thf('164', plain,
% 0.77/0.97      (((k1_relat_1 @ sk_C_1) = (k2_relat_1 @ (k4_relat_1 @ sk_C_1)))),
% 0.77/0.97      inference('demod', [status(thm)], ['141', '142', '143', '144'])).
% 0.77/0.97  thf('165', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C_1))),
% 0.77/0.97      inference('demod', [status(thm)], ['148', '149', '150'])).
% 0.77/0.97  thf('166', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C_1))),
% 0.77/0.97      inference('demod', [status(thm)], ['154', '155', '156'])).
% 0.77/0.97  thf('167', plain,
% 0.77/0.97      ((v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B @ (k1_relat_1 @ sk_C_1))),
% 0.77/0.97      inference('demod', [status(thm)], ['163', '164', '165', '166'])).
% 0.77/0.97  thf('168', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C_1))),
% 0.77/0.97      inference('demod', [status(thm)], ['154', '155', '156'])).
% 0.77/0.97  thf('169', plain,
% 0.77/0.97      (![X0 : $i]:
% 0.77/0.97         ((zip_tseitin_0 @ (k4_relat_1 @ sk_C_1) @ X0 @ sk_B)
% 0.77/0.97          | (zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.77/0.97          | ~ (r1_tarski @ (k1_relat_1 @ sk_C_1) @ X0))),
% 0.77/0.97      inference('demod', [status(thm)], ['160', '167', '168'])).
% 0.77/0.97  thf('170', plain,
% 0.77/0.97      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.77/0.97        | (zip_tseitin_0 @ (k4_relat_1 @ sk_C_1) @ sk_A @ sk_B))),
% 0.77/0.97      inference('sup-', [status(thm)], ['127', '169'])).
% 0.77/0.97  thf('171', plain,
% 0.77/0.97      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.77/0.97         ((v1_funct_2 @ X57 @ X59 @ X58) | ~ (zip_tseitin_0 @ X57 @ X58 @ X59))),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.77/0.97  thf('172', plain,
% 0.77/0.97      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.77/0.97        | (v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B @ sk_A))),
% 0.77/0.97      inference('sup-', [status(thm)], ['170', '171'])).
% 0.77/0.97  thf('173', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.77/0.97      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.77/0.97  thf('174', plain,
% 0.77/0.97      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))
% 0.77/0.97         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.77/0.97      inference('split', [status(esa)], ['9'])).
% 0.77/0.97  thf('175', plain,
% 0.77/0.97      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C_1) @ sk_B @ sk_A))
% 0.77/0.97         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['173', '174'])).
% 0.77/0.97  thf('176', plain,
% 0.77/0.97      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B))
% 0.77/0.97         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['172', '175'])).
% 0.77/0.97  thf('177', plain,
% 0.77/0.97      (![X60 : $i, X61 : $i]:
% 0.77/0.97         (((X60) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X60 @ X61))),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.77/0.97  thf('178', plain,
% 0.77/0.97      ((((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))
% 0.77/0.97         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['176', '177'])).
% 0.77/0.97  thf(t65_relat_1, axiom,
% 0.77/0.97    (![A:$i]:
% 0.77/0.97     ( ( v1_relat_1 @ A ) =>
% 0.77/0.97       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.77/0.97         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.77/0.97  thf('179', plain,
% 0.77/0.97      (![X23 : $i]:
% 0.77/0.97         (((k1_relat_1 @ X23) != (k1_xboole_0))
% 0.77/0.97          | ((k2_relat_1 @ X23) = (k1_xboole_0))
% 0.77/0.97          | ~ (v1_relat_1 @ X23))),
% 0.77/0.97      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.77/0.97  thf('180', plain,
% 0.77/0.97      (((((k1_xboole_0) != (k1_xboole_0))
% 0.77/0.97         | ~ (v1_relat_1 @ sk_C_1)
% 0.77/0.97         | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0))))
% 0.77/0.97         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['178', '179'])).
% 0.77/0.97  thf('181', plain, ((v1_relat_1 @ sk_C_1)),
% 0.77/0.97      inference('sup-', [status(thm)], ['12', '13'])).
% 0.77/0.97  thf('182', plain, (((k2_relat_1 @ sk_C_1) = (sk_B))),
% 0.77/0.97      inference('sup+', [status(thm)], ['113', '114'])).
% 0.77/0.97  thf('183', plain,
% 0.77/0.97      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.77/0.97         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.77/0.97      inference('demod', [status(thm)], ['180', '181', '182'])).
% 0.77/0.97  thf('184', plain,
% 0.77/0.97      ((((sk_B) = (k1_xboole_0)))
% 0.77/0.97         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)))),
% 0.77/0.97      inference('simplify', [status(thm)], ['183'])).
% 0.77/0.97  thf('185', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.77/0.97      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.77/0.97  thf('186', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A))),
% 0.77/0.97      inference('demod', [status(thm)], ['120', '184', '185'])).
% 0.77/0.97  thf('187', plain,
% 0.77/0.97      (~
% 0.77/0.97       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.77/0.97         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.77/0.97       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ sk_B @ sk_A)) | 
% 0.77/0.97       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 0.77/0.97      inference('split', [status(esa)], ['9'])).
% 0.77/0.97  thf('188', plain,
% 0.77/0.97      (~
% 0.77/0.97       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.77/0.97         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.77/0.97      inference('sat_resolution*', [status(thm)], ['27', '186', '187'])).
% 0.77/0.97  thf('189', plain, (~ (v1_xboole_0 @ (k4_relat_1 @ sk_C_1))),
% 0.77/0.97      inference('simpl_trail', [status(thm)], ['20', '188'])).
% 0.77/0.97  thf('190', plain,
% 0.77/0.97      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.77/0.97        | (zip_tseitin_0 @ (k4_relat_1 @ sk_C_1) @ sk_A @ sk_B))),
% 0.77/0.97      inference('sup-', [status(thm)], ['127', '169'])).
% 0.77/0.97  thf('191', plain,
% 0.77/0.97      (![X57 : $i, X58 : $i, X59 : $i]:
% 0.77/0.97         ((m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X58)))
% 0.77/0.97          | ~ (zip_tseitin_0 @ X57 @ X58 @ X59))),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.77/0.97  thf('192', plain,
% 0.77/0.97      (((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.77/0.97        | (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 0.77/0.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.77/0.97      inference('sup-', [status(thm)], ['190', '191'])).
% 0.77/0.97  thf('193', plain,
% 0.77/0.97      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.77/0.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.77/0.97         <= (~
% 0.77/0.97             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.77/0.97               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.77/0.97      inference('split', [status(esa)], ['9'])).
% 0.77/0.97  thf('194', plain, (((k2_funct_1 @ sk_C_1) = (k4_relat_1 @ sk_C_1))),
% 0.77/0.97      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.77/0.97  thf('195', plain,
% 0.77/0.97      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 0.77/0.97           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.77/0.97         <= (~
% 0.77/0.97             ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.77/0.97               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.77/0.97      inference('demod', [status(thm)], ['193', '194'])).
% 0.77/0.97  thf('196', plain,
% 0.77/0.97      (~
% 0.77/0.97       ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 0.77/0.97         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.77/0.97      inference('sat_resolution*', [status(thm)], ['27', '186', '187'])).
% 0.77/0.97  thf('197', plain,
% 0.77/0.97      (~ (m1_subset_1 @ (k4_relat_1 @ sk_C_1) @ 
% 0.77/0.97          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.77/0.97      inference('simpl_trail', [status(thm)], ['195', '196'])).
% 0.77/0.97  thf('198', plain, ((zip_tseitin_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)),
% 0.77/0.97      inference('clc', [status(thm)], ['192', '197'])).
% 0.77/0.97  thf('199', plain,
% 0.77/0.97      (![X60 : $i, X61 : $i]:
% 0.77/0.97         (((X60) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X60 @ X61))),
% 0.77/0.97      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.77/0.97  thf('200', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.77/0.97      inference('sup-', [status(thm)], ['198', '199'])).
% 0.77/0.97  thf(t64_relat_1, axiom,
% 0.77/0.97    (![A:$i]:
% 0.77/0.97     ( ( v1_relat_1 @ A ) =>
% 0.77/0.97       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.77/0.97           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.77/0.97         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.77/0.97  thf('201', plain,
% 0.77/0.97      (![X22 : $i]:
% 0.77/0.97         (((k1_relat_1 @ X22) != (k1_xboole_0))
% 0.77/0.97          | ((X22) = (k1_xboole_0))
% 0.77/0.97          | ~ (v1_relat_1 @ X22))),
% 0.77/0.97      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.77/0.97  thf('202', plain,
% 0.77/0.97      ((((k1_xboole_0) != (k1_xboole_0))
% 0.77/0.97        | ~ (v1_relat_1 @ sk_C_1)
% 0.77/0.97        | ((sk_C_1) = (k1_xboole_0)))),
% 0.77/0.97      inference('sup-', [status(thm)], ['200', '201'])).
% 0.77/0.97  thf('203', plain, ((v1_relat_1 @ sk_C_1)),
% 0.77/0.97      inference('sup-', [status(thm)], ['12', '13'])).
% 0.77/0.97  thf('204', plain,
% 0.77/0.97      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C_1) = (k1_xboole_0)))),
% 0.77/0.97      inference('demod', [status(thm)], ['202', '203'])).
% 0.77/0.97  thf('205', plain, (((sk_C_1) = (k1_xboole_0))),
% 0.77/0.97      inference('simplify', [status(thm)], ['204'])).
% 0.77/0.97  thf('206', plain, (((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))),
% 0.77/0.97      inference('demod', [status(thm)], ['104', '105'])).
% 0.77/0.97  thf('207', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.77/0.97      inference('sup+', [status(thm)], ['43', '46'])).
% 0.77/0.97  thf('208', plain,
% 0.77/0.97      (![X28 : $i]:
% 0.77/0.97         (~ (v2_funct_1 @ X28)
% 0.77/0.97          | ((k2_funct_1 @ X28) = (k4_relat_1 @ X28))
% 0.77/0.97          | ~ (v1_funct_1 @ X28)
% 0.77/0.97          | ~ (v1_relat_1 @ X28))),
% 0.77/0.97      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.77/0.97  thf('209', plain,
% 0.77/0.97      ((~ (v1_funct_1 @ k1_xboole_0)
% 0.77/0.97        | ((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))
% 0.77/0.97        | ~ (v2_funct_1 @ k1_xboole_0))),
% 0.77/0.97      inference('sup-', [status(thm)], ['207', '208'])).
% 0.77/0.97  thf('210', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.77/0.97      inference('sup+', [status(thm)], ['61', '64'])).
% 0.77/0.97  thf('211', plain,
% 0.77/0.97      ((((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))
% 0.77/0.97        | ~ (v2_funct_1 @ k1_xboole_0))),
% 0.77/0.97      inference('demod', [status(thm)], ['209', '210'])).
% 0.77/0.97  thf('212', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.97      inference('demod', [status(thm)], ['29', '30'])).
% 0.77/0.97  thf('213', plain, (![X0 : $i]: (v2_funct_1 @ (k6_partfun1 @ X0))),
% 0.77/0.97      inference('simplify', [status(thm)], ['96'])).
% 0.77/0.97  thf('214', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.77/0.97      inference('sup+', [status(thm)], ['212', '213'])).
% 0.77/0.97  thf('215', plain,
% 0.77/0.97      (((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 0.77/0.97      inference('demod', [status(thm)], ['211', '214'])).
% 0.77/0.97  thf('216', plain, (((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 0.77/0.97      inference('sup+', [status(thm)], ['206', '215'])).
% 0.77/0.97  thf('217', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.77/0.97      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.77/0.97  thf('218', plain, ($false),
% 0.77/0.97      inference('demod', [status(thm)], ['189', '205', '216', '217'])).
% 0.77/0.97  
% 0.77/0.97  % SZS output end Refutation
% 0.77/0.97  
% 0.77/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
