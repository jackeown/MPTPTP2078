%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iQiBodmatU

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 404 expanded)
%              Number of leaves         :   33 ( 127 expanded)
%              Depth                    :   19
%              Number of atoms          :  896 (5372 expanded)
%              Number of equality atoms :   60 ( 285 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t9_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ B @ C )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ B @ C )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_funct_2])).

thf('0',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
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

thf('1',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('5',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('9',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X9 @ X7 ) @ ( k2_zfmisc_1 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('17',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('18',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X7 @ X9 ) @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ X1 ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,
    ( ( r1_tarski @ sk_D @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_D @ X0 )
        | ~ ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_D @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('29',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ sk_D @ X1 )
        | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ X1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_D @ ( k2_zfmisc_1 @ X0 @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','29'])).

thf('31',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('33',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X21 ) ) )
      | ( v1_partfun1 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( v1_partfun1 @ sk_D @ X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('45',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_partfun1 @ X16 @ X17 )
      | ( v1_funct_2 @ X16 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('46',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_partfun1 @ sk_D @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['49'])).

thf('53',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('55',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['49'])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['49'])).

thf('58',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['53','56','57'])).

thf('59',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['50','58'])).

thf('60',plain,(
    ~ ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(clc,[status(thm)],['48','59'])).

thf('61',plain,
    ( ~ ( v1_partfun1 @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','60'])).

thf('62',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','61'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('63',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('64',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('66',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['64','65'])).

thf('67',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['13','66'])).

thf('68',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['11','67'])).

thf('69',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['6','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('71',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('72',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24
       != ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('74',plain,
    ( ( sk_A
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['50','58'])).

thf('76',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( sk_A
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('78',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('79',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('81',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X1 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('88',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['13','66'])).

thf('92',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['90','91'])).

thf('93',plain,(
    zip_tseitin_1 @ sk_D @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['79','92'])).

thf('94',plain,(
    sk_A
 != ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['76','93'])).

thf('95',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['69','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iQiBodmatU
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 213 iterations in 0.113s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.57  thf(t9_funct_2, conjecture,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.57       ( ( r1_tarski @ B @ C ) =>
% 0.21/0.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.21/0.57           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.21/0.57             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.57            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.57          ( ( r1_tarski @ B @ C ) =>
% 0.21/0.57            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.21/0.57              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.21/0.57                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 0.21/0.57  thf('0', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(d1_funct_2, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.57           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.57             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.57           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.57             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_1, axiom,
% 0.21/0.57    (![C:$i,B:$i,A:$i]:
% 0.21/0.57     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.57       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.57         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.21/0.57          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 0.21/0.57          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.21/0.57        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.57         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 0.21/0.57          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.57  thf('5', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.21/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.21/0.57      inference('demod', [status(thm)], ['2', '5'])).
% 0.21/0.57  thf(zf_stmt_2, axiom,
% 0.21/0.57    (![B:$i,A:$i]:
% 0.21/0.57     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.57       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      (![X22 : $i, X23 : $i]:
% 0.21/0.57         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.57  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.57  thf(zf_stmt_5, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.57           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.57             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.57         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.21/0.57          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.21/0.57          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['7', '10'])).
% 0.21/0.57  thf('12', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.21/0.57      inference('split', [status(esa)], ['12'])).
% 0.21/0.57  thf('14', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t118_zfmisc_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.57       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.21/0.57         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.57         (~ (r1_tarski @ X7 @ X8)
% 0.21/0.57          | (r1_tarski @ (k2_zfmisc_1 @ X9 @ X7) @ (k2_zfmisc_1 @ X9 @ X8)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.57  thf('17', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.21/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.57         (~ (r1_tarski @ X7 @ X8)
% 0.21/0.57          | (r1_tarski @ (k2_zfmisc_1 @ X7 @ X9) @ (k2_zfmisc_1 @ X8 @ X9)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (r1_tarski @ (k2_zfmisc_1 @ k1_xboole_0 @ X1) @ 
% 0.21/0.57          (k2_zfmisc_1 @ X0 @ X1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.57      inference('split', [status(esa)], ['12'])).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_D @ 
% 0.21/0.57         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.21/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.57      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.57  thf(t3_subset, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i]:
% 0.21/0.57         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      (((r1_tarski @ sk_D @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B)))
% 0.21/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.57  thf(t1_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.57       ( r1_tarski @ A @ C ) ))).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.57         (~ (r1_tarski @ X3 @ X4)
% 0.21/0.57          | ~ (r1_tarski @ X4 @ X5)
% 0.21/0.57          | (r1_tarski @ X3 @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.57  thf('26', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          ((r1_tarski @ sk_D @ X0)
% 0.21/0.57           | ~ (r1_tarski @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B) @ X0)))
% 0.21/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      ((![X0 : $i]: (r1_tarski @ sk_D @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.21/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['19', '26'])).
% 0.21/0.57  thf('28', plain,
% 0.21/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.57         (~ (r1_tarski @ X3 @ X4)
% 0.21/0.57          | ~ (r1_tarski @ X4 @ X5)
% 0.21/0.57          | (r1_tarski @ X3 @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      ((![X0 : $i, X1 : $i]:
% 0.21/0.57          ((r1_tarski @ sk_D @ X1)
% 0.21/0.57           | ~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ X1)))
% 0.21/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.57  thf('30', plain,
% 0.21/0.57      ((![X0 : $i]: (r1_tarski @ sk_D @ (k2_zfmisc_1 @ X0 @ sk_C)))
% 0.21/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['16', '29'])).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      (![X10 : $i, X12 : $i]:
% 0.21/0.57         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C))))
% 0.21/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.57  thf(cc1_partfun1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.57       ( ![C:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.21/0.57  thf('33', plain,
% 0.21/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.57         (~ (v1_xboole_0 @ X19)
% 0.21/0.57          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X21)))
% 0.21/0.57          | (v1_partfun1 @ X20 @ X19))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      ((![X0 : $i]: ((v1_partfun1 @ sk_D @ X0) | ~ (v1_xboole_0 @ X0)))
% 0.21/0.57         <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.57      inference('split', [status(esa)], ['12'])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.57  thf('37', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i]:
% 0.21/0.57         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.57  thf('39', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.57  thf('40', plain,
% 0.21/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.57         (~ (r1_tarski @ X3 @ X4)
% 0.21/0.57          | ~ (r1_tarski @ X4 @ X5)
% 0.21/0.57          | (r1_tarski @ X3 @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.57  thf('41', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((r1_tarski @ sk_D @ X0)
% 0.21/0.57          | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.57  thf('42', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['36', '41'])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      (![X10 : $i, X12 : $i]:
% 0.21/0.57         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.57  thf('44', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.57  thf(cc1_funct_2, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.21/0.57         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.21/0.57  thf('45', plain,
% 0.21/0.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.57         (~ (v1_funct_1 @ X16)
% 0.21/0.57          | ~ (v1_partfun1 @ X16 @ X17)
% 0.21/0.57          | (v1_funct_2 @ X16 @ X17 @ X18)
% 0.21/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.21/0.57  thf('46', plain,
% 0.21/0.57      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.21/0.57        | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.21/0.57        | ~ (v1_funct_1 @ sk_D))),
% 0.21/0.57      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.57  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('48', plain,
% 0.21/0.57      (((v1_funct_2 @ sk_D @ sk_A @ sk_C) | ~ (v1_partfun1 @ sk_D @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.57  thf('49', plain,
% 0.21/0.57      ((~ (v1_funct_1 @ sk_D)
% 0.21/0.57        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.21/0.57        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('50', plain,
% 0.21/0.57      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.21/0.57         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.21/0.57      inference('split', [status(esa)], ['49'])).
% 0.21/0.57  thf('51', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('52', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.21/0.57      inference('split', [status(esa)], ['49'])).
% 0.21/0.57  thf('53', plain, (((v1_funct_1 @ sk_D))),
% 0.21/0.57      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.57  thf('54', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.57  thf('55', plain,
% 0.21/0.57      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.21/0.57         <= (~
% 0.21/0.57             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.21/0.57      inference('split', [status(esa)], ['49'])).
% 0.21/0.57  thf('56', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.57  thf('57', plain,
% 0.21/0.57      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 0.21/0.57       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.21/0.57       ~ ((v1_funct_1 @ sk_D))),
% 0.21/0.57      inference('split', [status(esa)], ['49'])).
% 0.21/0.57  thf('58', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)], ['53', '56', '57'])).
% 0.21/0.57  thf('59', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['50', '58'])).
% 0.21/0.57  thf('60', plain, (~ (v1_partfun1 @ sk_D @ sk_A)),
% 0.21/0.57      inference('clc', [status(thm)], ['48', '59'])).
% 0.21/0.57  thf('61', plain,
% 0.21/0.57      ((~ (v1_partfun1 @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['35', '60'])).
% 0.21/0.57  thf('62', plain,
% 0.21/0.57      ((~ (v1_xboole_0 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['34', '61'])).
% 0.21/0.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.57  thf('63', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.57  thf('64', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['62', '63'])).
% 0.21/0.57  thf('65', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.21/0.57      inference('split', [status(esa)], ['12'])).
% 0.21/0.57  thf('66', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.21/0.57      inference('sat_resolution*', [status(thm)], ['64', '65'])).
% 0.21/0.57  thf('67', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['13', '66'])).
% 0.21/0.57  thf('68', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['11', '67'])).
% 0.21/0.57  thf('69', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.21/0.57      inference('demod', [status(thm)], ['6', '68'])).
% 0.21/0.57  thf('70', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.57  thf('71', plain,
% 0.21/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.57         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 0.21/0.57          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.57  thf('72', plain,
% 0.21/0.57      (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.21/0.57      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.57  thf('73', plain,
% 0.21/0.57      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.57         (((X24) != (k1_relset_1 @ X24 @ X25 @ X26))
% 0.21/0.57          | (v1_funct_2 @ X26 @ X24 @ X25)
% 0.21/0.57          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.57  thf('74', plain,
% 0.21/0.57      ((((sk_A) != (k1_relat_1 @ sk_D))
% 0.21/0.57        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 0.21/0.57        | (v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.57  thf('75', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['50', '58'])).
% 0.21/0.57  thf('76', plain,
% 0.21/0.57      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 0.21/0.57        | ((sk_A) != (k1_relat_1 @ sk_D)))),
% 0.21/0.57      inference('clc', [status(thm)], ['74', '75'])).
% 0.21/0.57  thf('77', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.57  thf('78', plain,
% 0.21/0.57      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.57         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.21/0.57          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.21/0.57          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.57  thf('79', plain,
% 0.21/0.57      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['77', '78'])).
% 0.21/0.57  thf('80', plain,
% 0.21/0.57      (![X22 : $i, X23 : $i]:
% 0.21/0.57         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.57  thf('81', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.21/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.57  thf('82', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.21/0.57      inference('sup+', [status(thm)], ['80', '81'])).
% 0.21/0.57  thf('83', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('84', plain,
% 0.21/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.57         (~ (r1_tarski @ X3 @ X4)
% 0.21/0.57          | ~ (r1_tarski @ X4 @ X5)
% 0.21/0.57          | (r1_tarski @ X3 @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.57  thf('85', plain,
% 0.21/0.57      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ sk_C @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['83', '84'])).
% 0.21/0.57  thf('86', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((zip_tseitin_0 @ sk_C @ X1) | (r1_tarski @ sk_B @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['82', '85'])).
% 0.21/0.57  thf('87', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.21/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.57  thf(d10_xboole_0, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.57  thf('88', plain,
% 0.21/0.57      (![X0 : $i, X2 : $i]:
% 0.21/0.57         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.57  thf('89', plain,
% 0.21/0.57      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['87', '88'])).
% 0.21/0.57  thf('90', plain,
% 0.21/0.57      (![X0 : $i]: ((zip_tseitin_0 @ sk_C @ X0) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['86', '89'])).
% 0.21/0.57  thf('91', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.57      inference('simpl_trail', [status(thm)], ['13', '66'])).
% 0.21/0.57  thf('92', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['90', '91'])).
% 0.21/0.57  thf('93', plain, ((zip_tseitin_1 @ sk_D @ sk_C @ sk_A)),
% 0.21/0.57      inference('demod', [status(thm)], ['79', '92'])).
% 0.21/0.57  thf('94', plain, (((sk_A) != (k1_relat_1 @ sk_D))),
% 0.21/0.57      inference('demod', [status(thm)], ['76', '93'])).
% 0.21/0.57  thf('95', plain, ($false),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['69', '94'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
