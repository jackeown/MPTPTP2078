%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s7fNW7gGzu

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:40 EST 2020

% Result     : Timeout 57.49s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  122 ( 413 expanded)
%              Number of leaves         :   34 ( 135 expanded)
%              Depth                    :   14
%              Number of atoms          :  848 (4040 expanded)
%              Number of equality atoms :   59 ( 158 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X16: $i] :
      ( ( r1_tarski @ X16 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X16 ) @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
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

thf('15',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('17',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X16: $i] :
      ( ( r1_tarski @ X16 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X16 ) @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('21',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf(rc1_relset_1,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ( v5_relat_1 @ C @ B )
      & ( v4_relat_1 @ C @ A )
      & ( v1_relat_1 @ C )
      & ( v1_xboole_0 @ C )
      & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('29',plain,(
    ! [X31: $i,X32: $i] :
      ( v1_xboole_0 @ ( sk_C @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[rc1_relset_1])).

thf('30',plain,(
    ! [X31: $i,X32: $i] :
      ( v1_xboole_0 @ ( sk_C @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[rc1_relset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_C @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','33'])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25
       != ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50'])).

thf('53',plain,(
    ! [X31: $i,X32: $i] :
      ( v4_relat_1 @ ( sk_C @ X31 @ X32 ) @ X32 ) ),
    inference(cnf,[status(esa)],[rc1_relset_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_C @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('55',plain,(
    ! [X32: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X32 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('56',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v4_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X31: $i,X32: $i] :
      ( v1_relat_1 @ ( sk_C @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[rc1_relset_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_C @ X1 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('60',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('63',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50'])).

thf('65',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('66',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['61','62'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25
       != ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('74',plain,(
    ! [X23: $i] :
      ( zip_tseitin_0 @ X23 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('76',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('78',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('82',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('83',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['72','84'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['14','51','52','63','64','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.s7fNW7gGzu
% 0.16/0.37  % Computer   : n021.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 19:59:50 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 57.49/57.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 57.49/57.68  % Solved by: fo/fo7.sh
% 57.49/57.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 57.49/57.68  % done 38627 iterations in 57.200s
% 57.49/57.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 57.49/57.68  % SZS output start Refutation
% 57.49/57.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 57.49/57.68  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 57.49/57.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 57.49/57.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 57.49/57.68  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 57.49/57.68  thf(sk_A_type, type, sk_A: $i).
% 57.49/57.68  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 57.49/57.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 57.49/57.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 57.49/57.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 57.49/57.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 57.49/57.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 57.49/57.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 57.49/57.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 57.49/57.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 57.49/57.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 57.49/57.68  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 57.49/57.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 57.49/57.68  thf(t3_funct_2, conjecture,
% 57.49/57.68    (![A:$i]:
% 57.49/57.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 57.49/57.68       ( ( v1_funct_1 @ A ) & 
% 57.49/57.68         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 57.49/57.68         ( m1_subset_1 @
% 57.49/57.68           A @ 
% 57.49/57.68           ( k1_zfmisc_1 @
% 57.49/57.68             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 57.49/57.68  thf(zf_stmt_0, negated_conjecture,
% 57.49/57.68    (~( ![A:$i]:
% 57.49/57.68        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 57.49/57.68          ( ( v1_funct_1 @ A ) & 
% 57.49/57.68            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 57.49/57.68            ( m1_subset_1 @
% 57.49/57.68              A @ 
% 57.49/57.68              ( k1_zfmisc_1 @
% 57.49/57.68                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 57.49/57.68    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 57.49/57.68  thf('0', plain,
% 57.49/57.68      ((~ (v1_funct_1 @ sk_A)
% 57.49/57.68        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 57.49/57.68        | ~ (m1_subset_1 @ sk_A @ 
% 57.49/57.68             (k1_zfmisc_1 @ 
% 57.49/57.68              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 57.49/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.49/57.68  thf('1', plain,
% 57.49/57.68      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 57.49/57.68         <= (~
% 57.49/57.68             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 57.49/57.68      inference('split', [status(esa)], ['0'])).
% 57.49/57.68  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 57.49/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.49/57.68  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 57.49/57.68      inference('split', [status(esa)], ['0'])).
% 57.49/57.68  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 57.49/57.68      inference('sup-', [status(thm)], ['2', '3'])).
% 57.49/57.68  thf(t21_relat_1, axiom,
% 57.49/57.68    (![A:$i]:
% 57.49/57.68     ( ( v1_relat_1 @ A ) =>
% 57.49/57.68       ( r1_tarski @
% 57.49/57.68         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 57.49/57.68  thf('5', plain,
% 57.49/57.68      (![X16 : $i]:
% 57.49/57.68         ((r1_tarski @ X16 @ 
% 57.49/57.68           (k2_zfmisc_1 @ (k1_relat_1 @ X16) @ (k2_relat_1 @ X16)))
% 57.49/57.68          | ~ (v1_relat_1 @ X16))),
% 57.49/57.68      inference('cnf', [status(esa)], [t21_relat_1])).
% 57.49/57.68  thf(t3_subset, axiom,
% 57.49/57.68    (![A:$i,B:$i]:
% 57.49/57.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 57.49/57.68  thf('6', plain,
% 57.49/57.68      (![X8 : $i, X10 : $i]:
% 57.49/57.68         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 57.49/57.68      inference('cnf', [status(esa)], [t3_subset])).
% 57.49/57.68  thf('7', plain,
% 57.49/57.68      (![X0 : $i]:
% 57.49/57.68         (~ (v1_relat_1 @ X0)
% 57.49/57.68          | (m1_subset_1 @ X0 @ 
% 57.49/57.68             (k1_zfmisc_1 @ 
% 57.49/57.68              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 57.49/57.68      inference('sup-', [status(thm)], ['5', '6'])).
% 57.49/57.68  thf('8', plain,
% 57.49/57.68      ((~ (m1_subset_1 @ sk_A @ 
% 57.49/57.68           (k1_zfmisc_1 @ 
% 57.49/57.68            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 57.49/57.68         <= (~
% 57.49/57.68             ((m1_subset_1 @ sk_A @ 
% 57.49/57.68               (k1_zfmisc_1 @ 
% 57.49/57.68                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 57.49/57.68      inference('split', [status(esa)], ['0'])).
% 57.49/57.68  thf('9', plain,
% 57.49/57.68      ((~ (v1_relat_1 @ sk_A))
% 57.49/57.68         <= (~
% 57.49/57.68             ((m1_subset_1 @ sk_A @ 
% 57.49/57.68               (k1_zfmisc_1 @ 
% 57.49/57.68                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 57.49/57.68      inference('sup-', [status(thm)], ['7', '8'])).
% 57.49/57.68  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 57.49/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.49/57.68  thf('11', plain,
% 57.49/57.68      (((m1_subset_1 @ sk_A @ 
% 57.49/57.68         (k1_zfmisc_1 @ 
% 57.49/57.68          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 57.49/57.68      inference('demod', [status(thm)], ['9', '10'])).
% 57.49/57.68  thf('12', plain,
% 57.49/57.68      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 57.49/57.68       ~
% 57.49/57.68       ((m1_subset_1 @ sk_A @ 
% 57.49/57.68         (k1_zfmisc_1 @ 
% 57.49/57.68          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 57.49/57.68       ~ ((v1_funct_1 @ sk_A))),
% 57.49/57.68      inference('split', [status(esa)], ['0'])).
% 57.49/57.68  thf('13', plain,
% 57.49/57.68      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 57.49/57.68      inference('sat_resolution*', [status(thm)], ['4', '11', '12'])).
% 57.49/57.68  thf('14', plain,
% 57.49/57.68      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 57.49/57.68      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 57.49/57.68  thf(d1_funct_2, axiom,
% 57.49/57.68    (![A:$i,B:$i,C:$i]:
% 57.49/57.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 57.49/57.68       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 57.49/57.68           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 57.49/57.68             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 57.49/57.68         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 57.49/57.68           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 57.49/57.68             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 57.49/57.68  thf(zf_stmt_1, axiom,
% 57.49/57.68    (![B:$i,A:$i]:
% 57.49/57.68     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 57.49/57.68       ( zip_tseitin_0 @ B @ A ) ))).
% 57.49/57.68  thf('15', plain,
% 57.49/57.68      (![X23 : $i, X24 : $i]:
% 57.49/57.68         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 57.49/57.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 57.49/57.68  thf(t113_zfmisc_1, axiom,
% 57.49/57.68    (![A:$i,B:$i]:
% 57.49/57.68     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 57.49/57.68       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 57.49/57.68  thf('16', plain,
% 57.49/57.68      (![X5 : $i, X6 : $i]:
% 57.49/57.68         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 57.49/57.68      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 57.49/57.68  thf('17', plain,
% 57.49/57.68      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 57.49/57.68      inference('simplify', [status(thm)], ['16'])).
% 57.49/57.68  thf('18', plain,
% 57.49/57.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 57.49/57.68         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 57.49/57.68      inference('sup+', [status(thm)], ['15', '17'])).
% 57.49/57.68  thf('19', plain,
% 57.49/57.68      (![X16 : $i]:
% 57.49/57.68         ((r1_tarski @ X16 @ 
% 57.49/57.68           (k2_zfmisc_1 @ (k1_relat_1 @ X16) @ (k2_relat_1 @ X16)))
% 57.49/57.68          | ~ (v1_relat_1 @ X16))),
% 57.49/57.68      inference('cnf', [status(esa)], [t21_relat_1])).
% 57.49/57.68  thf(l13_xboole_0, axiom,
% 57.49/57.68    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 57.49/57.68  thf('20', plain,
% 57.49/57.68      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 57.49/57.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 57.49/57.68  thf(t4_subset_1, axiom,
% 57.49/57.68    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 57.49/57.68  thf('21', plain,
% 57.49/57.68      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 57.49/57.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 57.49/57.68  thf('22', plain,
% 57.49/57.68      (![X8 : $i, X9 : $i]:
% 57.49/57.68         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 57.49/57.68      inference('cnf', [status(esa)], [t3_subset])).
% 57.49/57.68  thf('23', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 57.49/57.68      inference('sup-', [status(thm)], ['21', '22'])).
% 57.49/57.68  thf(d10_xboole_0, axiom,
% 57.49/57.68    (![A:$i,B:$i]:
% 57.49/57.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 57.49/57.68  thf('24', plain,
% 57.49/57.68      (![X1 : $i, X3 : $i]:
% 57.49/57.68         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 57.49/57.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 57.49/57.68  thf('25', plain,
% 57.49/57.68      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 57.49/57.68      inference('sup-', [status(thm)], ['23', '24'])).
% 57.49/57.68  thf('26', plain,
% 57.49/57.68      (![X0 : $i, X1 : $i]:
% 57.49/57.68         (~ (r1_tarski @ X1 @ X0)
% 57.49/57.68          | ~ (v1_xboole_0 @ X0)
% 57.49/57.68          | ((X1) = (k1_xboole_0)))),
% 57.49/57.68      inference('sup-', [status(thm)], ['20', '25'])).
% 57.49/57.68  thf('27', plain,
% 57.49/57.68      (![X0 : $i]:
% 57.49/57.68         (~ (v1_relat_1 @ X0)
% 57.49/57.68          | ((X0) = (k1_xboole_0))
% 57.49/57.68          | ~ (v1_xboole_0 @ 
% 57.49/57.68               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 57.49/57.68      inference('sup-', [status(thm)], ['19', '26'])).
% 57.49/57.68  thf('28', plain,
% 57.49/57.68      (![X0 : $i, X1 : $i]:
% 57.49/57.68         (~ (v1_xboole_0 @ k1_xboole_0)
% 57.49/57.68          | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 57.49/57.68          | ((X0) = (k1_xboole_0))
% 57.49/57.68          | ~ (v1_relat_1 @ X0))),
% 57.49/57.68      inference('sup-', [status(thm)], ['18', '27'])).
% 57.49/57.68  thf(rc1_relset_1, axiom,
% 57.49/57.68    (![A:$i,B:$i]:
% 57.49/57.68     ( ?[C:$i]:
% 57.49/57.68       ( ( v5_relat_1 @ C @ B ) & ( v4_relat_1 @ C @ A ) & 
% 57.49/57.68         ( v1_relat_1 @ C ) & ( v1_xboole_0 @ C ) & 
% 57.49/57.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 57.49/57.68  thf('29', plain, (![X31 : $i, X32 : $i]: (v1_xboole_0 @ (sk_C @ X31 @ X32))),
% 57.49/57.68      inference('cnf', [status(esa)], [rc1_relset_1])).
% 57.49/57.68  thf('30', plain, (![X31 : $i, X32 : $i]: (v1_xboole_0 @ (sk_C @ X31 @ X32))),
% 57.49/57.68      inference('cnf', [status(esa)], [rc1_relset_1])).
% 57.49/57.68  thf('31', plain,
% 57.49/57.68      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 57.49/57.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 57.49/57.68  thf('32', plain, (![X0 : $i, X1 : $i]: ((sk_C @ X1 @ X0) = (k1_xboole_0))),
% 57.49/57.68      inference('sup-', [status(thm)], ['30', '31'])).
% 57.49/57.68  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 57.49/57.68      inference('demod', [status(thm)], ['29', '32'])).
% 57.49/57.68  thf('34', plain,
% 57.49/57.68      (![X0 : $i, X1 : $i]:
% 57.49/57.68         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 57.49/57.68          | ((X0) = (k1_xboole_0))
% 57.49/57.68          | ~ (v1_relat_1 @ X0))),
% 57.49/57.68      inference('demod', [status(thm)], ['28', '33'])).
% 57.49/57.68  thf('35', plain,
% 57.49/57.68      (![X0 : $i]:
% 57.49/57.68         (~ (v1_relat_1 @ X0)
% 57.49/57.68          | (m1_subset_1 @ X0 @ 
% 57.49/57.68             (k1_zfmisc_1 @ 
% 57.49/57.68              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 57.49/57.68      inference('sup-', [status(thm)], ['5', '6'])).
% 57.49/57.68  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 57.49/57.68  thf(zf_stmt_3, axiom,
% 57.49/57.68    (![C:$i,B:$i,A:$i]:
% 57.49/57.68     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 57.49/57.68       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 57.49/57.68  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 57.49/57.68  thf(zf_stmt_5, axiom,
% 57.49/57.68    (![A:$i,B:$i,C:$i]:
% 57.49/57.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 57.49/57.68       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 57.49/57.68         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 57.49/57.68           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 57.49/57.68             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 57.49/57.68  thf('36', plain,
% 57.49/57.68      (![X28 : $i, X29 : $i, X30 : $i]:
% 57.49/57.68         (~ (zip_tseitin_0 @ X28 @ X29)
% 57.49/57.68          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 57.49/57.68          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 57.49/57.68      inference('cnf', [status(esa)], [zf_stmt_5])).
% 57.49/57.68  thf('37', plain,
% 57.49/57.68      (![X0 : $i]:
% 57.49/57.68         (~ (v1_relat_1 @ X0)
% 57.49/57.68          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 57.49/57.68          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 57.49/57.68      inference('sup-', [status(thm)], ['35', '36'])).
% 57.49/57.68  thf('38', plain,
% 57.49/57.68      (![X0 : $i]:
% 57.49/57.68         (~ (v1_relat_1 @ X0)
% 57.49/57.68          | ((X0) = (k1_xboole_0))
% 57.49/57.68          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 57.49/57.68          | ~ (v1_relat_1 @ X0))),
% 57.49/57.68      inference('sup-', [status(thm)], ['34', '37'])).
% 57.49/57.68  thf('39', plain,
% 57.49/57.68      (![X0 : $i]:
% 57.49/57.68         ((zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 57.49/57.68          | ((X0) = (k1_xboole_0))
% 57.49/57.68          | ~ (v1_relat_1 @ X0))),
% 57.49/57.68      inference('simplify', [status(thm)], ['38'])).
% 57.49/57.68  thf('40', plain,
% 57.49/57.68      (![X0 : $i]:
% 57.49/57.68         (~ (v1_relat_1 @ X0)
% 57.49/57.68          | (m1_subset_1 @ X0 @ 
% 57.49/57.68             (k1_zfmisc_1 @ 
% 57.49/57.68              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 57.49/57.68      inference('sup-', [status(thm)], ['5', '6'])).
% 57.49/57.68  thf(redefinition_k1_relset_1, axiom,
% 57.49/57.68    (![A:$i,B:$i,C:$i]:
% 57.49/57.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 57.49/57.68       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 57.49/57.68  thf('41', plain,
% 57.49/57.68      (![X20 : $i, X21 : $i, X22 : $i]:
% 57.49/57.68         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 57.49/57.68          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 57.49/57.68      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 57.49/57.68  thf('42', plain,
% 57.49/57.68      (![X0 : $i]:
% 57.49/57.68         (~ (v1_relat_1 @ X0)
% 57.49/57.68          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 57.49/57.68              = (k1_relat_1 @ X0)))),
% 57.49/57.68      inference('sup-', [status(thm)], ['40', '41'])).
% 57.49/57.68  thf('43', plain,
% 57.49/57.68      (![X25 : $i, X26 : $i, X27 : $i]:
% 57.49/57.68         (((X25) != (k1_relset_1 @ X25 @ X26 @ X27))
% 57.49/57.68          | (v1_funct_2 @ X27 @ X25 @ X26)
% 57.49/57.68          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 57.49/57.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 57.49/57.68  thf('44', plain,
% 57.49/57.68      (![X0 : $i]:
% 57.49/57.68         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 57.49/57.68          | ~ (v1_relat_1 @ X0)
% 57.49/57.68          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 57.49/57.68          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 57.49/57.68      inference('sup-', [status(thm)], ['42', '43'])).
% 57.49/57.68  thf('45', plain,
% 57.49/57.68      (![X0 : $i]:
% 57.49/57.68         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 57.49/57.68          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 57.49/57.68          | ~ (v1_relat_1 @ X0))),
% 57.49/57.68      inference('simplify', [status(thm)], ['44'])).
% 57.49/57.68  thf('46', plain,
% 57.49/57.68      (![X0 : $i]:
% 57.49/57.68         (~ (v1_relat_1 @ X0)
% 57.49/57.68          | ((X0) = (k1_xboole_0))
% 57.49/57.68          | ~ (v1_relat_1 @ X0)
% 57.49/57.68          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 57.49/57.68      inference('sup-', [status(thm)], ['39', '45'])).
% 57.49/57.68  thf('47', plain,
% 57.49/57.68      (![X0 : $i]:
% 57.49/57.68         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 57.49/57.68          | ((X0) = (k1_xboole_0))
% 57.49/57.68          | ~ (v1_relat_1 @ X0))),
% 57.49/57.68      inference('simplify', [status(thm)], ['46'])).
% 57.49/57.68  thf('48', plain,
% 57.49/57.68      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 57.49/57.68      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 57.49/57.68  thf('49', plain, ((~ (v1_relat_1 @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 57.49/57.68      inference('sup-', [status(thm)], ['47', '48'])).
% 57.49/57.68  thf('50', plain, ((v1_relat_1 @ sk_A)),
% 57.49/57.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.49/57.68  thf('51', plain, (((sk_A) = (k1_xboole_0))),
% 57.49/57.68      inference('demod', [status(thm)], ['49', '50'])).
% 57.49/57.68  thf('52', plain, (((sk_A) = (k1_xboole_0))),
% 57.49/57.68      inference('demod', [status(thm)], ['49', '50'])).
% 57.49/57.68  thf('53', plain,
% 57.49/57.68      (![X31 : $i, X32 : $i]: (v4_relat_1 @ (sk_C @ X31 @ X32) @ X32)),
% 57.49/57.68      inference('cnf', [status(esa)], [rc1_relset_1])).
% 57.49/57.68  thf('54', plain, (![X0 : $i, X1 : $i]: ((sk_C @ X1 @ X0) = (k1_xboole_0))),
% 57.49/57.68      inference('sup-', [status(thm)], ['30', '31'])).
% 57.49/57.68  thf('55', plain, (![X32 : $i]: (v4_relat_1 @ k1_xboole_0 @ X32)),
% 57.49/57.68      inference('demod', [status(thm)], ['53', '54'])).
% 57.49/57.68  thf(d18_relat_1, axiom,
% 57.49/57.68    (![A:$i,B:$i]:
% 57.49/57.68     ( ( v1_relat_1 @ B ) =>
% 57.49/57.68       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 57.49/57.68  thf('56', plain,
% 57.49/57.68      (![X14 : $i, X15 : $i]:
% 57.49/57.68         (~ (v4_relat_1 @ X14 @ X15)
% 57.49/57.68          | (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 57.49/57.68          | ~ (v1_relat_1 @ X14))),
% 57.49/57.68      inference('cnf', [status(esa)], [d18_relat_1])).
% 57.49/57.68  thf('57', plain,
% 57.49/57.68      (![X0 : $i]:
% 57.49/57.68         (~ (v1_relat_1 @ k1_xboole_0)
% 57.49/57.68          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 57.49/57.68      inference('sup-', [status(thm)], ['55', '56'])).
% 57.49/57.68  thf('58', plain, (![X31 : $i, X32 : $i]: (v1_relat_1 @ (sk_C @ X31 @ X32))),
% 57.49/57.68      inference('cnf', [status(esa)], [rc1_relset_1])).
% 57.49/57.68  thf('59', plain, (![X0 : $i, X1 : $i]: ((sk_C @ X1 @ X0) = (k1_xboole_0))),
% 57.49/57.68      inference('sup-', [status(thm)], ['30', '31'])).
% 57.49/57.68  thf('60', plain, ((v1_relat_1 @ k1_xboole_0)),
% 57.49/57.68      inference('demod', [status(thm)], ['58', '59'])).
% 57.49/57.68  thf('61', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 57.49/57.68      inference('demod', [status(thm)], ['57', '60'])).
% 57.49/57.68  thf('62', plain,
% 57.49/57.68      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 57.49/57.68      inference('sup-', [status(thm)], ['23', '24'])).
% 57.49/57.68  thf('63', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 57.49/57.68      inference('sup-', [status(thm)], ['61', '62'])).
% 57.49/57.68  thf('64', plain, (((sk_A) = (k1_xboole_0))),
% 57.49/57.68      inference('demod', [status(thm)], ['49', '50'])).
% 57.49/57.68  thf('65', plain,
% 57.49/57.68      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 57.49/57.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 57.49/57.68  thf('66', plain,
% 57.49/57.68      (![X20 : $i, X21 : $i, X22 : $i]:
% 57.49/57.68         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 57.49/57.68          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 57.49/57.68      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 57.49/57.68  thf('67', plain,
% 57.49/57.68      (![X0 : $i, X1 : $i]:
% 57.49/57.68         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 57.49/57.68      inference('sup-', [status(thm)], ['65', '66'])).
% 57.49/57.68  thf('68', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 57.49/57.68      inference('sup-', [status(thm)], ['61', '62'])).
% 57.49/57.68  thf('69', plain,
% 57.49/57.68      (![X0 : $i, X1 : $i]:
% 57.49/57.68         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 57.49/57.68      inference('demod', [status(thm)], ['67', '68'])).
% 57.49/57.68  thf('70', plain,
% 57.49/57.68      (![X25 : $i, X26 : $i, X27 : $i]:
% 57.49/57.68         (((X25) != (k1_relset_1 @ X25 @ X26 @ X27))
% 57.49/57.68          | (v1_funct_2 @ X27 @ X25 @ X26)
% 57.49/57.68          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 57.49/57.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 57.49/57.68  thf('71', plain,
% 57.49/57.68      (![X0 : $i, X1 : $i]:
% 57.49/57.68         (((X1) != (k1_xboole_0))
% 57.49/57.68          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 57.49/57.68          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 57.49/57.68      inference('sup-', [status(thm)], ['69', '70'])).
% 57.49/57.68  thf('72', plain,
% 57.49/57.68      (![X0 : $i]:
% 57.49/57.68         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 57.49/57.68          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 57.49/57.68      inference('simplify', [status(thm)], ['71'])).
% 57.49/57.68  thf('73', plain,
% 57.49/57.68      (![X23 : $i, X24 : $i]:
% 57.49/57.68         ((zip_tseitin_0 @ X23 @ X24) | ((X24) != (k1_xboole_0)))),
% 57.49/57.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 57.49/57.68  thf('74', plain, (![X23 : $i]: (zip_tseitin_0 @ X23 @ k1_xboole_0)),
% 57.49/57.68      inference('simplify', [status(thm)], ['73'])).
% 57.49/57.68  thf('75', plain,
% 57.49/57.68      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 57.49/57.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 57.49/57.68  thf('76', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 57.49/57.68      inference('simplify', [status(thm)], ['75'])).
% 57.49/57.68  thf('77', plain,
% 57.49/57.68      (![X8 : $i, X10 : $i]:
% 57.49/57.68         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 57.49/57.68      inference('cnf', [status(esa)], [t3_subset])).
% 57.49/57.68  thf('78', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 57.49/57.68      inference('sup-', [status(thm)], ['76', '77'])).
% 57.49/57.68  thf('79', plain,
% 57.49/57.68      (![X28 : $i, X29 : $i, X30 : $i]:
% 57.49/57.68         (~ (zip_tseitin_0 @ X28 @ X29)
% 57.49/57.68          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 57.49/57.68          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 57.49/57.68      inference('cnf', [status(esa)], [zf_stmt_5])).
% 57.49/57.68  thf('80', plain,
% 57.49/57.68      (![X0 : $i, X1 : $i]:
% 57.49/57.68         ((zip_tseitin_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X0 @ X1)
% 57.49/57.68          | ~ (zip_tseitin_0 @ X0 @ X1))),
% 57.49/57.68      inference('sup-', [status(thm)], ['78', '79'])).
% 57.49/57.68  thf('81', plain,
% 57.49/57.68      (![X0 : $i]:
% 57.49/57.68         (zip_tseitin_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0) @ X0 @ k1_xboole_0)),
% 57.49/57.68      inference('sup-', [status(thm)], ['74', '80'])).
% 57.49/57.68  thf('82', plain,
% 57.49/57.68      (![X5 : $i, X6 : $i]:
% 57.49/57.68         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 57.49/57.68      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 57.49/57.68  thf('83', plain,
% 57.49/57.68      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 57.49/57.68      inference('simplify', [status(thm)], ['82'])).
% 57.49/57.68  thf('84', plain,
% 57.49/57.68      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 57.49/57.68      inference('demod', [status(thm)], ['81', '83'])).
% 57.49/57.68  thf('85', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 57.49/57.68      inference('demod', [status(thm)], ['72', '84'])).
% 57.49/57.68  thf('86', plain, ($false),
% 57.49/57.68      inference('demod', [status(thm)], ['14', '51', '52', '63', '64', '85'])).
% 57.49/57.68  
% 57.49/57.68  % SZS output end Refutation
% 57.49/57.68  
% 57.49/57.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
