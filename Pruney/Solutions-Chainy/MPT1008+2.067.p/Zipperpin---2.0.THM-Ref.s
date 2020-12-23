%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RFhYMCI03U

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:40 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 124 expanded)
%              Number of leaves         :   43 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :  700 (1292 expanded)
%              Number of equality atoms :   80 ( 121 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t62_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
            = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_2])).

thf('0',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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

thf('5',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('16',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12
        = ( k7_relat_1 @ X12 @ X13 ) )
      | ~ ( v4_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('21',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf(t167_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X15 @ ( k1_tarski @ X16 ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t167_funct_1])).

thf('24',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('28',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('29',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( X4
        = ( k2_tarski @ X2 @ X3 ) )
      | ( X4
        = ( k1_tarski @ X3 ) )
      | ( X4
        = ( k1_tarski @ X2 ) )
      | ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ ( k2_tarski @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( k2_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('34',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('39',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['35','40'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('42',plain,(
    ! [X14: $i] :
      ( ( ( k2_relat_1 @ X14 )
       != k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf('45',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['45'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('47',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('48',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['13','46','47'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('50',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X6 ) @ X7 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RFhYMCI03U
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:52:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.70  % Solved by: fo/fo7.sh
% 0.46/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.70  % done 305 iterations in 0.241s
% 0.46/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.70  % SZS output start Refutation
% 0.46/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.70  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.46/0.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.70  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.46/0.70  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.46/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.70  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.46/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.70  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.70  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.46/0.70  thf(t62_funct_2, conjecture,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.46/0.70         ( m1_subset_1 @
% 0.46/0.70           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.46/0.70       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.46/0.70         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.46/0.70           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.46/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.70    (~( ![A:$i,B:$i,C:$i]:
% 0.46/0.70        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.46/0.70            ( m1_subset_1 @
% 0.46/0.70              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.46/0.70          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.46/0.70            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.46/0.70              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.46/0.70    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.46/0.70  thf('0', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(d1_funct_2, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.70           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.46/0.70             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.70         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.70           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.46/0.70             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.46/0.70  thf(zf_stmt_1, axiom,
% 0.46/0.70    (![C:$i,B:$i,A:$i]:
% 0.46/0.70     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.46/0.70       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.46/0.70  thf('1', plain,
% 0.46/0.70      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.46/0.70         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.46/0.70          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 0.46/0.70          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.70  thf('2', plain,
% 0.46/0.70      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.70        | ((k1_tarski @ sk_A)
% 0.46/0.70            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.70  thf(zf_stmt_2, axiom,
% 0.46/0.70    (![B:$i,A:$i]:
% 0.46/0.70     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.70       ( zip_tseitin_0 @ B @ A ) ))).
% 0.46/0.70  thf('3', plain,
% 0.46/0.70      (![X29 : $i, X30 : $i]:
% 0.46/0.70         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.46/0.70  thf('4', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.70  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.46/0.70  thf(zf_stmt_5, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.46/0.70         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.70           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.70             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.46/0.70  thf('5', plain,
% 0.46/0.70      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.46/0.70         (~ (zip_tseitin_0 @ X34 @ X35)
% 0.46/0.70          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 0.46/0.70          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.70  thf('6', plain,
% 0.46/0.70      (((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.46/0.70        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['4', '5'])).
% 0.46/0.70  thf('7', plain,
% 0.46/0.70      ((((sk_B) = (k1_xboole_0))
% 0.46/0.70        | (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['3', '6'])).
% 0.46/0.70  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('9', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))),
% 0.46/0.70      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.46/0.70  thf('10', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.70  thf('11', plain,
% 0.46/0.70      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.46/0.70         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.46/0.70          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.70  thf('12', plain,
% 0.46/0.70      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.70  thf('13', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.46/0.70      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.46/0.70  thf('14', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(cc2_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.70  thf('15', plain,
% 0.46/0.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.70         ((v4_relat_1 @ X20 @ X21)
% 0.46/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.70  thf('16', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.46/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.70  thf(t209_relat_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.46/0.70       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.46/0.70  thf('17', plain,
% 0.46/0.70      (![X12 : $i, X13 : $i]:
% 0.46/0.70         (((X12) = (k7_relat_1 @ X12 @ X13))
% 0.46/0.70          | ~ (v4_relat_1 @ X12 @ X13)
% 0.46/0.70          | ~ (v1_relat_1 @ X12))),
% 0.46/0.70      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.46/0.70  thf('18', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.70  thf('19', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(cc1_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( v1_relat_1 @ C ) ))).
% 0.46/0.70  thf('20', plain,
% 0.46/0.70      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.70         ((v1_relat_1 @ X17)
% 0.46/0.70          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.70  thf('21', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.70  thf('22', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.46/0.70      inference('demod', [status(thm)], ['18', '21'])).
% 0.46/0.70  thf(t167_funct_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.70       ( r1_tarski @
% 0.46/0.70         ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ 
% 0.46/0.70         ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ))).
% 0.46/0.70  thf('23', plain,
% 0.46/0.70      (![X15 : $i, X16 : $i]:
% 0.46/0.70         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X15 @ (k1_tarski @ X16))) @ 
% 0.46/0.70           (k1_tarski @ (k1_funct_1 @ X15 @ X16)))
% 0.46/0.70          | ~ (v1_funct_1 @ X15)
% 0.46/0.70          | ~ (v1_relat_1 @ X15))),
% 0.46/0.70      inference('cnf', [status(esa)], [t167_funct_1])).
% 0.46/0.70  thf('24', plain,
% 0.46/0.70      (((r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.46/0.70         (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.46/0.70        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | ~ (v1_funct_1 @ sk_C))),
% 0.46/0.70      inference('sup+', [status(thm)], ['22', '23'])).
% 0.46/0.70  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.70  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('27', plain,
% 0.46/0.70      ((r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.46/0.70        (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.46/0.70      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.46/0.70  thf(t69_enumset1, axiom,
% 0.46/0.70    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.46/0.70  thf('28', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.46/0.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.70  thf(l45_zfmisc_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.46/0.70       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.46/0.70            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.46/0.70  thf('29', plain,
% 0.46/0.70      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.70         (((X4) = (k2_tarski @ X2 @ X3))
% 0.46/0.70          | ((X4) = (k1_tarski @ X3))
% 0.46/0.70          | ((X4) = (k1_tarski @ X2))
% 0.46/0.70          | ((X4) = (k1_xboole_0))
% 0.46/0.70          | ~ (r1_tarski @ X4 @ (k2_tarski @ X2 @ X3)))),
% 0.46/0.70      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.46/0.70  thf('30', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.46/0.70          | ((X1) = (k1_xboole_0))
% 0.46/0.70          | ((X1) = (k1_tarski @ X0))
% 0.46/0.70          | ((X1) = (k1_tarski @ X0))
% 0.46/0.70          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.70  thf('31', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (((X1) = (k2_tarski @ X0 @ X0))
% 0.46/0.70          | ((X1) = (k1_tarski @ X0))
% 0.46/0.70          | ((X1) = (k1_xboole_0))
% 0.46/0.70          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.46/0.70      inference('simplify', [status(thm)], ['30'])).
% 0.46/0.70  thf('32', plain,
% 0.46/0.70      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 0.46/0.70        | ((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.46/0.70        | ((k2_relat_1 @ sk_C)
% 0.46/0.70            = (k2_tarski @ (k1_funct_1 @ sk_C @ sk_A) @ 
% 0.46/0.70               (k1_funct_1 @ sk_C @ sk_A))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['27', '31'])).
% 0.46/0.70  thf('33', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.46/0.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.46/0.70  thf('34', plain,
% 0.46/0.70      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 0.46/0.70        | ((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.46/0.70        | ((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A))))),
% 0.46/0.70      inference('demod', [status(thm)], ['32', '33'])).
% 0.46/0.70  thf('35', plain,
% 0.46/0.70      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 0.46/0.70        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.46/0.70      inference('simplify', [status(thm)], ['34'])).
% 0.46/0.70  thf('36', plain,
% 0.46/0.70      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 0.46/0.70         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('37', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_C @ 
% 0.46/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.70  thf('38', plain,
% 0.46/0.70      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.70         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 0.46/0.70          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.70  thf('39', plain,
% 0.46/0.70      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.46/0.70      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.70  thf('40', plain,
% 0.46/0.70      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.46/0.70      inference('demod', [status(thm)], ['36', '39'])).
% 0.46/0.70  thf('41', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.46/0.70      inference('simplify_reflect-', [status(thm)], ['35', '40'])).
% 0.46/0.70  thf(t64_relat_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ A ) =>
% 0.46/0.70       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.70           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.70         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.46/0.70  thf('42', plain,
% 0.46/0.70      (![X14 : $i]:
% 0.46/0.70         (((k2_relat_1 @ X14) != (k1_xboole_0))
% 0.46/0.70          | ((X14) = (k1_xboole_0))
% 0.46/0.70          | ~ (v1_relat_1 @ X14))),
% 0.46/0.70      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.46/0.70  thf('43', plain,
% 0.46/0.70      ((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.70        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.70        | ((sk_C) = (k1_xboole_0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.70  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.70      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.70  thf('45', plain,
% 0.46/0.70      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 0.46/0.70      inference('demod', [status(thm)], ['43', '44'])).
% 0.46/0.70  thf('46', plain, (((sk_C) = (k1_xboole_0))),
% 0.46/0.70      inference('simplify', [status(thm)], ['45'])).
% 0.46/0.70  thf(t60_relat_1, axiom,
% 0.46/0.70    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.46/0.70     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.46/0.70  thf('47', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.46/0.70  thf('48', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.46/0.70      inference('demod', [status(thm)], ['13', '46', '47'])).
% 0.46/0.70  thf(t1_boole, axiom,
% 0.46/0.70    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.70  thf('49', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t1_boole])).
% 0.46/0.70  thf(t49_zfmisc_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.46/0.70  thf('50', plain,
% 0.46/0.70      (![X6 : $i, X7 : $i]:
% 0.46/0.70         ((k2_xboole_0 @ (k1_tarski @ X6) @ X7) != (k1_xboole_0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.46/0.70  thf('51', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['49', '50'])).
% 0.46/0.70  thf('52', plain, ($false),
% 0.46/0.70      inference('simplify_reflect-', [status(thm)], ['48', '51'])).
% 0.46/0.70  
% 0.46/0.70  % SZS output end Refutation
% 0.46/0.70  
% 0.46/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
