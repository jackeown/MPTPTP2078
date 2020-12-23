%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.soKmwPR0pt

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:39 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 761 expanded)
%              Number of leaves         :   45 ( 239 expanded)
%              Depth                    :   24
%              Number of atoms          : 1004 (7395 expanded)
%              Number of equality atoms :   62 ( 332 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $o )).

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
    ! [X3: $i] :
      ( ( r1_tarski @ X3 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X3 ) @ ( k2_relat_1 @ X3 ) ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
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
     => ( zip_tseitin_4 @ B @ A ) ) )).

thf('15',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_4 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(zf_stmt_2,type,(
    zip_tseitin_5: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_5 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_4: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_4 @ B @ A )
         => ( zip_tseitin_5 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_4 @ X30 @ X31 )
      | ( zip_tseitin_5 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_5 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_4 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_5 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X27
       != ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ~ ( zip_tseitin_5 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_5 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_5 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','31'])).

thf('33',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('34',plain,(
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
       != k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf(t18_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_relat_1 @ C ) )
           => ~ ( ( r1_tarski @ ( k2_relat_1 @ C ) @ A )
                & ( B
                  = ( k1_relat_1 @ C ) ) ) )
        & ~ ( ( B != k1_xboole_0 )
            & ( A = k1_xboole_0 ) ) ) )).

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( ( zip_tseitin_0 @ C )
       => ~ ( zip_tseitin_1 @ C @ B @ A ) )
     => ( zip_tseitin_2 @ C @ B @ A ) ) )).

thf('40',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_2 @ X9 @ X10 @ X11 )
      | ( zip_tseitin_1 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('41',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_2 @ X9 @ X10 @ X11 )
      | ( zip_tseitin_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf(zf_stmt_7,type,(
    zip_tseitin_3: $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [B: $i,A: $i] :
      ( ( zip_tseitin_3 @ B @ A )
     => ( ( A = k1_xboole_0 )
        & ( B != k1_xboole_0 ) ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_10,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_11,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( B
          = ( k1_relat_1 @ C ) )
        & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) )).

thf(zf_stmt_12,type,(
    zip_tseitin_0: $i > $o )).

thf(zf_stmt_13,axiom,(
    ! [C: $i] :
      ( ( zip_tseitin_0 @ C )
     => ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) ) ) )).

thf(zf_stmt_14,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( zip_tseitin_3 @ B @ A )
        & ! [C: $i] :
            ( zip_tseitin_2 @ C @ B @ A ) ) )).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_3 @ X14 @ X15 )
      | ~ ( zip_tseitin_2 @ ( sk_C @ X14 @ X15 ) @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_14])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_C @ X1 @ X0 ) )
      | ( zip_tseitin_3 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( zip_tseitin_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('45',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_2 @ X9 @ X10 @ X11 )
      | ( zip_tseitin_1 @ X9 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('46',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_3 @ X14 @ X15 )
      | ~ ( zip_tseitin_2 @ ( sk_C @ X14 @ X15 ) @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_14])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ ( sk_C @ X1 @ X0 ) @ X1 @ X0 )
      | ( zip_tseitin_3 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X7
        = ( k1_relat_1 @ X6 ) )
      | ~ ( zip_tseitin_1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ X1 @ X0 )
      | ( X1
        = ( k1_relat_1 @ ( sk_C @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
       != k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( zip_tseitin_3 @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( sk_C @ X0 @ X1 ) )
      | ( ( sk_C @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X1: $i] :
      ( ( ( sk_C @ k1_xboole_0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C @ k1_xboole_0 @ X1 ) )
      | ( zip_tseitin_3 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X13 != k1_xboole_0 )
      | ~ ( zip_tseitin_3 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('54',plain,(
    ! [X12: $i] :
      ~ ( zip_tseitin_3 @ k1_xboole_0 @ X12 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ ( sk_C @ k1_xboole_0 @ X1 ) )
      | ( ( sk_C @ k1_xboole_0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['52','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ k1_xboole_0 @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','56'])).

thf('58',plain,(
    ! [X12: $i] :
      ~ ( zip_tseitin_3 @ k1_xboole_0 @ X12 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( sk_C @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X14: $i,X15: $i] :
      ( ( zip_tseitin_3 @ X14 @ X15 )
      | ~ ( zip_tseitin_2 @ ( sk_C @ X14 @ X15 ) @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_14])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( zip_tseitin_3 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X12: $i] :
      ~ ( zip_tseitin_3 @ k1_xboole_0 @ X12 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('63',plain,(
    ! [X0: $i] :
      ~ ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['40','63'])).

thf('65',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X7
        = ( k1_relat_1 @ X6 ) )
      | ~ ( zip_tseitin_1 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_11])).

thf('66',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','38','39','66'])).

thf('68',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( zip_tseitin_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('69',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ X5 )
      | ~ ( zip_tseitin_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('70',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('72',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_partfun1 @ X19 @ X20 )
      | ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( zip_tseitin_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('76',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('78',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X24 ) ) )
      | ( v1_partfun1 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_partfun1 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('82',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('83',plain,
    ( ( v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ~ ( zip_tseitin_0 @ k1_xboole_0 )
    | ( v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','83'])).

thf('85',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_2 @ X9 @ X10 @ X11 )
      | ( zip_tseitin_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('86',plain,(
    ! [X0: $i] :
      ~ ( zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('87',plain,(
    zip_tseitin_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['84','87'])).

thf('89',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('90',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','88','89'])).

thf('91',plain,
    ( ~ ( zip_tseitin_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','90'])).

thf('92',plain,(
    zip_tseitin_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['85','86'])).

thf('93',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( zip_tseitin_0 @ k1_xboole_0 )
    | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','93'])).

thf('95',plain,(
    zip_tseitin_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['85','86'])).

thf('96',plain,(
    v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['29','30'])).

thf('98',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('99',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['96','99'])).

thf('101',plain,(
    $false ),
    inference(demod,[status(thm)],['67','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.soKmwPR0pt
% 0.15/0.38  % Computer   : n017.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 16:35:32 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 192 iterations in 0.183s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.67  thf(zip_tseitin_4_type, type, zip_tseitin_4: $i > $i > $o).
% 0.45/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.67  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.45/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.67  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.45/0.67  thf(zip_tseitin_5_type, type, zip_tseitin_5: $i > $i > $i > $o).
% 0.45/0.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.67  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $o).
% 0.45/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $o).
% 0.45/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.67  thf(t3_funct_2, conjecture,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.67       ( ( v1_funct_1 @ A ) & 
% 0.45/0.67         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.45/0.67         ( m1_subset_1 @
% 0.45/0.67           A @ 
% 0.45/0.67           ( k1_zfmisc_1 @
% 0.45/0.67             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i]:
% 0.45/0.67        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.67          ( ( v1_funct_1 @ A ) & 
% 0.45/0.67            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.45/0.67            ( m1_subset_1 @
% 0.45/0.67              A @ 
% 0.45/0.67              ( k1_zfmisc_1 @
% 0.45/0.67                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.45/0.67  thf('0', plain,
% 0.45/0.67      ((~ (v1_funct_1 @ sk_A)
% 0.45/0.67        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.45/0.67        | ~ (m1_subset_1 @ sk_A @ 
% 0.45/0.67             (k1_zfmisc_1 @ 
% 0.45/0.67              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('1', plain,
% 0.45/0.67      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.45/0.67         <= (~
% 0.45/0.67             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.45/0.67      inference('split', [status(esa)], ['0'])).
% 0.45/0.67  thf('2', plain, ((v1_funct_1 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('3', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.45/0.67      inference('split', [status(esa)], ['0'])).
% 0.45/0.67  thf('4', plain, (((v1_funct_1 @ sk_A))),
% 0.45/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.67  thf(t21_relat_1, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( v1_relat_1 @ A ) =>
% 0.45/0.67       ( r1_tarski @
% 0.45/0.67         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.45/0.67  thf('5', plain,
% 0.45/0.67      (![X3 : $i]:
% 0.45/0.67         ((r1_tarski @ X3 @ 
% 0.45/0.67           (k2_zfmisc_1 @ (k1_relat_1 @ X3) @ (k2_relat_1 @ X3)))
% 0.45/0.67          | ~ (v1_relat_1 @ X3))),
% 0.45/0.67      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.45/0.67  thf(t3_subset, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.45/0.67  thf('6', plain,
% 0.45/0.67      (![X0 : $i, X2 : $i]:
% 0.45/0.67         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.67      inference('cnf', [status(esa)], [t3_subset])).
% 0.45/0.67  thf('7', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ X0)
% 0.45/0.67          | (m1_subset_1 @ X0 @ 
% 0.45/0.67             (k1_zfmisc_1 @ 
% 0.45/0.67              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.67  thf('8', plain,
% 0.45/0.67      ((~ (m1_subset_1 @ sk_A @ 
% 0.45/0.67           (k1_zfmisc_1 @ 
% 0.45/0.67            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.45/0.67         <= (~
% 0.45/0.67             ((m1_subset_1 @ sk_A @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.45/0.67      inference('split', [status(esa)], ['0'])).
% 0.45/0.67  thf('9', plain,
% 0.45/0.67      ((~ (v1_relat_1 @ sk_A))
% 0.45/0.67         <= (~
% 0.45/0.67             ((m1_subset_1 @ sk_A @ 
% 0.45/0.67               (k1_zfmisc_1 @ 
% 0.45/0.67                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.67  thf('10', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('11', plain,
% 0.45/0.67      (((m1_subset_1 @ sk_A @ 
% 0.45/0.67         (k1_zfmisc_1 @ 
% 0.45/0.67          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.45/0.67      inference('demod', [status(thm)], ['9', '10'])).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.45/0.67       ~
% 0.45/0.67       ((m1_subset_1 @ sk_A @ 
% 0.45/0.67         (k1_zfmisc_1 @ 
% 0.45/0.67          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.45/0.67       ~ ((v1_funct_1 @ sk_A))),
% 0.45/0.67      inference('split', [status(esa)], ['0'])).
% 0.45/0.67  thf('13', plain,
% 0.45/0.67      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.45/0.67      inference('sat_resolution*', [status(thm)], ['4', '11', '12'])).
% 0.45/0.67  thf('14', plain,
% 0.45/0.67      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.45/0.67      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.45/0.67  thf(d1_funct_2, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.67           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.45/0.67             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.67           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.45/0.67             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_1, axiom,
% 0.45/0.67    (![B:$i,A:$i]:
% 0.45/0.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.67       ( zip_tseitin_4 @ B @ A ) ))).
% 0.45/0.67  thf('15', plain,
% 0.45/0.67      (![X25 : $i, X26 : $i]:
% 0.45/0.67         ((zip_tseitin_4 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.67  thf('16', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ X0)
% 0.45/0.67          | (m1_subset_1 @ X0 @ 
% 0.45/0.67             (k1_zfmisc_1 @ 
% 0.45/0.67              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.67  thf(zf_stmt_2, type, zip_tseitin_5 : $i > $i > $i > $o).
% 0.45/0.67  thf(zf_stmt_3, axiom,
% 0.45/0.67    (![C:$i,B:$i,A:$i]:
% 0.45/0.67     ( ( zip_tseitin_5 @ C @ B @ A ) =>
% 0.45/0.67       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_4, type, zip_tseitin_4 : $i > $i > $o).
% 0.45/0.67  thf(zf_stmt_5, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67       ( ( ( zip_tseitin_4 @ B @ A ) => ( zip_tseitin_5 @ C @ B @ A ) ) & 
% 0.45/0.67         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.67           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.67             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.45/0.67  thf('17', plain,
% 0.45/0.67      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.45/0.67         (~ (zip_tseitin_4 @ X30 @ X31)
% 0.45/0.67          | (zip_tseitin_5 @ X32 @ X30 @ X31)
% 0.45/0.67          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.67  thf('18', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ X0)
% 0.45/0.67          | (zip_tseitin_5 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.45/0.67          | ~ (zip_tseitin_4 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.67  thf('19', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.45/0.67          | (zip_tseitin_5 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.45/0.67          | ~ (v1_relat_1 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['15', '18'])).
% 0.45/0.67  thf('20', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ X0)
% 0.45/0.67          | (m1_subset_1 @ X0 @ 
% 0.45/0.67             (k1_zfmisc_1 @ 
% 0.45/0.67              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.67  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.67  thf('21', plain,
% 0.45/0.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.67         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.45/0.67          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.45/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.67  thf('22', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ X0)
% 0.45/0.67          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.45/0.67              = (k1_relat_1 @ X0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.67  thf('23', plain,
% 0.45/0.67      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.67         (((X27) != (k1_relset_1 @ X27 @ X28 @ X29))
% 0.45/0.67          | (v1_funct_2 @ X29 @ X27 @ X28)
% 0.45/0.67          | ~ (zip_tseitin_5 @ X29 @ X28 @ X27))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.67  thf('24', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.45/0.67          | ~ (v1_relat_1 @ X0)
% 0.45/0.67          | ~ (zip_tseitin_5 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.45/0.67          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.67  thf('25', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.45/0.67          | ~ (zip_tseitin_5 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.45/0.67          | ~ (v1_relat_1 @ X0))),
% 0.45/0.67      inference('simplify', [status(thm)], ['24'])).
% 0.45/0.67  thf('26', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ X0)
% 0.45/0.67          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.45/0.67          | ~ (v1_relat_1 @ X0)
% 0.45/0.67          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['19', '25'])).
% 0.45/0.67  thf('27', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.45/0.67          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.45/0.67          | ~ (v1_relat_1 @ X0))),
% 0.45/0.67      inference('simplify', [status(thm)], ['26'])).
% 0.45/0.67  thf('28', plain,
% 0.45/0.67      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.45/0.67      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.45/0.67  thf('29', plain,
% 0.45/0.67      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.67  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('31', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.45/0.67      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.67  thf('32', plain, (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ k1_xboole_0)),
% 0.45/0.67      inference('demod', [status(thm)], ['14', '31'])).
% 0.45/0.67  thf('33', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.45/0.67      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.67  thf(t64_relat_1, axiom,
% 0.45/0.67    (![A:$i]:
% 0.45/0.67     ( ( v1_relat_1 @ A ) =>
% 0.45/0.67       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.67           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.67         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.67  thf('34', plain,
% 0.45/0.67      (![X4 : $i]:
% 0.45/0.67         (((k2_relat_1 @ X4) != (k1_xboole_0))
% 0.45/0.67          | ((X4) = (k1_xboole_0))
% 0.45/0.67          | ~ (v1_relat_1 @ X4))),
% 0.45/0.67      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.45/0.67  thf('35', plain,
% 0.45/0.67      ((((k1_xboole_0) != (k1_xboole_0))
% 0.45/0.67        | ~ (v1_relat_1 @ sk_A)
% 0.45/0.67        | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.67  thf('36', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('37', plain,
% 0.45/0.67      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.67      inference('demod', [status(thm)], ['35', '36'])).
% 0.45/0.67  thf('38', plain, (((sk_A) = (k1_xboole_0))),
% 0.45/0.67      inference('simplify', [status(thm)], ['37'])).
% 0.45/0.67  thf('39', plain, (((sk_A) = (k1_xboole_0))),
% 0.45/0.67      inference('simplify', [status(thm)], ['37'])).
% 0.45/0.67  thf(t18_funct_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ~( ( ![C:$i]:
% 0.45/0.67            ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.45/0.67              ( ~( ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) & 
% 0.45/0.67                   ( ( B ) = ( k1_relat_1 @ C ) ) ) ) ) ) & 
% 0.45/0.67          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_6, axiom,
% 0.45/0.67    (![C:$i,B:$i,A:$i]:
% 0.45/0.67     ( ( ( zip_tseitin_0 @ C ) => ( ~( zip_tseitin_1 @ C @ B @ A ) ) ) =>
% 0.45/0.67       ( zip_tseitin_2 @ C @ B @ A ) ))).
% 0.45/0.67  thf('40', plain,
% 0.45/0.67      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.67         ((zip_tseitin_2 @ X9 @ X10 @ X11) | (zip_tseitin_1 @ X9 @ X10 @ X11))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.45/0.67  thf('41', plain,
% 0.45/0.67      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.67         ((zip_tseitin_2 @ X9 @ X10 @ X11) | (zip_tseitin_0 @ X9))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.45/0.67  thf(zf_stmt_7, type, zip_tseitin_3 : $i > $i > $o).
% 0.45/0.67  thf(zf_stmt_8, axiom,
% 0.45/0.67    (![B:$i,A:$i]:
% 0.45/0.67     ( ( zip_tseitin_3 @ B @ A ) =>
% 0.45/0.67       ( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_9, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.45/0.67  thf(zf_stmt_10, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.45/0.67  thf(zf_stmt_11, axiom,
% 0.45/0.67    (![C:$i,B:$i,A:$i]:
% 0.45/0.67     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.45/0.67       ( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.45/0.67         ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ))).
% 0.45/0.67  thf(zf_stmt_12, type, zip_tseitin_0 : $i > $o).
% 0.45/0.67  thf(zf_stmt_13, axiom,
% 0.45/0.67    (![C:$i]:
% 0.45/0.67     ( ( zip_tseitin_0 @ C ) => ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) ))).
% 0.45/0.67  thf(zf_stmt_14, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ~( ( ~( zip_tseitin_3 @ B @ A ) ) & 
% 0.45/0.67          ( ![C:$i]: ( zip_tseitin_2 @ C @ B @ A ) ) ) ))).
% 0.45/0.67  thf('42', plain,
% 0.45/0.67      (![X14 : $i, X15 : $i]:
% 0.45/0.67         ((zip_tseitin_3 @ X14 @ X15)
% 0.45/0.67          | ~ (zip_tseitin_2 @ (sk_C @ X14 @ X15) @ X14 @ X15))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_14])).
% 0.45/0.67  thf('43', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((zip_tseitin_0 @ (sk_C @ X1 @ X0)) | (zip_tseitin_3 @ X1 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['41', '42'])).
% 0.45/0.67  thf('44', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (zip_tseitin_0 @ X5))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.45/0.67  thf('45', plain,
% 0.45/0.67      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.67         ((zip_tseitin_2 @ X9 @ X10 @ X11) | (zip_tseitin_1 @ X9 @ X10 @ X11))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.45/0.67  thf('46', plain,
% 0.45/0.67      (![X14 : $i, X15 : $i]:
% 0.45/0.67         ((zip_tseitin_3 @ X14 @ X15)
% 0.45/0.67          | ~ (zip_tseitin_2 @ (sk_C @ X14 @ X15) @ X14 @ X15))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_14])).
% 0.45/0.67  thf('47', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((zip_tseitin_1 @ (sk_C @ X1 @ X0) @ X1 @ X0)
% 0.45/0.67          | (zip_tseitin_3 @ X1 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.67  thf('48', plain,
% 0.45/0.67      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.67         (((X7) = (k1_relat_1 @ X6)) | ~ (zip_tseitin_1 @ X6 @ X7 @ X8))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_11])).
% 0.45/0.67  thf('49', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((zip_tseitin_3 @ X1 @ X0) | ((X1) = (k1_relat_1 @ (sk_C @ X1 @ X0))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['47', '48'])).
% 0.45/0.67  thf('50', plain,
% 0.45/0.67      (![X4 : $i]:
% 0.45/0.67         (((k1_relat_1 @ X4) != (k1_xboole_0))
% 0.45/0.67          | ((X4) = (k1_xboole_0))
% 0.45/0.67          | ~ (v1_relat_1 @ X4))),
% 0.45/0.67      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.45/0.67  thf('51', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         (((X0) != (k1_xboole_0))
% 0.45/0.67          | (zip_tseitin_3 @ X0 @ X1)
% 0.45/0.67          | ~ (v1_relat_1 @ (sk_C @ X0 @ X1))
% 0.45/0.67          | ((sk_C @ X0 @ X1) = (k1_xboole_0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['49', '50'])).
% 0.45/0.67  thf('52', plain,
% 0.45/0.67      (![X1 : $i]:
% 0.45/0.67         (((sk_C @ k1_xboole_0 @ X1) = (k1_xboole_0))
% 0.45/0.67          | ~ (v1_relat_1 @ (sk_C @ k1_xboole_0 @ X1))
% 0.45/0.67          | (zip_tseitin_3 @ k1_xboole_0 @ X1))),
% 0.45/0.67      inference('simplify', [status(thm)], ['51'])).
% 0.45/0.67  thf('53', plain,
% 0.45/0.67      (![X12 : $i, X13 : $i]:
% 0.45/0.67         (((X13) != (k1_xboole_0)) | ~ (zip_tseitin_3 @ X13 @ X12))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.45/0.67  thf('54', plain, (![X12 : $i]: ~ (zip_tseitin_3 @ k1_xboole_0 @ X12)),
% 0.45/0.67      inference('simplify', [status(thm)], ['53'])).
% 0.45/0.67  thf('55', plain,
% 0.45/0.67      (![X1 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ (sk_C @ k1_xboole_0 @ X1))
% 0.45/0.67          | ((sk_C @ k1_xboole_0 @ X1) = (k1_xboole_0)))),
% 0.45/0.67      inference('clc', [status(thm)], ['52', '54'])).
% 0.45/0.67  thf('56', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (zip_tseitin_0 @ (sk_C @ k1_xboole_0 @ X0))
% 0.45/0.67          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['44', '55'])).
% 0.45/0.67  thf('57', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         ((zip_tseitin_3 @ k1_xboole_0 @ X0)
% 0.45/0.67          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['43', '56'])).
% 0.45/0.67  thf('58', plain, (![X12 : $i]: ~ (zip_tseitin_3 @ k1_xboole_0 @ X12)),
% 0.45/0.67      inference('simplify', [status(thm)], ['53'])).
% 0.45/0.67  thf('59', plain, (![X0 : $i]: ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.67      inference('clc', [status(thm)], ['57', '58'])).
% 0.45/0.67  thf('60', plain,
% 0.45/0.67      (![X14 : $i, X15 : $i]:
% 0.45/0.67         ((zip_tseitin_3 @ X14 @ X15)
% 0.45/0.67          | ~ (zip_tseitin_2 @ (sk_C @ X14 @ X15) @ X14 @ X15))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_14])).
% 0.45/0.67  thf('61', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 0.45/0.67          | (zip_tseitin_3 @ k1_xboole_0 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['59', '60'])).
% 0.45/0.67  thf('62', plain, (![X12 : $i]: ~ (zip_tseitin_3 @ k1_xboole_0 @ X12)),
% 0.45/0.67      inference('simplify', [status(thm)], ['53'])).
% 0.45/0.67  thf('63', plain,
% 0.45/0.67      (![X0 : $i]: ~ (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.45/0.67      inference('clc', [status(thm)], ['61', '62'])).
% 0.45/0.67  thf('64', plain,
% 0.45/0.67      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.45/0.67      inference('sup-', [status(thm)], ['40', '63'])).
% 0.45/0.67  thf('65', plain,
% 0.45/0.67      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.67         (((X7) = (k1_relat_1 @ X6)) | ~ (zip_tseitin_1 @ X6 @ X7 @ X8))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_11])).
% 0.45/0.67  thf('66', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['64', '65'])).
% 0.45/0.67  thf('67', plain, (~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.45/0.67      inference('demod', [status(thm)], ['32', '38', '39', '66'])).
% 0.45/0.67  thf('68', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (zip_tseitin_0 @ X5))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.45/0.67  thf('69', plain, (![X5 : $i]: ((v1_funct_1 @ X5) | ~ (zip_tseitin_0 @ X5))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.45/0.67  thf('70', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['64', '65'])).
% 0.45/0.67  thf('71', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ X0)
% 0.45/0.67          | (m1_subset_1 @ X0 @ 
% 0.45/0.67             (k1_zfmisc_1 @ 
% 0.45/0.67              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.67  thf(cc1_funct_2, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.45/0.67         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.45/0.67  thf('72', plain,
% 0.45/0.67      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.67         (~ (v1_funct_1 @ X19)
% 0.45/0.67          | ~ (v1_partfun1 @ X19 @ X20)
% 0.45/0.67          | (v1_funct_2 @ X19 @ X20 @ X21)
% 0.45/0.67          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.45/0.67      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.45/0.67  thf('73', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ X0)
% 0.45/0.67          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.45/0.67          | ~ (v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.45/0.67          | ~ (v1_funct_1 @ X0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['71', '72'])).
% 0.45/0.67  thf('74', plain,
% 0.45/0.67      ((~ (v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)
% 0.45/0.67        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.45/0.67        | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 0.45/0.67           (k2_relat_1 @ k1_xboole_0))
% 0.45/0.67        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['70', '73'])).
% 0.45/0.67  thf('75', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (zip_tseitin_0 @ X5))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_13])).
% 0.45/0.67  thf('76', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['64', '65'])).
% 0.45/0.67  thf('77', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ X0)
% 0.45/0.67          | (m1_subset_1 @ X0 @ 
% 0.45/0.67             (k1_zfmisc_1 @ 
% 0.45/0.67              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.45/0.67      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.67  thf(cc1_partfun1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( v1_xboole_0 @ A ) =>
% 0.45/0.67       ( ![C:$i]:
% 0.45/0.67         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.67           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.45/0.67  thf('78', plain,
% 0.45/0.67      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.67         (~ (v1_xboole_0 @ X22)
% 0.45/0.67          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X24)))
% 0.45/0.67          | (v1_partfun1 @ X23 @ X22))),
% 0.45/0.67      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.45/0.67  thf('79', plain,
% 0.45/0.67      (![X0 : $i]:
% 0.45/0.67         (~ (v1_relat_1 @ X0)
% 0.45/0.67          | (v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.45/0.67          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['77', '78'])).
% 0.45/0.67  thf('80', plain,
% 0.45/0.67      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.45/0.67        | (v1_partfun1 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))
% 0.45/0.67        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['76', '79'])).
% 0.45/0.67  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.45/0.67  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.67  thf('82', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['64', '65'])).
% 0.45/0.67  thf('83', plain,
% 0.45/0.67      (((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)
% 0.45/0.67        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.45/0.67      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.45/0.67  thf('84', plain,
% 0.45/0.67      ((~ (zip_tseitin_0 @ k1_xboole_0)
% 0.45/0.67        | (v1_partfun1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['75', '83'])).
% 0.45/0.67  thf('85', plain,
% 0.45/0.67      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.67         ((zip_tseitin_2 @ X9 @ X10 @ X11) | (zip_tseitin_0 @ X9))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.45/0.67  thf('86', plain,
% 0.45/0.67      (![X0 : $i]: ~ (zip_tseitin_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.45/0.67      inference('clc', [status(thm)], ['61', '62'])).
% 0.45/0.67  thf('87', plain, ((zip_tseitin_0 @ k1_xboole_0)),
% 0.45/0.67      inference('sup-', [status(thm)], ['85', '86'])).
% 0.45/0.67  thf('88', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.45/0.67      inference('demod', [status(thm)], ['84', '87'])).
% 0.45/0.67  thf('89', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.45/0.67      inference('sup-', [status(thm)], ['64', '65'])).
% 0.45/0.67  thf('90', plain,
% 0.45/0.67      ((~ (v1_funct_1 @ k1_xboole_0)
% 0.45/0.67        | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0))
% 0.45/0.67        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.45/0.67      inference('demod', [status(thm)], ['74', '88', '89'])).
% 0.45/0.67  thf('91', plain,
% 0.45/0.67      ((~ (zip_tseitin_0 @ k1_xboole_0)
% 0.45/0.67        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.45/0.67        | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['69', '90'])).
% 0.45/0.67  thf('92', plain, ((zip_tseitin_0 @ k1_xboole_0)),
% 0.45/0.67      inference('sup-', [status(thm)], ['85', '86'])).
% 0.45/0.67  thf('93', plain,
% 0.45/0.67      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.45/0.67        | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0)))),
% 0.45/0.67      inference('demod', [status(thm)], ['91', '92'])).
% 0.45/0.67  thf('94', plain,
% 0.45/0.67      ((~ (zip_tseitin_0 @ k1_xboole_0)
% 0.45/0.67        | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['68', '93'])).
% 0.45/0.67  thf('95', plain, ((zip_tseitin_0 @ k1_xboole_0)),
% 0.45/0.67      inference('sup-', [status(thm)], ['85', '86'])).
% 0.45/0.67  thf('96', plain,
% 0.45/0.67      ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0))),
% 0.45/0.67      inference('demod', [status(thm)], ['94', '95'])).
% 0.45/0.67  thf('97', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.45/0.67      inference('demod', [status(thm)], ['29', '30'])).
% 0.45/0.67  thf('98', plain, (((sk_A) = (k1_xboole_0))),
% 0.45/0.67      inference('simplify', [status(thm)], ['37'])).
% 0.45/0.68  thf('99', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.68      inference('demod', [status(thm)], ['97', '98'])).
% 0.45/0.68  thf('100', plain, ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.45/0.68      inference('demod', [status(thm)], ['96', '99'])).
% 0.45/0.68  thf('101', plain, ($false), inference('demod', [status(thm)], ['67', '100'])).
% 0.45/0.68  
% 0.45/0.68  % SZS output end Refutation
% 0.45/0.68  
% 0.45/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
