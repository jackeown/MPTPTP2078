%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IeC8wSAeaa

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:55 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 350 expanded)
%              Number of leaves         :   37 ( 116 expanded)
%              Depth                    :   18
%              Number of atoms          :  624 (3594 expanded)
%              Number of equality atoms :   39 (  82 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t4_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
         => ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X19 )
      | ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X26 )
      | ( zip_tseitin_1 @ X27 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22
       != ( k1_relset_1 @ X22 @ X23 @ X24 ) )
      | ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( zip_tseitin_1 @ X24 @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
     != ( k1_relat_1 @ sk_B_1 ) )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
   <= ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['19'])).

thf('23',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['19'])).

thf('26',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['19'])).

thf('28',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['23','26','27'])).

thf('29',plain,(
    ~ ( v1_funct_2 @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['20','28'])).

thf('30',plain,(
    ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['18','29'])).

thf('31',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['12','30'])).

thf('32',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('33',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['12','30'])).

thf('34',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( zip_tseitin_0 @ k1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['31','34'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('37',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('40',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('43',plain,(
    ! [X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X1 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('44',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('46',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['41','42','48'])).

thf('50',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['36','49'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('51',plain,(
    ! [X13: $i] :
      ( ( ( k2_relat_1 @ X13 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X13 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( ( k1_relat_1 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('57',plain,(
    ! [X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 )
      | ( X21 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('58',plain,(
    ! [X20: $i] :
      ( zip_tseitin_0 @ X20 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['56','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['35','55','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.IeC8wSAeaa
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:16:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.58  % Solved by: fo/fo7.sh
% 0.35/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.58  % done 140 iterations in 0.122s
% 0.35/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.58  % SZS output start Refutation
% 0.35/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.35/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.35/0.58  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.35/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.35/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.58  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.35/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.35/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.35/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.58  thf(t4_funct_2, conjecture,
% 0.35/0.58    (![A:$i,B:$i]:
% 0.35/0.58     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.58       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.35/0.58         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.35/0.58           ( m1_subset_1 @
% 0.35/0.58             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.35/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.58    (~( ![A:$i,B:$i]:
% 0.35/0.58        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.58          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.35/0.58            ( ( v1_funct_1 @ B ) & 
% 0.35/0.58              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.35/0.58              ( m1_subset_1 @
% 0.35/0.58                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 0.35/0.58    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 0.35/0.58  thf('0', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf(dt_k2_subset_1, axiom,
% 0.35/0.58    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.35/0.58  thf('1', plain,
% 0.35/0.58      (![X6 : $i]: (m1_subset_1 @ (k2_subset_1 @ X6) @ (k1_zfmisc_1 @ X6))),
% 0.35/0.58      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.35/0.58  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.35/0.58  thf('2', plain, (![X5 : $i]: ((k2_subset_1 @ X5) = (X5))),
% 0.35/0.58      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.35/0.58  thf('3', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.35/0.58      inference('demod', [status(thm)], ['1', '2'])).
% 0.35/0.58  thf(t3_subset, axiom,
% 0.35/0.58    (![A:$i,B:$i]:
% 0.35/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.35/0.58  thf('4', plain,
% 0.35/0.58      (![X7 : $i, X8 : $i]:
% 0.35/0.58         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.35/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.35/0.58  thf('5', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.35/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.35/0.58  thf(t11_relset_1, axiom,
% 0.35/0.58    (![A:$i,B:$i,C:$i]:
% 0.35/0.58     ( ( v1_relat_1 @ C ) =>
% 0.35/0.58       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.35/0.58           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.35/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.35/0.58  thf('6', plain,
% 0.35/0.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.35/0.58         (~ (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.35/0.58          | ~ (r1_tarski @ (k2_relat_1 @ X17) @ X19)
% 0.35/0.58          | (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.35/0.58          | ~ (v1_relat_1 @ X17))),
% 0.35/0.58      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.35/0.58  thf('7', plain,
% 0.35/0.58      (![X0 : $i, X1 : $i]:
% 0.35/0.58         (~ (v1_relat_1 @ X0)
% 0.35/0.58          | (m1_subset_1 @ X0 @ 
% 0.35/0.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.35/0.58          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.35/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.35/0.58  thf('8', plain,
% 0.35/0.58      (((m1_subset_1 @ sk_B_1 @ 
% 0.35/0.58         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))
% 0.35/0.58        | ~ (v1_relat_1 @ sk_B_1))),
% 0.35/0.58      inference('sup-', [status(thm)], ['0', '7'])).
% 0.35/0.58  thf('9', plain, ((v1_relat_1 @ sk_B_1)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('10', plain,
% 0.35/0.58      ((m1_subset_1 @ sk_B_1 @ 
% 0.35/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.35/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.35/0.58  thf(d1_funct_2, axiom,
% 0.35/0.58    (![A:$i,B:$i,C:$i]:
% 0.35/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.58           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.35/0.58             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.35/0.58         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.58           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.35/0.58             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.35/0.58  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.35/0.58  thf(zf_stmt_2, axiom,
% 0.35/0.58    (![C:$i,B:$i,A:$i]:
% 0.35/0.58     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.35/0.58       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.35/0.58  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.35/0.58  thf(zf_stmt_4, axiom,
% 0.35/0.58    (![B:$i,A:$i]:
% 0.35/0.58     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.35/0.58       ( zip_tseitin_0 @ B @ A ) ))).
% 0.35/0.58  thf(zf_stmt_5, axiom,
% 0.35/0.58    (![A:$i,B:$i,C:$i]:
% 0.35/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.58       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.35/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.35/0.58           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.35/0.58             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.35/0.58  thf('11', plain,
% 0.35/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.35/0.58         (~ (zip_tseitin_0 @ X25 @ X26)
% 0.35/0.58          | (zip_tseitin_1 @ X27 @ X25 @ X26)
% 0.35/0.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25))))),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.35/0.58  thf('12', plain,
% 0.35/0.58      (((zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 0.35/0.58        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.35/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.35/0.58  thf('13', plain,
% 0.35/0.58      ((m1_subset_1 @ sk_B_1 @ 
% 0.35/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.35/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.35/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.35/0.58    (![A:$i,B:$i,C:$i]:
% 0.35/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.35/0.58  thf('14', plain,
% 0.35/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.35/0.58         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.35/0.58          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.35/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.35/0.58  thf('15', plain,
% 0.35/0.58      (((k1_relset_1 @ (k1_relat_1 @ sk_B_1) @ sk_A @ sk_B_1)
% 0.35/0.58         = (k1_relat_1 @ sk_B_1))),
% 0.35/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.35/0.58  thf('16', plain,
% 0.35/0.58      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.35/0.58         (((X22) != (k1_relset_1 @ X22 @ X23 @ X24))
% 0.35/0.58          | (v1_funct_2 @ X24 @ X22 @ X23)
% 0.35/0.58          | ~ (zip_tseitin_1 @ X24 @ X23 @ X22))),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.35/0.58  thf('17', plain,
% 0.35/0.58      ((((k1_relat_1 @ sk_B_1) != (k1_relat_1 @ sk_B_1))
% 0.35/0.58        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))
% 0.35/0.58        | (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.35/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.35/0.58  thf('18', plain,
% 0.35/0.58      (((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.35/0.58        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.35/0.58      inference('simplify', [status(thm)], ['17'])).
% 0.35/0.58  thf('19', plain,
% 0.35/0.58      ((~ (v1_funct_1 @ sk_B_1)
% 0.35/0.58        | ~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.35/0.58        | ~ (m1_subset_1 @ sk_B_1 @ 
% 0.35/0.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('20', plain,
% 0.35/0.58      ((~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.35/0.58         <= (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.35/0.58      inference('split', [status(esa)], ['19'])).
% 0.35/0.58  thf('21', plain, ((v1_funct_1 @ sk_B_1)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('22', plain, ((~ (v1_funct_1 @ sk_B_1)) <= (~ ((v1_funct_1 @ sk_B_1)))),
% 0.35/0.58      inference('split', [status(esa)], ['19'])).
% 0.35/0.58  thf('23', plain, (((v1_funct_1 @ sk_B_1))),
% 0.35/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.35/0.58  thf('24', plain,
% 0.35/0.58      ((m1_subset_1 @ sk_B_1 @ 
% 0.35/0.58        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.35/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.35/0.58  thf('25', plain,
% 0.35/0.58      ((~ (m1_subset_1 @ sk_B_1 @ 
% 0.35/0.58           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))
% 0.35/0.58         <= (~
% 0.35/0.58             ((m1_subset_1 @ sk_B_1 @ 
% 0.35/0.58               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))))),
% 0.35/0.58      inference('split', [status(esa)], ['19'])).
% 0.35/0.58  thf('26', plain,
% 0.35/0.58      (((m1_subset_1 @ sk_B_1 @ 
% 0.35/0.58         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))))),
% 0.35/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.35/0.58  thf('27', plain,
% 0.35/0.58      (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.35/0.58       ~
% 0.35/0.58       ((m1_subset_1 @ sk_B_1 @ 
% 0.35/0.58         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)))) | 
% 0.35/0.58       ~ ((v1_funct_1 @ sk_B_1))),
% 0.35/0.58      inference('split', [status(esa)], ['19'])).
% 0.35/0.58  thf('28', plain, (~ ((v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A))),
% 0.35/0.58      inference('sat_resolution*', [status(thm)], ['23', '26', '27'])).
% 0.35/0.58  thf('29', plain, (~ (v1_funct_2 @ sk_B_1 @ (k1_relat_1 @ sk_B_1) @ sk_A)),
% 0.35/0.58      inference('simpl_trail', [status(thm)], ['20', '28'])).
% 0.35/0.58  thf('30', plain, (~ (zip_tseitin_1 @ sk_B_1 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.35/0.58      inference('clc', [status(thm)], ['18', '29'])).
% 0.35/0.58  thf('31', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.35/0.58      inference('clc', [status(thm)], ['12', '30'])).
% 0.35/0.58  thf('32', plain,
% 0.35/0.58      (![X20 : $i, X21 : $i]:
% 0.35/0.58         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.35/0.58  thf('33', plain, (~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.35/0.58      inference('clc', [status(thm)], ['12', '30'])).
% 0.35/0.58  thf('34', plain, (((sk_A) = (k1_xboole_0))),
% 0.35/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.35/0.58  thf('35', plain, (~ (zip_tseitin_0 @ k1_xboole_0 @ (k1_relat_1 @ sk_B_1))),
% 0.35/0.58      inference('demod', [status(thm)], ['31', '34'])).
% 0.35/0.58  thf(t7_xboole_0, axiom,
% 0.35/0.58    (![A:$i]:
% 0.35/0.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.35/0.58          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.35/0.58  thf('36', plain,
% 0.35/0.58      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.35/0.58      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.35/0.58  thf('37', plain, ((r1_tarski @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('38', plain,
% 0.35/0.58      (![X7 : $i, X9 : $i]:
% 0.35/0.58         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.35/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.35/0.58  thf('39', plain,
% 0.35/0.58      ((m1_subset_1 @ (k2_relat_1 @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.35/0.58      inference('sup-', [status(thm)], ['37', '38'])).
% 0.35/0.58  thf(t5_subset, axiom,
% 0.35/0.58    (![A:$i,B:$i,C:$i]:
% 0.35/0.58     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.35/0.58          ( v1_xboole_0 @ C ) ) ))).
% 0.35/0.58  thf('40', plain,
% 0.35/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.35/0.58         (~ (r2_hidden @ X10 @ X11)
% 0.35/0.58          | ~ (v1_xboole_0 @ X12)
% 0.35/0.58          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.35/0.58      inference('cnf', [status(esa)], [t5_subset])).
% 0.35/0.58  thf('41', plain,
% 0.35/0.58      (![X0 : $i]:
% 0.35/0.58         (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1)))),
% 0.35/0.58      inference('sup-', [status(thm)], ['39', '40'])).
% 0.35/0.58  thf('42', plain, (((sk_A) = (k1_xboole_0))),
% 0.35/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.35/0.58  thf(t66_xboole_1, axiom,
% 0.35/0.58    (![A:$i]:
% 0.35/0.58     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.35/0.58       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.35/0.58  thf('43', plain,
% 0.35/0.58      (![X1 : $i]: ((r1_xboole_0 @ X1 @ X1) | ((X1) != (k1_xboole_0)))),
% 0.35/0.58      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.35/0.58  thf('44', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.35/0.58      inference('simplify', [status(thm)], ['43'])).
% 0.35/0.58  thf(t69_xboole_1, axiom,
% 0.35/0.58    (![A:$i,B:$i]:
% 0.35/0.58     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.35/0.58       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.35/0.58  thf('45', plain,
% 0.35/0.58      (![X3 : $i, X4 : $i]:
% 0.35/0.58         (~ (r1_xboole_0 @ X3 @ X4)
% 0.35/0.58          | ~ (r1_tarski @ X3 @ X4)
% 0.35/0.58          | (v1_xboole_0 @ X3))),
% 0.35/0.58      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.35/0.58  thf('46', plain,
% 0.35/0.58      (((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0))),
% 0.35/0.58      inference('sup-', [status(thm)], ['44', '45'])).
% 0.35/0.58  thf('47', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.35/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.35/0.58  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.35/0.58      inference('demod', [status(thm)], ['46', '47'])).
% 0.35/0.58  thf('49', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B_1))),
% 0.35/0.58      inference('demod', [status(thm)], ['41', '42', '48'])).
% 0.35/0.58  thf('50', plain, (((k2_relat_1 @ sk_B_1) = (k1_xboole_0))),
% 0.35/0.58      inference('sup-', [status(thm)], ['36', '49'])).
% 0.35/0.58  thf(t65_relat_1, axiom,
% 0.35/0.58    (![A:$i]:
% 0.35/0.58     ( ( v1_relat_1 @ A ) =>
% 0.35/0.58       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.35/0.58         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.35/0.58  thf('51', plain,
% 0.35/0.58      (![X13 : $i]:
% 0.35/0.58         (((k2_relat_1 @ X13) != (k1_xboole_0))
% 0.35/0.58          | ((k1_relat_1 @ X13) = (k1_xboole_0))
% 0.35/0.58          | ~ (v1_relat_1 @ X13))),
% 0.35/0.58      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.35/0.58  thf('52', plain,
% 0.35/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.35/0.58        | ~ (v1_relat_1 @ sk_B_1)
% 0.35/0.58        | ((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 0.35/0.58      inference('sup-', [status(thm)], ['50', '51'])).
% 0.35/0.58  thf('53', plain, ((v1_relat_1 @ sk_B_1)),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.58  thf('54', plain,
% 0.35/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.35/0.58        | ((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))),
% 0.35/0.58      inference('demod', [status(thm)], ['52', '53'])).
% 0.35/0.58  thf('55', plain, (((k1_relat_1 @ sk_B_1) = (k1_xboole_0))),
% 0.35/0.58      inference('simplify', [status(thm)], ['54'])).
% 0.35/0.58  thf('56', plain,
% 0.35/0.58      (![X20 : $i, X21 : $i]:
% 0.35/0.58         ((zip_tseitin_0 @ X20 @ X21) | ((X20) = (k1_xboole_0)))),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.35/0.58  thf('57', plain,
% 0.35/0.58      (![X20 : $i, X21 : $i]:
% 0.35/0.58         ((zip_tseitin_0 @ X20 @ X21) | ((X21) != (k1_xboole_0)))),
% 0.35/0.58      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.35/0.58  thf('58', plain, (![X20 : $i]: (zip_tseitin_0 @ X20 @ k1_xboole_0)),
% 0.35/0.58      inference('simplify', [status(thm)], ['57'])).
% 0.35/0.58  thf('59', plain,
% 0.35/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.35/0.58         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.35/0.58      inference('sup+', [status(thm)], ['56', '58'])).
% 0.35/0.58  thf('60', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ X0)),
% 0.35/0.58      inference('eq_fact', [status(thm)], ['59'])).
% 0.35/0.58  thf('61', plain, ($false),
% 0.35/0.58      inference('demod', [status(thm)], ['35', '55', '60'])).
% 0.35/0.58  
% 0.35/0.58  % SZS output end Refutation
% 0.35/0.58  
% 0.35/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
