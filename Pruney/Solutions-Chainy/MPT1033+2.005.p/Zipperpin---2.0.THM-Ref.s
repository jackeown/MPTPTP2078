%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZxxE1VvpD5

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:04 EST 2020

% Result     : Theorem 0.87s
% Output     : Refutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 962 expanded)
%              Number of leaves         :   36 ( 291 expanded)
%              Depth                    :   23
%              Number of atoms          : 1052 (14213 expanded)
%              Number of equality atoms :   99 ( 780 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t142_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r1_partfun1 @ C @ D )
           => ( ( ( B = k1_xboole_0 )
                & ( A != k1_xboole_0 ) )
              | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ( r1_partfun1 @ C @ D )
             => ( ( ( B = k1_xboole_0 )
                  & ( A != k1_xboole_0 ) )
                | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t142_funct_2])).

thf('0',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( v1_partfun1 @ X29 @ X30 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( v1_funct_1 @ X29 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B_1 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t148_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( ( v1_partfun1 @ C @ A )
              & ( v1_partfun1 @ D @ A )
              & ( r1_partfun1 @ C @ D ) )
           => ( C = D ) ) ) ) )).

thf('12',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( X35 = X32 )
      | ~ ( r1_partfun1 @ X35 @ X32 )
      | ~ ( v1_partfun1 @ X32 @ X33 )
      | ~ ( v1_partfun1 @ X35 @ X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( X0 = sk_D )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( r1_partfun1 @ sk_C @ sk_D )
    | ( sk_C = sk_D )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ( sk_C = sk_D )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( v1_partfun1 @ X29 @ X30 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( v1_funct_1 @ X29 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C = sk_D ) ),
    inference(clc,[status(thm)],['20','26'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('28',plain,(
    ! [X26: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X26 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,
    ( ( sk_C = sk_D )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_C = sk_D ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_C = sk_D )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_C )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('43',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_relset_1 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['43'])).

thf('45',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','45'])).

thf('47',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['3','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C = sk_D ) ),
    inference(clc,[status(thm)],['20','26'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('53',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('54',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( v5_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('56',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v5_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('59',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['57','60'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('62',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('63',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('64',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('68',plain,(
    ! [X15: $i] :
      ( ( ( k2_relat_1 @ X15 )
       != k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('76',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_C = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['51','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ( sk_C = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['83'])).

thf('85',plain,
    ( ( sk_C = sk_D )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','84'])).

thf('86',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['42','44'])).

thf('89',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['49','89'])).

thf('91',plain,
    ( ( sk_C = sk_D )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('92',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C = sk_D ) ),
    inference(clc,[status(thm)],['20','26'])).

thf('93',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_C = sk_D )
    | ( sk_C = sk_D ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( sk_C = sk_D )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88'])).

thf('96',plain,
    ( ( k1_xboole_0 = sk_D )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( sk_C = sk_D )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('98',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('99',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('102',plain,
    ( ( r1_tarski @ sk_D @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('104',plain,
    ( ( ( sk_D = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ( sk_C = sk_D )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('107',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_C = sk_D )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88'])).

thf('109',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0 = sk_D )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k1_xboole_0 = sk_D )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['46','47'])).

thf('112',plain,
    ( ( k1_xboole_0 = sk_D )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['110','111'])).

thf('113',plain,(
    k1_xboole_0 = sk_D ),
    inference(clc,[status(thm)],['96','112'])).

thf('114',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['43'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    $false ),
    inference(demod,[status(thm)],['90','113','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZxxE1VvpD5
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:21:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.87/1.06  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.87/1.06  % Solved by: fo/fo7.sh
% 0.87/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.87/1.06  % done 1188 iterations in 0.612s
% 0.87/1.06  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.87/1.06  % SZS output start Refutation
% 0.87/1.06  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.87/1.06  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.87/1.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.87/1.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.87/1.06  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.87/1.06  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.87/1.06  thf(sk_D_type, type, sk_D: $i).
% 0.87/1.06  thf(sk_B_type, type, sk_B: $i > $i).
% 0.87/1.06  thf(sk_C_type, type, sk_C: $i).
% 0.87/1.06  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.87/1.06  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.87/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.87/1.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.87/1.06  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.87/1.06  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.87/1.06  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.87/1.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.87/1.06  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.87/1.06  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.87/1.06  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.87/1.06  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.87/1.06  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.87/1.06  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.87/1.06  thf(t142_funct_2, conjecture,
% 0.87/1.06    (![A:$i,B:$i,C:$i]:
% 0.87/1.06     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.87/1.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.87/1.06       ( ![D:$i]:
% 0.87/1.06         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.87/1.06             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.87/1.06           ( ( r1_partfun1 @ C @ D ) =>
% 0.87/1.06             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.87/1.06               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.87/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.87/1.06    (~( ![A:$i,B:$i,C:$i]:
% 0.87/1.06        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.87/1.06            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.87/1.06          ( ![D:$i]:
% 0.87/1.06            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.87/1.06                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.87/1.06              ( ( r1_partfun1 @ C @ D ) =>
% 0.87/1.06                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.87/1.06                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.87/1.06    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.87/1.06  thf('0', plain, ((((sk_B_1) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('1', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.87/1.06      inference('split', [status(esa)], ['0'])).
% 0.87/1.06  thf('2', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('3', plain,
% 0.87/1.06      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ sk_D))
% 0.87/1.06         <= ((((sk_A) = (k1_xboole_0))))),
% 0.87/1.06      inference('sup-', [status(thm)], ['1', '2'])).
% 0.87/1.06  thf('4', plain,
% 0.87/1.06      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('5', plain,
% 0.87/1.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf(cc5_funct_2, axiom,
% 0.87/1.06    (![A:$i,B:$i]:
% 0.87/1.06     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.87/1.06       ( ![C:$i]:
% 0.87/1.06         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.87/1.06           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.87/1.06             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.87/1.06  thf('6', plain,
% 0.87/1.06      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.87/1.06         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.87/1.06          | (v1_partfun1 @ X29 @ X30)
% 0.87/1.06          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 0.87/1.06          | ~ (v1_funct_1 @ X29)
% 0.87/1.06          | (v1_xboole_0 @ X31))),
% 0.87/1.06      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.87/1.06  thf('7', plain,
% 0.87/1.06      (((v1_xboole_0 @ sk_B_1)
% 0.87/1.06        | ~ (v1_funct_1 @ sk_D)
% 0.87/1.06        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B_1)
% 0.87/1.06        | (v1_partfun1 @ sk_D @ sk_A))),
% 0.87/1.06      inference('sup-', [status(thm)], ['5', '6'])).
% 0.87/1.06  thf('8', plain, ((v1_funct_1 @ sk_D)),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('9', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('10', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.87/1.06      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.87/1.06  thf('11', plain,
% 0.87/1.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf(t148_partfun1, axiom,
% 0.87/1.06    (![A:$i,B:$i,C:$i]:
% 0.87/1.06     ( ( ( v1_funct_1 @ C ) & 
% 0.87/1.06         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.87/1.06       ( ![D:$i]:
% 0.87/1.06         ( ( ( v1_funct_1 @ D ) & 
% 0.87/1.06             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.87/1.06           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.87/1.06               ( r1_partfun1 @ C @ D ) ) =>
% 0.87/1.06             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.87/1.06  thf('12', plain,
% 0.87/1.06      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.87/1.06         (~ (v1_funct_1 @ X32)
% 0.87/1.06          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.87/1.06          | ((X35) = (X32))
% 0.87/1.06          | ~ (r1_partfun1 @ X35 @ X32)
% 0.87/1.06          | ~ (v1_partfun1 @ X32 @ X33)
% 0.87/1.06          | ~ (v1_partfun1 @ X35 @ X33)
% 0.87/1.06          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.87/1.06          | ~ (v1_funct_1 @ X35))),
% 0.87/1.06      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.87/1.06  thf('13', plain,
% 0.87/1.06      (![X0 : $i]:
% 0.87/1.06         (~ (v1_funct_1 @ X0)
% 0.87/1.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.87/1.06          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.87/1.06          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.87/1.06          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.87/1.06          | ((X0) = (sk_D))
% 0.87/1.06          | ~ (v1_funct_1 @ sk_D))),
% 0.87/1.06      inference('sup-', [status(thm)], ['11', '12'])).
% 0.87/1.06  thf('14', plain, ((v1_funct_1 @ sk_D)),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('15', plain,
% 0.87/1.06      (![X0 : $i]:
% 0.87/1.06         (~ (v1_funct_1 @ X0)
% 0.87/1.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.87/1.06          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.87/1.06          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.87/1.06          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.87/1.06          | ((X0) = (sk_D)))),
% 0.87/1.06      inference('demod', [status(thm)], ['13', '14'])).
% 0.87/1.06  thf('16', plain,
% 0.87/1.06      (![X0 : $i]:
% 0.87/1.06         ((v1_xboole_0 @ sk_B_1)
% 0.87/1.06          | ((X0) = (sk_D))
% 0.87/1.06          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.87/1.06          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.87/1.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.87/1.06          | ~ (v1_funct_1 @ X0))),
% 0.87/1.06      inference('sup-', [status(thm)], ['10', '15'])).
% 0.87/1.06  thf('17', plain,
% 0.87/1.06      ((~ (v1_funct_1 @ sk_C)
% 0.87/1.06        | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.87/1.06        | ~ (r1_partfun1 @ sk_C @ sk_D)
% 0.87/1.06        | ((sk_C) = (sk_D))
% 0.87/1.06        | (v1_xboole_0 @ sk_B_1))),
% 0.87/1.06      inference('sup-', [status(thm)], ['4', '16'])).
% 0.87/1.06  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('19', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('20', plain,
% 0.87/1.06      ((~ (v1_partfun1 @ sk_C @ sk_A)
% 0.87/1.06        | ((sk_C) = (sk_D))
% 0.87/1.06        | (v1_xboole_0 @ sk_B_1))),
% 0.87/1.06      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.87/1.06  thf('21', plain,
% 0.87/1.06      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('22', plain,
% 0.87/1.06      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.87/1.06         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.87/1.06          | (v1_partfun1 @ X29 @ X30)
% 0.87/1.06          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 0.87/1.06          | ~ (v1_funct_1 @ X29)
% 0.87/1.06          | (v1_xboole_0 @ X31))),
% 0.87/1.06      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.87/1.06  thf('23', plain,
% 0.87/1.06      (((v1_xboole_0 @ sk_B_1)
% 0.87/1.06        | ~ (v1_funct_1 @ sk_C)
% 0.87/1.06        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.87/1.06        | (v1_partfun1 @ sk_C @ sk_A))),
% 0.87/1.06      inference('sup-', [status(thm)], ['21', '22'])).
% 0.87/1.06  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('25', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('26', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_C @ sk_A))),
% 0.87/1.06      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.87/1.06  thf('27', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_C) = (sk_D)))),
% 0.87/1.06      inference('clc', [status(thm)], ['20', '26'])).
% 0.87/1.06  thf(t9_mcart_1, axiom,
% 0.87/1.06    (![A:$i]:
% 0.87/1.06     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.87/1.06          ( ![B:$i]:
% 0.87/1.06            ( ~( ( r2_hidden @ B @ A ) & 
% 0.87/1.06                 ( ![C:$i,D:$i]:
% 0.87/1.06                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.87/1.06                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.87/1.06  thf('28', plain,
% 0.87/1.06      (![X26 : $i]:
% 0.87/1.06         (((X26) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X26) @ X26))),
% 0.87/1.06      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.87/1.06  thf(d10_xboole_0, axiom,
% 0.87/1.06    (![A:$i,B:$i]:
% 0.87/1.06     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.87/1.06  thf('29', plain,
% 0.87/1.06      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.87/1.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.87/1.06  thf('30', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.87/1.06      inference('simplify', [status(thm)], ['29'])).
% 0.87/1.06  thf(t3_subset, axiom,
% 0.87/1.06    (![A:$i,B:$i]:
% 0.87/1.06     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.87/1.06  thf('31', plain,
% 0.87/1.06      (![X4 : $i, X6 : $i]:
% 0.87/1.06         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.87/1.06      inference('cnf', [status(esa)], [t3_subset])).
% 0.87/1.06  thf('32', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.87/1.06      inference('sup-', [status(thm)], ['30', '31'])).
% 0.87/1.06  thf(t5_subset, axiom,
% 0.87/1.06    (![A:$i,B:$i,C:$i]:
% 0.87/1.06     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.87/1.06          ( v1_xboole_0 @ C ) ) ))).
% 0.87/1.06  thf('33', plain,
% 0.87/1.06      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.87/1.06         (~ (r2_hidden @ X10 @ X11)
% 0.87/1.06          | ~ (v1_xboole_0 @ X12)
% 0.87/1.06          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.87/1.06      inference('cnf', [status(esa)], [t5_subset])).
% 0.87/1.06  thf('34', plain,
% 0.87/1.06      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.87/1.06      inference('sup-', [status(thm)], ['32', '33'])).
% 0.87/1.06  thf('35', plain,
% 0.87/1.06      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.87/1.06      inference('sup-', [status(thm)], ['28', '34'])).
% 0.87/1.06  thf('36', plain, ((((sk_C) = (sk_D)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.87/1.06      inference('sup-', [status(thm)], ['27', '35'])).
% 0.87/1.06  thf('37', plain,
% 0.87/1.06      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.87/1.06      inference('split', [status(esa)], ['0'])).
% 0.87/1.06  thf('38', plain,
% 0.87/1.06      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (sk_D))))
% 0.87/1.06         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.87/1.06      inference('sup-', [status(thm)], ['36', '37'])).
% 0.87/1.06  thf('39', plain, ((((sk_C) = (sk_D))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.87/1.06      inference('simplify', [status(thm)], ['38'])).
% 0.87/1.06  thf('40', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('41', plain,
% 0.87/1.06      ((~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_C))
% 0.87/1.06         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.87/1.06      inference('sup-', [status(thm)], ['39', '40'])).
% 0.87/1.06  thf('42', plain,
% 0.87/1.06      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf(reflexivity_r2_relset_1, axiom,
% 0.87/1.06    (![A:$i,B:$i,C:$i,D:$i]:
% 0.87/1.06     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.87/1.06         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.87/1.06       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.87/1.06  thf('43', plain,
% 0.87/1.06      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.87/1.06         ((r2_relset_1 @ X22 @ X23 @ X24 @ X24)
% 0.87/1.06          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.87/1.06          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.87/1.06      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.87/1.06  thf('44', plain,
% 0.87/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.87/1.06         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.87/1.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.87/1.06      inference('condensation', [status(thm)], ['43'])).
% 0.87/1.06  thf('45', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_C)),
% 0.87/1.06      inference('sup-', [status(thm)], ['42', '44'])).
% 0.87/1.06  thf('46', plain, ((((sk_B_1) = (k1_xboole_0)))),
% 0.87/1.06      inference('demod', [status(thm)], ['41', '45'])).
% 0.87/1.06  thf('47', plain,
% 0.87/1.06      ((((sk_A) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.87/1.06      inference('split', [status(esa)], ['0'])).
% 0.87/1.06  thf('48', plain, ((((sk_A) = (k1_xboole_0)))),
% 0.87/1.06      inference('sat_resolution*', [status(thm)], ['46', '47'])).
% 0.87/1.06  thf('49', plain, (~ (r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C @ sk_D)),
% 0.87/1.06      inference('simpl_trail', [status(thm)], ['3', '48'])).
% 0.87/1.06  thf('50', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_C) = (sk_D)))),
% 0.87/1.06      inference('clc', [status(thm)], ['20', '26'])).
% 0.87/1.06  thf('51', plain,
% 0.87/1.06      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.87/1.06      inference('sup-', [status(thm)], ['28', '34'])).
% 0.87/1.06  thf('52', plain,
% 0.87/1.06      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.87/1.06      inference('sup-', [status(thm)], ['28', '34'])).
% 0.87/1.06  thf('53', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.87/1.06      inference('sup-', [status(thm)], ['30', '31'])).
% 0.87/1.06  thf(cc2_relset_1, axiom,
% 0.87/1.06    (![A:$i,B:$i,C:$i]:
% 0.87/1.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.87/1.06       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.87/1.06  thf('54', plain,
% 0.87/1.06      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.87/1.06         ((v5_relat_1 @ X19 @ X21)
% 0.87/1.06          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.87/1.06      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.87/1.06  thf('55', plain,
% 0.87/1.06      (![X0 : $i, X1 : $i]: (v5_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X0)),
% 0.87/1.06      inference('sup-', [status(thm)], ['53', '54'])).
% 0.87/1.06  thf(d19_relat_1, axiom,
% 0.87/1.06    (![A:$i,B:$i]:
% 0.87/1.06     ( ( v1_relat_1 @ B ) =>
% 0.87/1.06       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.87/1.06  thf('56', plain,
% 0.87/1.06      (![X13 : $i, X14 : $i]:
% 0.87/1.06         (~ (v5_relat_1 @ X13 @ X14)
% 0.87/1.06          | (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 0.87/1.06          | ~ (v1_relat_1 @ X13))),
% 0.87/1.06      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.87/1.06  thf('57', plain,
% 0.87/1.06      (![X0 : $i, X1 : $i]:
% 0.87/1.06         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.87/1.06          | (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0))),
% 0.87/1.06      inference('sup-', [status(thm)], ['55', '56'])).
% 0.87/1.06  thf('58', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.87/1.06      inference('sup-', [status(thm)], ['30', '31'])).
% 0.87/1.06  thf(cc1_relset_1, axiom,
% 0.87/1.06    (![A:$i,B:$i,C:$i]:
% 0.87/1.06     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.87/1.06       ( v1_relat_1 @ C ) ))).
% 0.87/1.06  thf('59', plain,
% 0.87/1.06      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.87/1.06         ((v1_relat_1 @ X16)
% 0.87/1.06          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.87/1.06      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.87/1.06  thf('60', plain,
% 0.87/1.06      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 0.87/1.06      inference('sup-', [status(thm)], ['58', '59'])).
% 0.87/1.06  thf('61', plain,
% 0.87/1.06      (![X0 : $i, X1 : $i]:
% 0.87/1.06         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X0)),
% 0.87/1.06      inference('demod', [status(thm)], ['57', '60'])).
% 0.87/1.06  thf(t4_subset_1, axiom,
% 0.87/1.06    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.87/1.06  thf('62', plain,
% 0.87/1.06      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.87/1.06      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.87/1.06  thf('63', plain,
% 0.87/1.06      (![X4 : $i, X5 : $i]:
% 0.87/1.06         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.87/1.06      inference('cnf', [status(esa)], [t3_subset])).
% 0.87/1.06  thf('64', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.87/1.06      inference('sup-', [status(thm)], ['62', '63'])).
% 0.87/1.06  thf('65', plain,
% 0.87/1.06      (![X0 : $i, X2 : $i]:
% 0.87/1.06         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.87/1.06      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.87/1.06  thf('66', plain,
% 0.87/1.06      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.87/1.06      inference('sup-', [status(thm)], ['64', '65'])).
% 0.87/1.06  thf('67', plain,
% 0.87/1.06      (![X0 : $i]:
% 0.87/1.06         ((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.87/1.06      inference('sup-', [status(thm)], ['61', '66'])).
% 0.87/1.06  thf(t64_relat_1, axiom,
% 0.87/1.06    (![A:$i]:
% 0.87/1.06     ( ( v1_relat_1 @ A ) =>
% 0.87/1.06       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.87/1.06           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.87/1.06         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.87/1.06  thf('68', plain,
% 0.87/1.06      (![X15 : $i]:
% 0.87/1.06         (((k2_relat_1 @ X15) != (k1_xboole_0))
% 0.87/1.06          | ((X15) = (k1_xboole_0))
% 0.87/1.06          | ~ (v1_relat_1 @ X15))),
% 0.87/1.06      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.87/1.06  thf('69', plain,
% 0.87/1.06      (![X0 : $i]:
% 0.87/1.06         (((k1_xboole_0) != (k1_xboole_0))
% 0.87/1.06          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 0.87/1.06          | ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.87/1.06      inference('sup-', [status(thm)], ['67', '68'])).
% 0.87/1.06  thf('70', plain,
% 0.87/1.06      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 0.87/1.06      inference('sup-', [status(thm)], ['58', '59'])).
% 0.87/1.06  thf('71', plain,
% 0.87/1.06      (![X0 : $i]:
% 0.87/1.06         (((k1_xboole_0) != (k1_xboole_0))
% 0.87/1.06          | ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.87/1.06      inference('demod', [status(thm)], ['69', '70'])).
% 0.87/1.06  thf('72', plain,
% 0.87/1.06      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.87/1.06      inference('simplify', [status(thm)], ['71'])).
% 0.87/1.06  thf('73', plain,
% 0.87/1.06      (![X0 : $i, X1 : $i]:
% 0.87/1.06         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.87/1.06      inference('sup+', [status(thm)], ['52', '72'])).
% 0.87/1.06  thf('74', plain,
% 0.87/1.06      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('75', plain,
% 0.87/1.06      (![X4 : $i, X5 : $i]:
% 0.87/1.06         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.87/1.06      inference('cnf', [status(esa)], [t3_subset])).
% 0.87/1.06  thf('76', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.87/1.06      inference('sup-', [status(thm)], ['74', '75'])).
% 0.87/1.06  thf('77', plain,
% 0.87/1.06      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.87/1.06      inference('sup-', [status(thm)], ['28', '34'])).
% 0.87/1.06  thf('78', plain,
% 0.87/1.06      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.87/1.06      inference('sup-', [status(thm)], ['64', '65'])).
% 0.87/1.06  thf('79', plain,
% 0.87/1.06      (![X0 : $i, X1 : $i]:
% 0.87/1.06         (~ (r1_tarski @ X1 @ X0)
% 0.87/1.06          | ~ (v1_xboole_0 @ X0)
% 0.87/1.06          | ((X1) = (k1_xboole_0)))),
% 0.87/1.06      inference('sup-', [status(thm)], ['77', '78'])).
% 0.87/1.06  thf('80', plain,
% 0.87/1.06      ((((sk_C) = (k1_xboole_0))
% 0.87/1.06        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.87/1.06      inference('sup-', [status(thm)], ['76', '79'])).
% 0.87/1.06  thf('81', plain,
% 0.87/1.06      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.87/1.06        | ~ (v1_xboole_0 @ sk_B_1)
% 0.87/1.06        | ((sk_C) = (k1_xboole_0)))),
% 0.87/1.06      inference('sup-', [status(thm)], ['73', '80'])).
% 0.87/1.06  thf('82', plain,
% 0.87/1.06      (![X0 : $i]:
% 0.87/1.06         (~ (v1_xboole_0 @ X0)
% 0.87/1.06          | ~ (v1_xboole_0 @ X0)
% 0.87/1.06          | ((sk_C) = (k1_xboole_0))
% 0.87/1.06          | ~ (v1_xboole_0 @ sk_B_1))),
% 0.87/1.06      inference('sup-', [status(thm)], ['51', '81'])).
% 0.87/1.06  thf('83', plain,
% 0.87/1.06      (![X0 : $i]:
% 0.87/1.06         (~ (v1_xboole_0 @ sk_B_1)
% 0.87/1.06          | ((sk_C) = (k1_xboole_0))
% 0.87/1.06          | ~ (v1_xboole_0 @ X0))),
% 0.87/1.06      inference('simplify', [status(thm)], ['82'])).
% 0.87/1.06  thf('84', plain, ((~ (v1_xboole_0 @ sk_B_1) | ((sk_C) = (k1_xboole_0)))),
% 0.87/1.06      inference('condensation', [status(thm)], ['83'])).
% 0.87/1.06  thf('85', plain, ((((sk_C) = (sk_D)) | ((sk_C) = (k1_xboole_0)))),
% 0.87/1.06      inference('sup-', [status(thm)], ['50', '84'])).
% 0.87/1.06  thf('86', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('87', plain,
% 0.87/1.06      ((~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_C)
% 0.87/1.06        | ((sk_C) = (k1_xboole_0)))),
% 0.87/1.06      inference('sup-', [status(thm)], ['85', '86'])).
% 0.87/1.06  thf('88', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_C)),
% 0.87/1.06      inference('sup-', [status(thm)], ['42', '44'])).
% 0.87/1.06  thf('89', plain, (((sk_C) = (k1_xboole_0))),
% 0.87/1.06      inference('demod', [status(thm)], ['87', '88'])).
% 0.87/1.06  thf('90', plain,
% 0.87/1.06      (~ (r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ sk_D)),
% 0.87/1.06      inference('demod', [status(thm)], ['49', '89'])).
% 0.87/1.06  thf('91', plain, ((((sk_C) = (sk_D)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.87/1.06      inference('sup-', [status(thm)], ['27', '35'])).
% 0.87/1.06  thf('92', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_C) = (sk_D)))),
% 0.87/1.06      inference('clc', [status(thm)], ['20', '26'])).
% 0.87/1.06  thf('93', plain,
% 0.87/1.06      (((v1_xboole_0 @ k1_xboole_0) | ((sk_C) = (sk_D)) | ((sk_C) = (sk_D)))),
% 0.87/1.06      inference('sup+', [status(thm)], ['91', '92'])).
% 0.87/1.06  thf('94', plain, ((((sk_C) = (sk_D)) | (v1_xboole_0 @ k1_xboole_0))),
% 0.87/1.06      inference('simplify', [status(thm)], ['93'])).
% 0.87/1.06  thf('95', plain, (((sk_C) = (k1_xboole_0))),
% 0.87/1.06      inference('demod', [status(thm)], ['87', '88'])).
% 0.87/1.06  thf('96', plain, ((((k1_xboole_0) = (sk_D)) | (v1_xboole_0 @ k1_xboole_0))),
% 0.87/1.06      inference('demod', [status(thm)], ['94', '95'])).
% 0.87/1.06  thf('97', plain, ((((sk_C) = (sk_D)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.87/1.06      inference('sup-', [status(thm)], ['27', '35'])).
% 0.87/1.06  thf('98', plain,
% 0.87/1.06      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.87/1.06      inference('split', [status(esa)], ['0'])).
% 0.87/1.06  thf('99', plain,
% 0.87/1.06      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.87/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.06  thf('100', plain,
% 0.87/1.06      (((m1_subset_1 @ sk_D @ 
% 0.87/1.06         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.87/1.06         <= ((((sk_A) = (k1_xboole_0))))),
% 0.87/1.06      inference('sup+', [status(thm)], ['98', '99'])).
% 0.87/1.06  thf('101', plain,
% 0.87/1.06      (![X4 : $i, X5 : $i]:
% 0.87/1.06         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.87/1.06      inference('cnf', [status(esa)], [t3_subset])).
% 0.87/1.06  thf('102', plain,
% 0.87/1.06      (((r1_tarski @ sk_D @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1)))
% 0.87/1.06         <= ((((sk_A) = (k1_xboole_0))))),
% 0.87/1.06      inference('sup-', [status(thm)], ['100', '101'])).
% 0.87/1.06  thf('103', plain,
% 0.87/1.06      (![X0 : $i, X1 : $i]:
% 0.87/1.06         (~ (r1_tarski @ X1 @ X0)
% 0.87/1.06          | ~ (v1_xboole_0 @ X0)
% 0.87/1.06          | ((X1) = (k1_xboole_0)))),
% 0.87/1.06      inference('sup-', [status(thm)], ['77', '78'])).
% 0.87/1.06  thf('104', plain,
% 0.87/1.06      (((((sk_D) = (k1_xboole_0))
% 0.87/1.06         | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.87/1.06         <= ((((sk_A) = (k1_xboole_0))))),
% 0.87/1.06      inference('sup-', [status(thm)], ['102', '103'])).
% 0.87/1.06  thf('105', plain,
% 0.87/1.06      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.87/1.06         | ((sk_C) = (sk_D))
% 0.87/1.06         | ((sk_D) = (k1_xboole_0)))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.87/1.06      inference('sup-', [status(thm)], ['97', '104'])).
% 0.87/1.06  thf('106', plain,
% 0.87/1.06      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.87/1.06      inference('simplify', [status(thm)], ['71'])).
% 0.87/1.06  thf('107', plain,
% 0.87/1.06      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.87/1.06         | ((sk_C) = (sk_D))
% 0.87/1.06         | ((sk_D) = (k1_xboole_0)))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.87/1.06      inference('demod', [status(thm)], ['105', '106'])).
% 0.87/1.06  thf('108', plain, (((sk_C) = (k1_xboole_0))),
% 0.87/1.06      inference('demod', [status(thm)], ['87', '88'])).
% 0.87/1.06  thf('109', plain,
% 0.87/1.06      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.87/1.06         | ((k1_xboole_0) = (sk_D))
% 0.87/1.06         | ((sk_D) = (k1_xboole_0)))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.87/1.06      inference('demod', [status(thm)], ['107', '108'])).
% 0.87/1.06  thf('110', plain,
% 0.87/1.06      (((((k1_xboole_0) = (sk_D)) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.87/1.06         <= ((((sk_A) = (k1_xboole_0))))),
% 0.87/1.06      inference('simplify', [status(thm)], ['109'])).
% 0.87/1.06  thf('111', plain, ((((sk_A) = (k1_xboole_0)))),
% 0.87/1.06      inference('sat_resolution*', [status(thm)], ['46', '47'])).
% 0.87/1.06  thf('112', plain,
% 0.87/1.06      ((((k1_xboole_0) = (sk_D)) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.87/1.06      inference('simpl_trail', [status(thm)], ['110', '111'])).
% 0.87/1.06  thf('113', plain, (((k1_xboole_0) = (sk_D))),
% 0.87/1.06      inference('clc', [status(thm)], ['96', '112'])).
% 0.87/1.06  thf('114', plain,
% 0.87/1.06      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.87/1.06      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.87/1.06  thf('115', plain,
% 0.87/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.87/1.06         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.87/1.06          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.87/1.06      inference('condensation', [status(thm)], ['43'])).
% 0.87/1.06  thf('116', plain,
% 0.87/1.06      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.87/1.06      inference('sup-', [status(thm)], ['114', '115'])).
% 0.87/1.06  thf('117', plain, ($false),
% 0.87/1.06      inference('demod', [status(thm)], ['90', '113', '116'])).
% 0.87/1.06  
% 0.87/1.06  % SZS output end Refutation
% 0.87/1.06  
% 0.87/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
