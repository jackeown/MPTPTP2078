%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N70pICwXkG

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:40 EST 2020

% Result     : Theorem 17.49s
% Output     : Refutation 17.49s
% Verified   : 
% Statistics : Number of formulae       :  236 (1561 expanded)
%              Number of leaves         :   37 ( 473 expanded)
%              Depth                    :   33
%              Number of atoms          : 1978 (23011 expanded)
%              Number of equality atoms :  103 ( 971 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

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

thf('12',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X14 ) ) )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('20',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('21',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('28',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('32',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('33',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('39',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('43',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X31: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('46',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X13 ) ) )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['36','57'])).

thf('59',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['39','40'])).

thf('60',plain,(
    ! [X31: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('61',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('66',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_relat_1 @ sk_C ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','66'])).

thf('68',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['35','67'])).

thf('69',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( sk_C = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ( sk_C
      = ( k2_funct_1 @ sk_C ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_C ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k1_relat_1 @ X7 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('79',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ sk_C ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['39','40'])).

thf('81',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('82',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('89',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('90',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X0 @ X2 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['87','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('95',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( ( k1_relset_1 @ X1 @ X0 @ X2 )
        = ( k1_relat_1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25
       != ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ X1 @ X2 )
      | ( v1_funct_2 @ X0 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( zip_tseitin_1 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['93','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('105',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( X1 = X2 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( sk_C = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('110',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ X0 @ sk_B @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['108','112'])).

thf('114',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_C ) )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('117',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('118',plain,
    ( ( ~ ( v1_funct_2 @ sk_C @ sk_B @ sk_A )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ sk_C @ X0 @ sk_A )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ~ ( v1_xboole_0 @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['115','118'])).

thf('120',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ~ ( v1_funct_2 @ sk_C @ X0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ sk_C )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['103','120'])).

thf('122',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['84','121'])).

thf('123',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ sk_C )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_xboole_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_xboole_0 @ sk_B )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( v1_xboole_0 @ sk_A ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','123'])).

thf('125',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ sk_B )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('128',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('129',plain,(
    ! [X23: $i] :
      ( zip_tseitin_0 @ X23 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['127','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X0 @ X2 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['126','132'])).

thf('134',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('135',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X13 ) ) )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('138',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['135','138'])).

thf('140',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_xboole_0 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['125','139'])).

thf('141',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('142',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k1_relat_1 @ X7 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('144',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('145',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('146',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('147',plain,(
    ! [X31: $i] :
      ( ( v1_funct_2 @ X31 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['145','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['144','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['143','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['142','154'])).

thf('156',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['39','40'])).

thf('157',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['155','156','157','158','159'])).

thf('161',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['11','160'])).

thf('162',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('163',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','161','162'])).

thf('164',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','163'])).

thf('165',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k1_relat_1 @ X7 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('166',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['39','40'])).

thf('167',plain,(
    ! [X6: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('168',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('169',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('170',plain,(
    ! [X31: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['168','171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['167','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['166','175'])).

thf('177',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('178',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['176','177','178','179'])).

thf('181',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['165','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['36','57'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('184',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('185',plain,
    ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['182','185'])).

thf('187',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('188',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('190',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['10','161','162'])).

thf('192',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['190','191'])).

thf('193',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('194',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['181','192','193','194','195'])).

thf('197',plain,(
    $false ),
    inference(demod,[status(thm)],['164','196'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N70pICwXkG
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:44:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 17.49/17.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 17.49/17.70  % Solved by: fo/fo7.sh
% 17.49/17.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.49/17.70  % done 10950 iterations in 17.250s
% 17.49/17.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 17.49/17.70  % SZS output start Refutation
% 17.49/17.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 17.49/17.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 17.49/17.70  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 17.49/17.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 17.49/17.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 17.49/17.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 17.49/17.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 17.49/17.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 17.49/17.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 17.49/17.70  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 17.49/17.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 17.49/17.70  thf(sk_B_type, type, sk_B: $i).
% 17.49/17.70  thf(sk_A_type, type, sk_A: $i).
% 17.49/17.70  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 17.49/17.70  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 17.49/17.70  thf(sk_C_type, type, sk_C: $i).
% 17.49/17.70  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 17.49/17.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 17.49/17.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 17.49/17.70  thf(t31_funct_2, conjecture,
% 17.49/17.70    (![A:$i,B:$i,C:$i]:
% 17.49/17.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 17.49/17.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 17.49/17.70       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 17.49/17.70         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 17.49/17.70           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 17.49/17.70           ( m1_subset_1 @
% 17.49/17.70             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 17.49/17.70  thf(zf_stmt_0, negated_conjecture,
% 17.49/17.70    (~( ![A:$i,B:$i,C:$i]:
% 17.49/17.70        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 17.49/17.70            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 17.49/17.70          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 17.49/17.70            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 17.49/17.70              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 17.49/17.70              ( m1_subset_1 @
% 17.49/17.70                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 17.49/17.70    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 17.49/17.70  thf('0', plain,
% 17.49/17.70      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 17.49/17.70        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 17.49/17.70        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 17.49/17.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 17.49/17.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.49/17.70  thf('1', plain,
% 17.49/17.70      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 17.49/17.70           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 17.49/17.70         <= (~
% 17.49/17.70             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 17.49/17.70               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 17.49/17.70      inference('split', [status(esa)], ['0'])).
% 17.49/17.70  thf('2', plain,
% 17.49/17.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.49/17.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.49/17.70  thf(cc1_relset_1, axiom,
% 17.49/17.70    (![A:$i,B:$i,C:$i]:
% 17.49/17.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.49/17.70       ( v1_relat_1 @ C ) ))).
% 17.49/17.70  thf('3', plain,
% 17.49/17.70      (![X8 : $i, X9 : $i, X10 : $i]:
% 17.49/17.70         ((v1_relat_1 @ X8)
% 17.49/17.70          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 17.49/17.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 17.49/17.70  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 17.49/17.70      inference('sup-', [status(thm)], ['2', '3'])).
% 17.49/17.70  thf(dt_k2_funct_1, axiom,
% 17.49/17.70    (![A:$i]:
% 17.49/17.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 17.49/17.70       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 17.49/17.70         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 17.49/17.70  thf('5', plain,
% 17.49/17.70      (![X6 : $i]:
% 17.49/17.70         ((v1_funct_1 @ (k2_funct_1 @ X6))
% 17.49/17.70          | ~ (v1_funct_1 @ X6)
% 17.49/17.70          | ~ (v1_relat_1 @ X6))),
% 17.49/17.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 17.49/17.70  thf('6', plain,
% 17.49/17.70      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 17.49/17.70         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 17.49/17.70      inference('split', [status(esa)], ['0'])).
% 17.49/17.70  thf('7', plain,
% 17.49/17.70      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 17.49/17.70         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 17.49/17.70      inference('sup-', [status(thm)], ['5', '6'])).
% 17.49/17.70  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 17.49/17.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.49/17.70  thf('9', plain,
% 17.49/17.70      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 17.49/17.70      inference('demod', [status(thm)], ['7', '8'])).
% 17.49/17.70  thf('10', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 17.49/17.70      inference('sup-', [status(thm)], ['4', '9'])).
% 17.49/17.70  thf('11', plain,
% 17.49/17.70      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 17.49/17.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 17.49/17.70      inference('split', [status(esa)], ['0'])).
% 17.49/17.70  thf(d1_funct_2, axiom,
% 17.49/17.70    (![A:$i,B:$i,C:$i]:
% 17.49/17.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.49/17.70       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 17.49/17.70           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 17.49/17.70             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 17.49/17.70         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 17.49/17.70           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 17.49/17.70             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 17.49/17.70  thf(zf_stmt_1, axiom,
% 17.49/17.70    (![B:$i,A:$i]:
% 17.49/17.70     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 17.49/17.70       ( zip_tseitin_0 @ B @ A ) ))).
% 17.49/17.70  thf('12', plain,
% 17.49/17.70      (![X23 : $i, X24 : $i]:
% 17.49/17.70         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 17.49/17.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 17.49/17.70  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 17.49/17.70  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 17.49/17.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 17.49/17.70  thf('14', plain,
% 17.49/17.70      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 17.49/17.70      inference('sup+', [status(thm)], ['12', '13'])).
% 17.49/17.70  thf('15', plain,
% 17.49/17.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.49/17.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.49/17.70  thf(cc4_relset_1, axiom,
% 17.49/17.70    (![A:$i,B:$i]:
% 17.49/17.70     ( ( v1_xboole_0 @ A ) =>
% 17.49/17.70       ( ![C:$i]:
% 17.49/17.70         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 17.49/17.70           ( v1_xboole_0 @ C ) ) ) ))).
% 17.49/17.70  thf('16', plain,
% 17.49/17.70      (![X14 : $i, X15 : $i, X16 : $i]:
% 17.49/17.70         (~ (v1_xboole_0 @ X14)
% 17.49/17.70          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X14)))
% 17.49/17.70          | (v1_xboole_0 @ X15))),
% 17.49/17.70      inference('cnf', [status(esa)], [cc4_relset_1])).
% 17.49/17.70  thf('17', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_B))),
% 17.49/17.70      inference('sup-', [status(thm)], ['15', '16'])).
% 17.49/17.70  thf('18', plain,
% 17.49/17.70      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_C))),
% 17.49/17.70      inference('sup-', [status(thm)], ['14', '17'])).
% 17.49/17.70  thf('19', plain,
% 17.49/17.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.49/17.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.49/17.70  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 17.49/17.70  thf(zf_stmt_3, axiom,
% 17.49/17.70    (![C:$i,B:$i,A:$i]:
% 17.49/17.70     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 17.49/17.70       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 17.49/17.70  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 17.49/17.70  thf(zf_stmt_5, axiom,
% 17.49/17.70    (![A:$i,B:$i,C:$i]:
% 17.49/17.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.49/17.70       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 17.49/17.70         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 17.49/17.70           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 17.49/17.70             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 17.49/17.70  thf('20', plain,
% 17.49/17.70      (![X28 : $i, X29 : $i, X30 : $i]:
% 17.49/17.70         (~ (zip_tseitin_0 @ X28 @ X29)
% 17.49/17.70          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 17.49/17.70          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 17.49/17.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 17.49/17.70  thf('21', plain,
% 17.49/17.70      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 17.49/17.70      inference('sup-', [status(thm)], ['19', '20'])).
% 17.49/17.70  thf('22', plain,
% 17.49/17.70      (((v1_xboole_0 @ sk_C) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 17.49/17.70      inference('sup-', [status(thm)], ['18', '21'])).
% 17.49/17.70  thf('23', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 17.49/17.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.49/17.70  thf('24', plain,
% 17.49/17.70      (![X25 : $i, X26 : $i, X27 : $i]:
% 17.49/17.70         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 17.49/17.70          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 17.49/17.70          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 17.49/17.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 17.49/17.70  thf('25', plain,
% 17.49/17.70      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 17.49/17.70        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 17.49/17.70      inference('sup-', [status(thm)], ['23', '24'])).
% 17.49/17.70  thf('26', plain,
% 17.49/17.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.49/17.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.49/17.70  thf(redefinition_k1_relset_1, axiom,
% 17.49/17.70    (![A:$i,B:$i,C:$i]:
% 17.49/17.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.49/17.70       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 17.49/17.70  thf('27', plain,
% 17.49/17.70      (![X17 : $i, X18 : $i, X19 : $i]:
% 17.49/17.70         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 17.49/17.70          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 17.49/17.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 17.49/17.70  thf('28', plain,
% 17.49/17.70      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 17.49/17.70      inference('sup-', [status(thm)], ['26', '27'])).
% 17.49/17.70  thf('29', plain,
% 17.49/17.70      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 17.49/17.70      inference('demod', [status(thm)], ['25', '28'])).
% 17.49/17.70  thf('30', plain, (((v1_xboole_0 @ sk_C) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 17.49/17.70      inference('sup-', [status(thm)], ['22', '29'])).
% 17.49/17.70  thf('31', plain,
% 17.49/17.70      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 17.49/17.70      inference('sup+', [status(thm)], ['12', '13'])).
% 17.49/17.70  thf('32', plain,
% 17.49/17.70      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 17.49/17.70      inference('sup-', [status(thm)], ['19', '20'])).
% 17.49/17.70  thf('33', plain,
% 17.49/17.70      (((v1_xboole_0 @ sk_B) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 17.49/17.70      inference('sup-', [status(thm)], ['31', '32'])).
% 17.49/17.70  thf('34', plain,
% 17.49/17.70      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 17.49/17.70      inference('demod', [status(thm)], ['25', '28'])).
% 17.49/17.70  thf('35', plain, (((v1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 17.49/17.70      inference('sup-', [status(thm)], ['33', '34'])).
% 17.49/17.70  thf('36', plain,
% 17.49/17.70      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 17.49/17.70      inference('sup+', [status(thm)], ['12', '13'])).
% 17.49/17.70  thf('37', plain,
% 17.49/17.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.49/17.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.49/17.70  thf(redefinition_k2_relset_1, axiom,
% 17.49/17.70    (![A:$i,B:$i,C:$i]:
% 17.49/17.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.49/17.70       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 17.49/17.70  thf('38', plain,
% 17.49/17.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 17.49/17.70         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 17.49/17.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 17.49/17.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 17.49/17.70  thf('39', plain,
% 17.49/17.70      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 17.49/17.70      inference('sup-', [status(thm)], ['37', '38'])).
% 17.49/17.70  thf('40', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 17.49/17.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.49/17.70  thf('41', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 17.49/17.70      inference('sup+', [status(thm)], ['39', '40'])).
% 17.49/17.70  thf('42', plain,
% 17.49/17.70      (![X6 : $i]:
% 17.49/17.70         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 17.49/17.70          | ~ (v1_funct_1 @ X6)
% 17.49/17.70          | ~ (v1_relat_1 @ X6))),
% 17.49/17.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 17.49/17.70  thf('43', plain,
% 17.49/17.70      (![X6 : $i]:
% 17.49/17.70         ((v1_funct_1 @ (k2_funct_1 @ X6))
% 17.49/17.70          | ~ (v1_funct_1 @ X6)
% 17.49/17.70          | ~ (v1_relat_1 @ X6))),
% 17.49/17.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 17.49/17.70  thf(t55_funct_1, axiom,
% 17.49/17.70    (![A:$i]:
% 17.49/17.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 17.49/17.70       ( ( v2_funct_1 @ A ) =>
% 17.49/17.70         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 17.49/17.70           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 17.49/17.70  thf('44', plain,
% 17.49/17.70      (![X7 : $i]:
% 17.49/17.70         (~ (v2_funct_1 @ X7)
% 17.49/17.70          | ((k2_relat_1 @ X7) = (k1_relat_1 @ (k2_funct_1 @ X7)))
% 17.49/17.70          | ~ (v1_funct_1 @ X7)
% 17.49/17.70          | ~ (v1_relat_1 @ X7))),
% 17.49/17.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 17.49/17.70  thf(t3_funct_2, axiom,
% 17.49/17.70    (![A:$i]:
% 17.49/17.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 17.49/17.70       ( ( v1_funct_1 @ A ) & 
% 17.49/17.70         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 17.49/17.70         ( m1_subset_1 @
% 17.49/17.70           A @ 
% 17.49/17.70           ( k1_zfmisc_1 @
% 17.49/17.70             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 17.49/17.70  thf('45', plain,
% 17.49/17.70      (![X31 : $i]:
% 17.49/17.70         ((m1_subset_1 @ X31 @ 
% 17.49/17.70           (k1_zfmisc_1 @ 
% 17.49/17.70            (k2_zfmisc_1 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))))
% 17.49/17.70          | ~ (v1_funct_1 @ X31)
% 17.49/17.70          | ~ (v1_relat_1 @ X31))),
% 17.49/17.70      inference('cnf', [status(esa)], [t3_funct_2])).
% 17.49/17.70  thf(cc3_relset_1, axiom,
% 17.49/17.70    (![A:$i,B:$i]:
% 17.49/17.70     ( ( v1_xboole_0 @ A ) =>
% 17.49/17.70       ( ![C:$i]:
% 17.49/17.70         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 17.49/17.70           ( v1_xboole_0 @ C ) ) ) ))).
% 17.49/17.70  thf('46', plain,
% 17.49/17.70      (![X11 : $i, X12 : $i, X13 : $i]:
% 17.49/17.70         (~ (v1_xboole_0 @ X11)
% 17.49/17.70          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X13)))
% 17.49/17.70          | (v1_xboole_0 @ X12))),
% 17.49/17.70      inference('cnf', [status(esa)], [cc3_relset_1])).
% 17.49/17.70  thf('47', plain,
% 17.49/17.70      (![X0 : $i]:
% 17.49/17.70         (~ (v1_relat_1 @ X0)
% 17.49/17.70          | ~ (v1_funct_1 @ X0)
% 17.49/17.70          | (v1_xboole_0 @ X0)
% 17.49/17.70          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 17.49/17.70      inference('sup-', [status(thm)], ['45', '46'])).
% 17.49/17.70  thf('48', plain,
% 17.49/17.70      (![X0 : $i]:
% 17.49/17.70         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 17.49/17.70          | ~ (v1_relat_1 @ X0)
% 17.49/17.70          | ~ (v1_funct_1 @ X0)
% 17.49/17.70          | ~ (v2_funct_1 @ X0)
% 17.49/17.70          | (v1_xboole_0 @ (k2_funct_1 @ X0))
% 17.49/17.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 17.49/17.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 17.49/17.70      inference('sup-', [status(thm)], ['44', '47'])).
% 17.49/17.70  thf('49', plain,
% 17.49/17.70      (![X0 : $i]:
% 17.49/17.70         (~ (v1_relat_1 @ X0)
% 17.49/17.70          | ~ (v1_funct_1 @ X0)
% 17.49/17.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 17.49/17.70          | (v1_xboole_0 @ (k2_funct_1 @ X0))
% 17.49/17.70          | ~ (v2_funct_1 @ X0)
% 17.49/17.70          | ~ (v1_funct_1 @ X0)
% 17.49/17.70          | ~ (v1_relat_1 @ X0)
% 17.49/17.70          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 17.49/17.70      inference('sup-', [status(thm)], ['43', '48'])).
% 17.49/17.70  thf('50', plain,
% 17.49/17.70      (![X0 : $i]:
% 17.49/17.70         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 17.49/17.70          | ~ (v2_funct_1 @ X0)
% 17.49/17.70          | (v1_xboole_0 @ (k2_funct_1 @ X0))
% 17.49/17.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 17.49/17.70          | ~ (v1_funct_1 @ X0)
% 17.49/17.70          | ~ (v1_relat_1 @ X0))),
% 17.49/17.70      inference('simplify', [status(thm)], ['49'])).
% 17.49/17.70  thf('51', plain,
% 17.49/17.70      (![X0 : $i]:
% 17.49/17.70         (~ (v1_relat_1 @ X0)
% 17.49/17.70          | ~ (v1_funct_1 @ X0)
% 17.49/17.70          | ~ (v1_relat_1 @ X0)
% 17.49/17.70          | ~ (v1_funct_1 @ X0)
% 17.49/17.70          | (v1_xboole_0 @ (k2_funct_1 @ X0))
% 17.49/17.70          | ~ (v2_funct_1 @ X0)
% 17.49/17.70          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 17.49/17.70      inference('sup-', [status(thm)], ['42', '50'])).
% 17.49/17.70  thf('52', plain,
% 17.49/17.70      (![X0 : $i]:
% 17.49/17.70         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 17.49/17.70          | ~ (v2_funct_1 @ X0)
% 17.49/17.70          | (v1_xboole_0 @ (k2_funct_1 @ X0))
% 17.49/17.70          | ~ (v1_funct_1 @ X0)
% 17.49/17.70          | ~ (v1_relat_1 @ X0))),
% 17.49/17.70      inference('simplify', [status(thm)], ['51'])).
% 17.49/17.70  thf('53', plain,
% 17.49/17.70      ((~ (v1_xboole_0 @ sk_B)
% 17.49/17.70        | ~ (v1_relat_1 @ sk_C)
% 17.49/17.70        | ~ (v1_funct_1 @ sk_C)
% 17.49/17.70        | (v1_xboole_0 @ (k2_funct_1 @ sk_C))
% 17.49/17.70        | ~ (v2_funct_1 @ sk_C))),
% 17.49/17.70      inference('sup-', [status(thm)], ['41', '52'])).
% 17.49/17.70  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 17.49/17.70      inference('sup-', [status(thm)], ['2', '3'])).
% 17.49/17.70  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 17.49/17.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.49/17.70  thf('56', plain, ((v2_funct_1 @ sk_C)),
% 17.49/17.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.49/17.70  thf('57', plain,
% 17.49/17.70      ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k2_funct_1 @ sk_C)))),
% 17.49/17.70      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 17.49/17.70  thf('58', plain,
% 17.49/17.70      (![X0 : $i]:
% 17.49/17.70         ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ (k2_funct_1 @ sk_C)))),
% 17.49/17.70      inference('sup-', [status(thm)], ['36', '57'])).
% 17.49/17.70  thf('59', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 17.49/17.70      inference('sup+', [status(thm)], ['39', '40'])).
% 17.49/17.70  thf('60', plain,
% 17.49/17.70      (![X31 : $i]:
% 17.49/17.70         ((m1_subset_1 @ X31 @ 
% 17.49/17.70           (k1_zfmisc_1 @ 
% 17.49/17.70            (k2_zfmisc_1 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))))
% 17.49/17.70          | ~ (v1_funct_1 @ X31)
% 17.49/17.70          | ~ (v1_relat_1 @ X31))),
% 17.49/17.70      inference('cnf', [status(esa)], [t3_funct_2])).
% 17.49/17.70  thf('61', plain,
% 17.49/17.70      (((m1_subset_1 @ sk_C @ 
% 17.49/17.70         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))
% 17.49/17.70        | ~ (v1_relat_1 @ sk_C)
% 17.49/17.70        | ~ (v1_funct_1 @ sk_C))),
% 17.49/17.70      inference('sup+', [status(thm)], ['59', '60'])).
% 17.49/17.70  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 17.49/17.70      inference('sup-', [status(thm)], ['2', '3'])).
% 17.49/17.70  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 17.49/17.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.49/17.70  thf('64', plain,
% 17.49/17.70      ((m1_subset_1 @ sk_C @ 
% 17.49/17.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 17.49/17.70      inference('demod', [status(thm)], ['61', '62', '63'])).
% 17.49/17.70  thf('65', plain,
% 17.49/17.70      (![X28 : $i, X29 : $i, X30 : $i]:
% 17.49/17.70         (~ (zip_tseitin_0 @ X28 @ X29)
% 17.49/17.70          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 17.49/17.70          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 17.49/17.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 17.49/17.70  thf('66', plain,
% 17.49/17.70      (((zip_tseitin_1 @ sk_C @ sk_B @ (k1_relat_1 @ sk_C))
% 17.49/17.70        | ~ (zip_tseitin_0 @ sk_B @ (k1_relat_1 @ sk_C)))),
% 17.49/17.70      inference('sup-', [status(thm)], ['64', '65'])).
% 17.49/17.70  thf('67', plain,
% 17.49/17.70      (((v1_xboole_0 @ (k2_funct_1 @ sk_C))
% 17.49/17.70        | (zip_tseitin_1 @ sk_C @ sk_B @ (k1_relat_1 @ sk_C)))),
% 17.49/17.70      inference('sup-', [status(thm)], ['58', '66'])).
% 17.49/17.70  thf('68', plain,
% 17.49/17.70      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 17.49/17.70        | (v1_xboole_0 @ sk_B)
% 17.49/17.70        | (v1_xboole_0 @ (k2_funct_1 @ sk_C)))),
% 17.49/17.70      inference('sup+', [status(thm)], ['35', '67'])).
% 17.49/17.70  thf('69', plain,
% 17.49/17.70      ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ (k2_funct_1 @ sk_C)))),
% 17.49/17.70      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 17.49/17.70  thf('70', plain,
% 17.49/17.70      (((v1_xboole_0 @ (k2_funct_1 @ sk_C))
% 17.49/17.70        | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 17.49/17.70      inference('clc', [status(thm)], ['68', '69'])).
% 17.49/17.70  thf('71', plain,
% 17.49/17.70      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 17.49/17.70      inference('demod', [status(thm)], ['25', '28'])).
% 17.49/17.70  thf('72', plain,
% 17.49/17.70      (((v1_xboole_0 @ (k2_funct_1 @ sk_C)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 17.49/17.70      inference('sup-', [status(thm)], ['70', '71'])).
% 17.49/17.70  thf('73', plain, (((v1_xboole_0 @ sk_C) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 17.49/17.70      inference('sup-', [status(thm)], ['22', '29'])).
% 17.49/17.70  thf(t8_boole, axiom,
% 17.49/17.70    (![A:$i,B:$i]:
% 17.49/17.70     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 17.49/17.70  thf('74', plain,
% 17.49/17.70      (![X0 : $i, X1 : $i]:
% 17.49/17.70         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 17.49/17.70      inference('cnf', [status(esa)], [t8_boole])).
% 17.49/17.70  thf('75', plain,
% 17.49/17.70      (![X0 : $i]:
% 17.49/17.70         (((sk_A) = (k1_relat_1 @ sk_C))
% 17.49/17.70          | ((sk_C) = (X0))
% 17.49/17.70          | ~ (v1_xboole_0 @ X0))),
% 17.49/17.70      inference('sup-', [status(thm)], ['73', '74'])).
% 17.49/17.70  thf('76', plain,
% 17.49/17.70      ((((sk_A) = (k1_relat_1 @ sk_C))
% 17.49/17.70        | ((sk_C) = (k2_funct_1 @ sk_C))
% 17.49/17.70        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 17.49/17.70      inference('sup-', [status(thm)], ['72', '75'])).
% 17.49/17.70  thf('77', plain,
% 17.49/17.70      ((((sk_C) = (k2_funct_1 @ sk_C)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 17.49/17.70      inference('simplify', [status(thm)], ['76'])).
% 17.49/17.70  thf('78', plain,
% 17.49/17.70      (![X7 : $i]:
% 17.49/17.70         (~ (v2_funct_1 @ X7)
% 17.49/17.70          | ((k1_relat_1 @ X7) = (k2_relat_1 @ (k2_funct_1 @ X7)))
% 17.49/17.70          | ~ (v1_funct_1 @ X7)
% 17.49/17.70          | ~ (v1_relat_1 @ X7))),
% 17.49/17.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 17.49/17.70  thf('79', plain,
% 17.49/17.70      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ sk_C))
% 17.49/17.70        | ((sk_A) = (k1_relat_1 @ sk_C))
% 17.49/17.70        | ~ (v1_relat_1 @ sk_C)
% 17.49/17.70        | ~ (v1_funct_1 @ sk_C)
% 17.49/17.70        | ~ (v2_funct_1 @ sk_C))),
% 17.49/17.70      inference('sup+', [status(thm)], ['77', '78'])).
% 17.49/17.70  thf('80', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 17.49/17.70      inference('sup+', [status(thm)], ['39', '40'])).
% 17.49/17.70  thf('81', plain, ((v1_relat_1 @ sk_C)),
% 17.49/17.70      inference('sup-', [status(thm)], ['2', '3'])).
% 17.49/17.70  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 17.49/17.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.49/17.70  thf('83', plain, ((v2_funct_1 @ sk_C)),
% 17.49/17.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.49/17.70  thf('84', plain,
% 17.49/17.70      ((((k1_relat_1 @ sk_C) = (sk_B)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 17.49/17.70      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 17.49/17.70  thf('85', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 17.49/17.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 17.49/17.70  thf('86', plain,
% 17.49/17.70      (![X0 : $i, X1 : $i]:
% 17.49/17.70         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 17.49/17.70      inference('cnf', [status(esa)], [t8_boole])).
% 17.49/17.70  thf('87', plain,
% 17.49/17.70      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 17.49/17.70      inference('sup-', [status(thm)], ['85', '86'])).
% 17.49/17.70  thf('88', plain,
% 17.49/17.70      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 17.49/17.70      inference('sup+', [status(thm)], ['12', '13'])).
% 17.49/17.70  thf(t4_subset_1, axiom,
% 17.49/17.70    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 17.49/17.70  thf('89', plain,
% 17.49/17.70      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 17.49/17.70      inference('cnf', [status(esa)], [t4_subset_1])).
% 17.49/17.70  thf('90', plain,
% 17.49/17.70      (![X28 : $i, X29 : $i, X30 : $i]:
% 17.49/17.70         (~ (zip_tseitin_0 @ X28 @ X29)
% 17.49/17.70          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 17.49/17.70          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 17.49/17.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 17.49/17.70  thf('91', plain,
% 17.49/17.70      (![X0 : $i, X1 : $i]:
% 17.49/17.70         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 17.49/17.70      inference('sup-', [status(thm)], ['89', '90'])).
% 17.49/17.70  thf('92', plain,
% 17.49/17.70      (![X0 : $i, X1 : $i]:
% 17.49/17.70         ((v1_xboole_0 @ X1) | (zip_tseitin_1 @ k1_xboole_0 @ X1 @ X0))),
% 17.49/17.70      inference('sup-', [status(thm)], ['88', '91'])).
% 17.49/17.70  thf('93', plain,
% 17.49/17.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.49/17.70         ((zip_tseitin_1 @ X0 @ X2 @ X1)
% 17.49/17.70          | ~ (v1_xboole_0 @ X0)
% 17.49/17.70          | (v1_xboole_0 @ X2))),
% 17.49/17.70      inference('sup+', [status(thm)], ['87', '92'])).
% 17.49/17.70  thf('94', plain,
% 17.49/17.70      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 17.49/17.70      inference('sup-', [status(thm)], ['85', '86'])).
% 17.49/17.70  thf('95', plain,
% 17.49/17.70      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 17.49/17.70      inference('cnf', [status(esa)], [t4_subset_1])).
% 17.49/17.70  thf('96', plain,
% 17.49/17.70      (![X0 : $i, X1 : $i]:
% 17.49/17.70         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 17.49/17.70      inference('sup+', [status(thm)], ['94', '95'])).
% 17.49/17.70  thf('97', plain,
% 17.49/17.70      (![X17 : $i, X18 : $i, X19 : $i]:
% 17.49/17.70         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 17.49/17.70          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 17.49/17.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 17.49/17.70  thf('98', plain,
% 17.49/17.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.49/17.70         (~ (v1_xboole_0 @ X2)
% 17.49/17.70          | ((k1_relset_1 @ X1 @ X0 @ X2) = (k1_relat_1 @ X2)))),
% 17.49/17.70      inference('sup-', [status(thm)], ['96', '97'])).
% 17.49/17.70  thf('99', plain,
% 17.49/17.70      (![X25 : $i, X26 : $i, X27 : $i]:
% 17.49/17.70         (((X25) != (k1_relset_1 @ X25 @ X26 @ X27))
% 17.49/17.70          | (v1_funct_2 @ X27 @ X25 @ X26)
% 17.49/17.70          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 17.49/17.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 17.49/17.70  thf('100', plain,
% 17.49/17.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.49/17.70         (((X2) != (k1_relat_1 @ X0))
% 17.49/17.70          | ~ (v1_xboole_0 @ X0)
% 17.49/17.70          | ~ (zip_tseitin_1 @ X0 @ X1 @ X2)
% 17.49/17.70          | (v1_funct_2 @ X0 @ X2 @ X1))),
% 17.49/17.70      inference('sup-', [status(thm)], ['98', '99'])).
% 17.49/17.70  thf('101', plain,
% 17.49/17.70      (![X0 : $i, X1 : $i]:
% 17.49/17.70         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ X1)
% 17.49/17.70          | ~ (zip_tseitin_1 @ X0 @ X1 @ (k1_relat_1 @ X0))
% 17.49/17.70          | ~ (v1_xboole_0 @ X0))),
% 17.49/17.70      inference('simplify', [status(thm)], ['100'])).
% 17.49/17.70  thf('102', plain,
% 17.49/17.70      (![X0 : $i, X1 : $i]:
% 17.49/17.70         ((v1_xboole_0 @ X1)
% 17.49/17.70          | ~ (v1_xboole_0 @ X0)
% 17.49/17.70          | ~ (v1_xboole_0 @ X0)
% 17.49/17.70          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ X1))),
% 17.49/17.70      inference('sup-', [status(thm)], ['93', '101'])).
% 17.49/17.70  thf('103', plain,
% 17.49/17.70      (![X0 : $i, X1 : $i]:
% 17.49/17.70         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ X1)
% 17.49/17.70          | ~ (v1_xboole_0 @ X0)
% 17.49/17.70          | (v1_xboole_0 @ X1))),
% 17.49/17.70      inference('simplify', [status(thm)], ['102'])).
% 17.49/17.70  thf('104', plain,
% 17.49/17.70      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 17.49/17.70      inference('sup-', [status(thm)], ['85', '86'])).
% 17.49/17.70  thf('105', plain,
% 17.49/17.70      (![X23 : $i, X24 : $i]:
% 17.49/17.70         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 17.49/17.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 17.49/17.70  thf('106', plain,
% 17.49/17.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.49/17.70         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | (zip_tseitin_0 @ X1 @ X2))),
% 17.49/17.70      inference('sup+', [status(thm)], ['104', '105'])).
% 17.49/17.70  thf('107', plain,
% 17.49/17.70      (![X0 : $i, X1 : $i]:
% 17.49/17.70         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 17.49/17.70      inference('sup-', [status(thm)], ['89', '90'])).
% 17.49/17.70  thf('108', plain,
% 17.49/17.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.49/17.70         (~ (v1_xboole_0 @ X2)
% 17.49/17.70          | ((X1) = (X2))
% 17.49/17.70          | (zip_tseitin_1 @ k1_xboole_0 @ X1 @ X0))),
% 17.49/17.70      inference('sup-', [status(thm)], ['106', '107'])).
% 17.49/17.70  thf('109', plain,
% 17.49/17.70      (![X0 : $i]:
% 17.49/17.70         (((sk_A) = (k1_relat_1 @ sk_C))
% 17.49/17.70          | ((sk_C) = (X0))
% 17.49/17.70          | ~ (v1_xboole_0 @ X0))),
% 17.49/17.70      inference('sup-', [status(thm)], ['73', '74'])).
% 17.49/17.70  thf('110', plain,
% 17.49/17.70      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 17.49/17.70      inference('demod', [status(thm)], ['25', '28'])).
% 17.49/17.70  thf('111', plain,
% 17.49/17.70      (![X0 : $i]:
% 17.49/17.70         (~ (zip_tseitin_1 @ X0 @ sk_B @ sk_A)
% 17.49/17.70          | ~ (v1_xboole_0 @ X0)
% 17.49/17.70          | ((sk_A) = (k1_relat_1 @ sk_C))
% 17.49/17.70          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 17.49/17.70      inference('sup-', [status(thm)], ['109', '110'])).
% 17.49/17.70  thf('112', plain,
% 17.49/17.70      (![X0 : $i]:
% 17.49/17.70         (((sk_A) = (k1_relat_1 @ sk_C))
% 17.49/17.70          | ~ (v1_xboole_0 @ X0)
% 17.49/17.70          | ~ (zip_tseitin_1 @ X0 @ sk_B @ sk_A))),
% 17.49/17.70      inference('simplify', [status(thm)], ['111'])).
% 17.49/17.70  thf('113', plain,
% 17.49/17.70      (![X0 : $i]:
% 17.49/17.70         (((sk_B) = (X0))
% 17.49/17.70          | ~ (v1_xboole_0 @ X0)
% 17.49/17.70          | ~ (v1_xboole_0 @ k1_xboole_0)
% 17.49/17.70          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 17.49/17.70      inference('sup-', [status(thm)], ['108', '112'])).
% 17.49/17.70  thf('114', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 17.49/17.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 17.49/17.70  thf('115', plain,
% 17.49/17.70      (![X0 : $i]:
% 17.49/17.70         (((sk_B) = (X0))
% 17.49/17.70          | ~ (v1_xboole_0 @ X0)
% 17.49/17.70          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 17.49/17.70      inference('demod', [status(thm)], ['113', '114'])).
% 17.49/17.70  thf('116', plain,
% 17.49/17.70      ((((sk_C) = (k2_funct_1 @ sk_C)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 17.49/17.70      inference('simplify', [status(thm)], ['76'])).
% 17.49/17.70  thf('117', plain,
% 17.49/17.70      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 17.49/17.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 17.49/17.70      inference('split', [status(esa)], ['0'])).
% 17.49/17.70  thf('118', plain,
% 17.49/17.70      (((~ (v1_funct_2 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C))))
% 17.49/17.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 17.49/17.70      inference('sup-', [status(thm)], ['116', '117'])).
% 17.49/17.70  thf('119', plain,
% 17.49/17.70      ((![X0 : $i]:
% 17.49/17.70          (~ (v1_funct_2 @ sk_C @ X0 @ sk_A)
% 17.49/17.70           | ((sk_A) = (k1_relat_1 @ sk_C))
% 17.49/17.70           | ~ (v1_xboole_0 @ X0)
% 17.49/17.70           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 17.49/17.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 17.49/17.70      inference('sup-', [status(thm)], ['115', '118'])).
% 17.49/17.70  thf('120', plain,
% 17.49/17.70      ((![X0 : $i]:
% 17.49/17.70          (~ (v1_xboole_0 @ X0)
% 17.49/17.70           | ((sk_A) = (k1_relat_1 @ sk_C))
% 17.49/17.70           | ~ (v1_funct_2 @ sk_C @ X0 @ sk_A)))
% 17.49/17.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 17.49/17.70      inference('simplify', [status(thm)], ['119'])).
% 17.49/17.70  thf('121', plain,
% 17.49/17.70      ((((v1_xboole_0 @ sk_A)
% 17.49/17.70         | ~ (v1_xboole_0 @ sk_C)
% 17.49/17.70         | ((sk_A) = (k1_relat_1 @ sk_C))
% 17.49/17.70         | ~ (v1_xboole_0 @ (k1_relat_1 @ sk_C))))
% 17.49/17.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 17.49/17.70      inference('sup-', [status(thm)], ['103', '120'])).
% 17.49/17.70  thf('122', plain,
% 17.49/17.70      (((~ (v1_xboole_0 @ sk_B)
% 17.49/17.70         | ((sk_A) = (k1_relat_1 @ sk_C))
% 17.49/17.70         | ((sk_A) = (k1_relat_1 @ sk_C))
% 17.49/17.70         | ~ (v1_xboole_0 @ sk_C)
% 17.49/17.70         | (v1_xboole_0 @ sk_A)))
% 17.49/17.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 17.49/17.70      inference('sup-', [status(thm)], ['84', '121'])).
% 17.49/17.70  thf('123', plain,
% 17.49/17.70      ((((v1_xboole_0 @ sk_A)
% 17.49/17.70         | ~ (v1_xboole_0 @ sk_C)
% 17.49/17.70         | ((sk_A) = (k1_relat_1 @ sk_C))
% 17.49/17.70         | ~ (v1_xboole_0 @ sk_B)))
% 17.49/17.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 17.49/17.70      inference('simplify', [status(thm)], ['122'])).
% 17.49/17.70  thf('124', plain,
% 17.49/17.70      (((((sk_A) = (k1_relat_1 @ sk_C))
% 17.49/17.70         | ~ (v1_xboole_0 @ sk_B)
% 17.49/17.70         | ((sk_A) = (k1_relat_1 @ sk_C))
% 17.49/17.70         | (v1_xboole_0 @ sk_A)))
% 17.49/17.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 17.49/17.70      inference('sup-', [status(thm)], ['30', '123'])).
% 17.49/17.70  thf('125', plain,
% 17.49/17.70      ((((v1_xboole_0 @ sk_A)
% 17.49/17.70         | ~ (v1_xboole_0 @ sk_B)
% 17.49/17.70         | ((sk_A) = (k1_relat_1 @ sk_C))))
% 17.49/17.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 17.49/17.70      inference('simplify', [status(thm)], ['124'])).
% 17.49/17.70  thf('126', plain,
% 17.49/17.70      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 17.49/17.70      inference('sup-', [status(thm)], ['85', '86'])).
% 17.49/17.70  thf('127', plain,
% 17.49/17.70      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 17.49/17.70      inference('sup-', [status(thm)], ['85', '86'])).
% 17.49/17.70  thf('128', plain,
% 17.49/17.70      (![X23 : $i, X24 : $i]:
% 17.49/17.70         ((zip_tseitin_0 @ X23 @ X24) | ((X24) != (k1_xboole_0)))),
% 17.49/17.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 17.49/17.70  thf('129', plain, (![X23 : $i]: (zip_tseitin_0 @ X23 @ k1_xboole_0)),
% 17.49/17.70      inference('simplify', [status(thm)], ['128'])).
% 17.49/17.70  thf('130', plain,
% 17.49/17.70      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 17.49/17.70      inference('sup+', [status(thm)], ['127', '129'])).
% 17.49/17.70  thf('131', plain,
% 17.49/17.70      (![X0 : $i, X1 : $i]:
% 17.49/17.70         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 17.49/17.70      inference('sup-', [status(thm)], ['89', '90'])).
% 17.49/17.70  thf('132', plain,
% 17.49/17.70      (![X0 : $i, X1 : $i]:
% 17.49/17.70         (~ (v1_xboole_0 @ X0) | (zip_tseitin_1 @ k1_xboole_0 @ X1 @ X0))),
% 17.49/17.70      inference('sup-', [status(thm)], ['130', '131'])).
% 17.49/17.70  thf('133', plain,
% 17.49/17.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.49/17.70         ((zip_tseitin_1 @ X0 @ X2 @ X1)
% 17.49/17.70          | ~ (v1_xboole_0 @ X0)
% 17.49/17.70          | ~ (v1_xboole_0 @ X1))),
% 17.49/17.70      inference('sup+', [status(thm)], ['126', '132'])).
% 17.49/17.70  thf('134', plain,
% 17.49/17.70      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 17.49/17.70      inference('demod', [status(thm)], ['25', '28'])).
% 17.49/17.70  thf('135', plain,
% 17.49/17.70      ((~ (v1_xboole_0 @ sk_A)
% 17.49/17.70        | ~ (v1_xboole_0 @ sk_C)
% 17.49/17.70        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 17.49/17.70      inference('sup-', [status(thm)], ['133', '134'])).
% 17.49/17.70  thf('136', plain,
% 17.49/17.70      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 17.49/17.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.49/17.70  thf('137', plain,
% 17.49/17.70      (![X11 : $i, X12 : $i, X13 : $i]:
% 17.49/17.70         (~ (v1_xboole_0 @ X11)
% 17.49/17.70          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X13)))
% 17.49/17.70          | (v1_xboole_0 @ X12))),
% 17.49/17.70      inference('cnf', [status(esa)], [cc3_relset_1])).
% 17.49/17.70  thf('138', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 17.49/17.70      inference('sup-', [status(thm)], ['136', '137'])).
% 17.49/17.70  thf('139', plain,
% 17.49/17.70      ((((sk_A) = (k1_relat_1 @ sk_C)) | ~ (v1_xboole_0 @ sk_A))),
% 17.49/17.70      inference('clc', [status(thm)], ['135', '138'])).
% 17.49/17.70  thf('140', plain,
% 17.49/17.70      (((((sk_A) = (k1_relat_1 @ sk_C)) | ~ (v1_xboole_0 @ sk_B)))
% 17.49/17.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 17.49/17.70      inference('clc', [status(thm)], ['125', '139'])).
% 17.49/17.70  thf('141', plain, (((v1_xboole_0 @ sk_B) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 17.49/17.70      inference('sup-', [status(thm)], ['33', '34'])).
% 17.49/17.70  thf('142', plain,
% 17.49/17.70      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 17.49/17.70         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 17.49/17.70      inference('clc', [status(thm)], ['140', '141'])).
% 17.49/17.70  thf('143', plain,
% 17.49/17.70      (![X7 : $i]:
% 17.49/17.70         (~ (v2_funct_1 @ X7)
% 17.49/17.70          | ((k1_relat_1 @ X7) = (k2_relat_1 @ (k2_funct_1 @ X7)))
% 17.49/17.70          | ~ (v1_funct_1 @ X7)
% 17.49/17.70          | ~ (v1_relat_1 @ X7))),
% 17.49/17.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 17.49/17.70  thf('144', plain,
% 17.49/17.70      (![X6 : $i]:
% 17.49/17.70         ((v1_funct_1 @ (k2_funct_1 @ X6))
% 17.49/17.70          | ~ (v1_funct_1 @ X6)
% 17.49/17.70          | ~ (v1_relat_1 @ X6))),
% 17.49/17.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 17.49/17.70  thf('145', plain,
% 17.49/17.70      (![X6 : $i]:
% 17.49/17.70         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 17.49/17.70          | ~ (v1_funct_1 @ X6)
% 17.49/17.70          | ~ (v1_relat_1 @ X6))),
% 17.49/17.70      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 17.49/17.70  thf('146', plain,
% 17.49/17.70      (![X7 : $i]:
% 17.49/17.70         (~ (v2_funct_1 @ X7)
% 17.49/17.70          | ((k2_relat_1 @ X7) = (k1_relat_1 @ (k2_funct_1 @ X7)))
% 17.49/17.70          | ~ (v1_funct_1 @ X7)
% 17.49/17.70          | ~ (v1_relat_1 @ X7))),
% 17.49/17.70      inference('cnf', [status(esa)], [t55_funct_1])).
% 17.49/17.70  thf('147', plain,
% 17.49/17.70      (![X31 : $i]:
% 17.49/17.70         ((v1_funct_2 @ X31 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))
% 17.49/17.70          | ~ (v1_funct_1 @ X31)
% 17.49/17.70          | ~ (v1_relat_1 @ X31))),
% 17.49/17.70      inference('cnf', [status(esa)], [t3_funct_2])).
% 17.49/17.70  thf('148', plain,
% 17.49/17.70      (![X0 : $i]:
% 17.49/17.70         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 17.49/17.70           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 17.49/17.70          | ~ (v1_relat_1 @ X0)
% 17.49/17.70          | ~ (v1_funct_1 @ X0)
% 17.49/17.70          | ~ (v2_funct_1 @ X0)
% 17.49/17.70          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 17.49/17.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 17.49/17.70      inference('sup+', [status(thm)], ['146', '147'])).
% 17.49/17.70  thf('149', plain,
% 17.49/17.70      (![X0 : $i]:
% 17.49/17.70         (~ (v1_relat_1 @ X0)
% 17.49/17.70          | ~ (v1_funct_1 @ X0)
% 17.49/17.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 17.49/17.70          | ~ (v2_funct_1 @ X0)
% 17.49/17.70          | ~ (v1_funct_1 @ X0)
% 17.49/17.70          | ~ (v1_relat_1 @ X0)
% 17.49/17.70          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 17.49/17.70             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 17.49/17.70      inference('sup-', [status(thm)], ['145', '148'])).
% 17.49/17.70  thf('150', plain,
% 17.49/17.70      (![X0 : $i]:
% 17.49/17.70         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 17.49/17.70           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 17.49/17.70          | ~ (v2_funct_1 @ X0)
% 17.49/17.70          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 17.49/17.70          | ~ (v1_funct_1 @ X0)
% 17.49/17.70          | ~ (v1_relat_1 @ X0))),
% 17.49/17.70      inference('simplify', [status(thm)], ['149'])).
% 17.49/17.70  thf('151', plain,
% 17.49/17.70      (![X0 : $i]:
% 17.49/17.70         (~ (v1_relat_1 @ X0)
% 17.49/17.70          | ~ (v1_funct_1 @ X0)
% 17.49/17.70          | ~ (v1_relat_1 @ X0)
% 17.49/17.70          | ~ (v1_funct_1 @ X0)
% 17.49/17.70          | ~ (v2_funct_1 @ X0)
% 17.49/17.70          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 17.49/17.70             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 17.49/17.70      inference('sup-', [status(thm)], ['144', '150'])).
% 17.49/17.70  thf('152', plain,
% 17.49/17.70      (![X0 : $i]:
% 17.49/17.70         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 17.49/17.70           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 17.49/17.70          | ~ (v2_funct_1 @ X0)
% 17.49/17.70          | ~ (v1_funct_1 @ X0)
% 17.49/17.70          | ~ (v1_relat_1 @ X0))),
% 17.49/17.70      inference('simplify', [status(thm)], ['151'])).
% 17.49/17.70  thf('153', plain,
% 17.49/17.70      (![X0 : $i]:
% 17.49/17.70         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 17.49/17.70           (k1_relat_1 @ X0))
% 17.49/17.70          | ~ (v1_relat_1 @ X0)
% 17.49/17.70          | ~ (v1_funct_1 @ X0)
% 17.49/17.70          | ~ (v2_funct_1 @ X0)
% 17.49/17.70          | ~ (v1_relat_1 @ X0)
% 17.49/17.70          | ~ (v1_funct_1 @ X0)
% 17.49/17.70          | ~ (v2_funct_1 @ X0))),
% 17.49/17.70      inference('sup+', [status(thm)], ['143', '152'])).
% 17.49/17.70  thf('154', plain,
% 17.49/17.70      (![X0 : $i]:
% 17.49/17.70         (~ (v2_funct_1 @ X0)
% 17.49/17.70          | ~ (v1_funct_1 @ X0)
% 17.49/17.70          | ~ (v1_relat_1 @ X0)
% 17.49/17.71          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 17.49/17.71             (k1_relat_1 @ X0)))),
% 17.49/17.71      inference('simplify', [status(thm)], ['153'])).
% 17.49/17.71  thf('155', plain,
% 17.49/17.71      ((((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 17.49/17.71         | ~ (v1_relat_1 @ sk_C)
% 17.49/17.71         | ~ (v1_funct_1 @ sk_C)
% 17.49/17.71         | ~ (v2_funct_1 @ sk_C)))
% 17.49/17.71         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 17.49/17.71      inference('sup+', [status(thm)], ['142', '154'])).
% 17.49/17.71  thf('156', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 17.49/17.71      inference('sup+', [status(thm)], ['39', '40'])).
% 17.49/17.71  thf('157', plain, ((v1_relat_1 @ sk_C)),
% 17.49/17.71      inference('sup-', [status(thm)], ['2', '3'])).
% 17.49/17.71  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 17.49/17.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.49/17.71  thf('159', plain, ((v2_funct_1 @ sk_C)),
% 17.49/17.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.49/17.71  thf('160', plain,
% 17.49/17.71      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 17.49/17.71         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 17.49/17.71      inference('demod', [status(thm)], ['155', '156', '157', '158', '159'])).
% 17.49/17.71  thf('161', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 17.49/17.71      inference('demod', [status(thm)], ['11', '160'])).
% 17.49/17.71  thf('162', plain,
% 17.49/17.71      (~
% 17.49/17.71       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 17.49/17.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 17.49/17.71       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 17.49/17.71       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 17.49/17.71      inference('split', [status(esa)], ['0'])).
% 17.49/17.71  thf('163', plain,
% 17.49/17.71      (~
% 17.49/17.71       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 17.49/17.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 17.49/17.71      inference('sat_resolution*', [status(thm)], ['10', '161', '162'])).
% 17.49/17.71  thf('164', plain,
% 17.49/17.71      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 17.49/17.71          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 17.49/17.71      inference('simpl_trail', [status(thm)], ['1', '163'])).
% 17.49/17.71  thf('165', plain,
% 17.49/17.71      (![X7 : $i]:
% 17.49/17.71         (~ (v2_funct_1 @ X7)
% 17.49/17.71          | ((k1_relat_1 @ X7) = (k2_relat_1 @ (k2_funct_1 @ X7)))
% 17.49/17.71          | ~ (v1_funct_1 @ X7)
% 17.49/17.71          | ~ (v1_relat_1 @ X7))),
% 17.49/17.71      inference('cnf', [status(esa)], [t55_funct_1])).
% 17.49/17.71  thf('166', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 17.49/17.71      inference('sup+', [status(thm)], ['39', '40'])).
% 17.49/17.71  thf('167', plain,
% 17.49/17.71      (![X6 : $i]:
% 17.49/17.71         ((v1_funct_1 @ (k2_funct_1 @ X6))
% 17.49/17.71          | ~ (v1_funct_1 @ X6)
% 17.49/17.71          | ~ (v1_relat_1 @ X6))),
% 17.49/17.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 17.49/17.71  thf('168', plain,
% 17.49/17.71      (![X6 : $i]:
% 17.49/17.71         ((v1_relat_1 @ (k2_funct_1 @ X6))
% 17.49/17.71          | ~ (v1_funct_1 @ X6)
% 17.49/17.71          | ~ (v1_relat_1 @ X6))),
% 17.49/17.71      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 17.49/17.71  thf('169', plain,
% 17.49/17.71      (![X7 : $i]:
% 17.49/17.71         (~ (v2_funct_1 @ X7)
% 17.49/17.71          | ((k2_relat_1 @ X7) = (k1_relat_1 @ (k2_funct_1 @ X7)))
% 17.49/17.71          | ~ (v1_funct_1 @ X7)
% 17.49/17.71          | ~ (v1_relat_1 @ X7))),
% 17.49/17.71      inference('cnf', [status(esa)], [t55_funct_1])).
% 17.49/17.71  thf('170', plain,
% 17.49/17.71      (![X31 : $i]:
% 17.49/17.71         ((m1_subset_1 @ X31 @ 
% 17.49/17.71           (k1_zfmisc_1 @ 
% 17.49/17.71            (k2_zfmisc_1 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))))
% 17.49/17.71          | ~ (v1_funct_1 @ X31)
% 17.49/17.71          | ~ (v1_relat_1 @ X31))),
% 17.49/17.71      inference('cnf', [status(esa)], [t3_funct_2])).
% 17.49/17.71  thf('171', plain,
% 17.49/17.71      (![X0 : $i]:
% 17.49/17.71         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 17.49/17.71           (k1_zfmisc_1 @ 
% 17.49/17.71            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 17.49/17.71          | ~ (v1_relat_1 @ X0)
% 17.49/17.71          | ~ (v1_funct_1 @ X0)
% 17.49/17.71          | ~ (v2_funct_1 @ X0)
% 17.49/17.71          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 17.49/17.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 17.49/17.71      inference('sup+', [status(thm)], ['169', '170'])).
% 17.49/17.71  thf('172', plain,
% 17.49/17.71      (![X0 : $i]:
% 17.49/17.71         (~ (v1_relat_1 @ X0)
% 17.49/17.71          | ~ (v1_funct_1 @ X0)
% 17.49/17.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 17.49/17.71          | ~ (v2_funct_1 @ X0)
% 17.49/17.71          | ~ (v1_funct_1 @ X0)
% 17.49/17.71          | ~ (v1_relat_1 @ X0)
% 17.49/17.71          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 17.49/17.71             (k1_zfmisc_1 @ 
% 17.49/17.71              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 17.49/17.71               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 17.49/17.71      inference('sup-', [status(thm)], ['168', '171'])).
% 17.49/17.71  thf('173', plain,
% 17.49/17.71      (![X0 : $i]:
% 17.49/17.71         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 17.49/17.71           (k1_zfmisc_1 @ 
% 17.49/17.71            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 17.49/17.71          | ~ (v2_funct_1 @ X0)
% 17.49/17.71          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 17.49/17.71          | ~ (v1_funct_1 @ X0)
% 17.49/17.71          | ~ (v1_relat_1 @ X0))),
% 17.49/17.71      inference('simplify', [status(thm)], ['172'])).
% 17.49/17.71  thf('174', plain,
% 17.49/17.71      (![X0 : $i]:
% 17.49/17.71         (~ (v1_relat_1 @ X0)
% 17.49/17.71          | ~ (v1_funct_1 @ X0)
% 17.49/17.71          | ~ (v1_relat_1 @ X0)
% 17.49/17.71          | ~ (v1_funct_1 @ X0)
% 17.49/17.71          | ~ (v2_funct_1 @ X0)
% 17.49/17.71          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 17.49/17.71             (k1_zfmisc_1 @ 
% 17.49/17.71              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 17.49/17.71               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 17.49/17.71      inference('sup-', [status(thm)], ['167', '173'])).
% 17.49/17.71  thf('175', plain,
% 17.49/17.71      (![X0 : $i]:
% 17.49/17.71         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 17.49/17.71           (k1_zfmisc_1 @ 
% 17.49/17.71            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 17.49/17.71          | ~ (v2_funct_1 @ X0)
% 17.49/17.71          | ~ (v1_funct_1 @ X0)
% 17.49/17.71          | ~ (v1_relat_1 @ X0))),
% 17.49/17.71      inference('simplify', [status(thm)], ['174'])).
% 17.49/17.71  thf('176', plain,
% 17.49/17.71      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 17.49/17.71         (k1_zfmisc_1 @ 
% 17.49/17.71          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 17.49/17.71        | ~ (v1_relat_1 @ sk_C)
% 17.49/17.71        | ~ (v1_funct_1 @ sk_C)
% 17.49/17.71        | ~ (v2_funct_1 @ sk_C))),
% 17.49/17.71      inference('sup+', [status(thm)], ['166', '175'])).
% 17.49/17.71  thf('177', plain, ((v1_relat_1 @ sk_C)),
% 17.49/17.71      inference('sup-', [status(thm)], ['2', '3'])).
% 17.49/17.71  thf('178', plain, ((v1_funct_1 @ sk_C)),
% 17.49/17.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.49/17.71  thf('179', plain, ((v2_funct_1 @ sk_C)),
% 17.49/17.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.49/17.71  thf('180', plain,
% 17.49/17.71      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 17.49/17.71        (k1_zfmisc_1 @ 
% 17.49/17.71         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 17.49/17.71      inference('demod', [status(thm)], ['176', '177', '178', '179'])).
% 17.49/17.71  thf('181', plain,
% 17.49/17.71      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 17.49/17.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))
% 17.49/17.71        | ~ (v1_relat_1 @ sk_C)
% 17.49/17.71        | ~ (v1_funct_1 @ sk_C)
% 17.49/17.71        | ~ (v2_funct_1 @ sk_C))),
% 17.49/17.71      inference('sup+', [status(thm)], ['165', '180'])).
% 17.49/17.71  thf('182', plain,
% 17.49/17.71      (![X0 : $i]:
% 17.49/17.71         ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ (k2_funct_1 @ sk_C)))),
% 17.49/17.71      inference('sup-', [status(thm)], ['36', '57'])).
% 17.49/17.71  thf('183', plain,
% 17.49/17.71      (![X0 : $i, X1 : $i]:
% 17.49/17.71         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 17.49/17.71      inference('sup+', [status(thm)], ['94', '95'])).
% 17.49/17.71  thf('184', plain,
% 17.49/17.71      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 17.49/17.71           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 17.49/17.71         <= (~
% 17.49/17.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 17.49/17.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 17.49/17.71      inference('split', [status(esa)], ['0'])).
% 17.49/17.71  thf('185', plain,
% 17.49/17.71      ((~ (v1_xboole_0 @ (k2_funct_1 @ sk_C)))
% 17.49/17.71         <= (~
% 17.49/17.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 17.49/17.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 17.49/17.71      inference('sup-', [status(thm)], ['183', '184'])).
% 17.49/17.71  thf('186', plain,
% 17.49/17.71      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 17.49/17.71         <= (~
% 17.49/17.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 17.49/17.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 17.49/17.71      inference('sup-', [status(thm)], ['182', '185'])).
% 17.49/17.71  thf('187', plain,
% 17.49/17.71      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 17.49/17.71      inference('sup-', [status(thm)], ['19', '20'])).
% 17.49/17.71  thf('188', plain,
% 17.49/17.71      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A))
% 17.49/17.71         <= (~
% 17.49/17.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 17.49/17.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 17.49/17.71      inference('sup-', [status(thm)], ['186', '187'])).
% 17.49/17.71  thf('189', plain,
% 17.49/17.71      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 17.49/17.71      inference('demod', [status(thm)], ['25', '28'])).
% 17.49/17.71  thf('190', plain,
% 17.49/17.71      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 17.49/17.71         <= (~
% 17.49/17.71             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 17.49/17.71               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 17.49/17.71      inference('sup-', [status(thm)], ['188', '189'])).
% 17.49/17.71  thf('191', plain,
% 17.49/17.71      (~
% 17.49/17.71       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 17.49/17.71         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 17.49/17.71      inference('sat_resolution*', [status(thm)], ['10', '161', '162'])).
% 17.49/17.71  thf('192', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 17.49/17.71      inference('simpl_trail', [status(thm)], ['190', '191'])).
% 17.49/17.71  thf('193', plain, ((v1_relat_1 @ sk_C)),
% 17.49/17.71      inference('sup-', [status(thm)], ['2', '3'])).
% 17.49/17.71  thf('194', plain, ((v1_funct_1 @ sk_C)),
% 17.49/17.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.49/17.71  thf('195', plain, ((v2_funct_1 @ sk_C)),
% 17.49/17.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.49/17.71  thf('196', plain,
% 17.49/17.71      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 17.49/17.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 17.49/17.71      inference('demod', [status(thm)], ['181', '192', '193', '194', '195'])).
% 17.49/17.71  thf('197', plain, ($false), inference('demod', [status(thm)], ['164', '196'])).
% 17.49/17.71  
% 17.49/17.71  % SZS output end Refutation
% 17.49/17.71  
% 17.49/17.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
