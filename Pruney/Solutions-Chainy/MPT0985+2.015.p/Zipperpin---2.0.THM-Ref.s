%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fwLsW8mGus

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:29 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  207 (1349 expanded)
%              Number of leaves         :   47 ( 426 expanded)
%              Depth                    :   21
%              Number of atoms          : 1360 (19826 expanded)
%              Number of equality atoms :   78 ( 762 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

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
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ X10 )
        = ( k4_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('19',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X32 ) @ X33 )
      | ( v1_funct_2 @ X32 @ ( k1_relat_1 @ X32 ) @ X33 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('22',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t45_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf('23',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('24',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('25',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf('27',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

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

thf('29',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('32',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('36',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('39',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('42',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','46'])).

thf('48',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['36','47'])).

thf('49',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['33','48'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('50',plain,(
    ! [X31: $i] :
      ( ( v1_funct_2 @ X31 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('51',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('53',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('54',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('60',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('61',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('65',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('66',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('67',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('69',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('72',plain,(
    ! [X11: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('73',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('75',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','64','70','76'])).

thf('78',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('79',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('80',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['27','28','81'])).

thf('83',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('84',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['61','62'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('85',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('86',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('88',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('90',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('91',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('92',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('93',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('95',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ X10 )
        = ( k4_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('96',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k2_funct_1 @ k1_xboole_0 )
      = ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v2_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('98',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf(cc2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) ) ) )).

thf('99',plain,(
    ! [X9: $i] :
      ( ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_1])).

thf('100',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( v2_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('102',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('103',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','97','103'])).

thf('105',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k1_relat_1 @ X12 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('106',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k2_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v2_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('108',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('109',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('110',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('111',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['106','107','108','109','110'])).

thf('112',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('113',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('115',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','97','103'])).

thf('116',plain,(
    ! [X11: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('117',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('119',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('120',plain,(
    v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    v1_xboole_0 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['113','114','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('123',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['82','93','123'])).

thf('125',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['26','124'])).

thf('126',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('127',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['18','125','126'])).

thf('128',plain,(
    ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['11','127'])).

thf('129',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('130',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf(fc14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) )
        & ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ) )).

thf('134',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ ( k4_relat_1 @ X6 ) )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc14_relat_1])).

thf('135',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('137',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('139',plain,(
    ! [X2: $i,X4: $i] :
      ( ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('142',plain,
    ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ~ ( v1_xboole_0 @ ( k4_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['135','142'])).

thf('144',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['134','143'])).

thf('145',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['133','144'])).

thf('146',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('147',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['36','47'])).

thf('149',plain,
    ( ( sk_A
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X31: $i] :
      ( ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X31 ) @ ( k2_relat_1 @ X31 ) ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('151',plain,
    ( ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A ) ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('153',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('154',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('155',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['151','152','153','154'])).

thf('156',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['18','125','126'])).

thf('157',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['155','156'])).

thf('158',plain,(
    $false ),
    inference(demod,[status(thm)],['128','157'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fwLsW8mGus
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.72  % Solved by: fo/fo7.sh
% 0.49/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.72  % done 411 iterations in 0.264s
% 0.49/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.72  % SZS output start Refutation
% 0.49/0.72  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.49/0.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.49/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.49/0.72  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.49/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.49/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.72  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.49/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.72  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.49/0.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.49/0.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.49/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.72  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 0.49/0.72  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.49/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.49/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.72  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.49/0.72  thf(t31_funct_2, conjecture,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.49/0.72         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.49/0.72       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.49/0.72         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.49/0.72           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.49/0.72           ( m1_subset_1 @
% 0.49/0.72             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.49/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.72    (~( ![A:$i,B:$i,C:$i]:
% 0.49/0.72        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.49/0.72            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.49/0.72          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.49/0.72            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.49/0.72              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.49/0.72              ( m1_subset_1 @
% 0.49/0.72                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.49/0.72    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.49/0.72  thf('0', plain,
% 0.49/0.72      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.49/0.72        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.49/0.72        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.72             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('1', plain,
% 0.49/0.72      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.49/0.72         <= (~
% 0.49/0.72             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.72               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.49/0.72      inference('split', [status(esa)], ['0'])).
% 0.49/0.72  thf('2', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(d9_funct_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.72       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.49/0.72  thf('3', plain,
% 0.49/0.72      (![X10 : $i]:
% 0.49/0.72         (~ (v2_funct_1 @ X10)
% 0.49/0.72          | ((k2_funct_1 @ X10) = (k4_relat_1 @ X10))
% 0.49/0.72          | ~ (v1_funct_1 @ X10)
% 0.49/0.72          | ~ (v1_relat_1 @ X10))),
% 0.49/0.72      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.49/0.72  thf('4', plain,
% 0.49/0.72      ((~ (v1_relat_1 @ sk_C)
% 0.49/0.72        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.49/0.72        | ~ (v2_funct_1 @ sk_C))),
% 0.49/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.49/0.72  thf('5', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('6', plain,
% 0.49/0.72      ((~ (v1_relat_1 @ sk_C) | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C)))),
% 0.49/0.72      inference('demod', [status(thm)], ['4', '5'])).
% 0.49/0.72  thf('7', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(cc1_relset_1, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.72       ( v1_relat_1 @ C ) ))).
% 0.49/0.72  thf('8', plain,
% 0.49/0.72      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.49/0.72         ((v1_relat_1 @ X14)
% 0.49/0.72          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.49/0.72      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.49/0.72  thf('9', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.49/0.72  thf('10', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.49/0.72      inference('demod', [status(thm)], ['6', '9'])).
% 0.49/0.72  thf('11', plain,
% 0.49/0.72      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.49/0.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.49/0.72         <= (~
% 0.49/0.72             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.72               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.49/0.72      inference('demod', [status(thm)], ['1', '10'])).
% 0.49/0.72  thf('12', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.49/0.72  thf(dt_k2_funct_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.72       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.49/0.72         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.49/0.72  thf('13', plain,
% 0.49/0.72      (![X11 : $i]:
% 0.49/0.72         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 0.49/0.72          | ~ (v1_funct_1 @ X11)
% 0.49/0.72          | ~ (v1_relat_1 @ X11))),
% 0.49/0.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.49/0.72  thf('14', plain,
% 0.49/0.72      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.49/0.72         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.49/0.72      inference('split', [status(esa)], ['0'])).
% 0.49/0.72  thf('15', plain,
% 0.49/0.72      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 0.49/0.72         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['13', '14'])).
% 0.49/0.72  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('17', plain,
% 0.49/0.72      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.49/0.72      inference('demod', [status(thm)], ['15', '16'])).
% 0.49/0.72  thf('18', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['12', '17'])).
% 0.49/0.72  thf(t60_relat_1, axiom,
% 0.49/0.72    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.49/0.72     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.49/0.72  thf('19', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.72      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.49/0.72  thf(t4_funct_2, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.49/0.72       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.49/0.72         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.49/0.72           ( m1_subset_1 @
% 0.49/0.72             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.49/0.72  thf('20', plain,
% 0.49/0.72      (![X32 : $i, X33 : $i]:
% 0.49/0.72         (~ (r1_tarski @ (k2_relat_1 @ X32) @ X33)
% 0.49/0.72          | (v1_funct_2 @ X32 @ (k1_relat_1 @ X32) @ X33)
% 0.49/0.72          | ~ (v1_funct_1 @ X32)
% 0.49/0.72          | ~ (v1_relat_1 @ X32))),
% 0.49/0.72      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.49/0.72  thf('21', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.49/0.72          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.49/0.72          | ~ (v1_funct_1 @ k1_xboole_0)
% 0.49/0.72          | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['19', '20'])).
% 0.49/0.72  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.49/0.72  thf('22', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.49/0.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.49/0.72  thf(t45_ordinal1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 0.49/0.72       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 0.49/0.72  thf('23', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.49/0.72  thf('24', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.49/0.72  thf('25', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.72      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.49/0.72  thf('26', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.49/0.72      inference('demod', [status(thm)], ['21', '22', '23', '24', '25'])).
% 0.49/0.72  thf('27', plain,
% 0.49/0.72      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.49/0.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.49/0.72      inference('split', [status(esa)], ['0'])).
% 0.49/0.72  thf('28', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.49/0.72      inference('demod', [status(thm)], ['6', '9'])).
% 0.49/0.72  thf(d1_funct_2, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.72       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.49/0.72           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.49/0.72             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.49/0.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.49/0.72           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.49/0.72             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.49/0.72  thf(zf_stmt_1, axiom,
% 0.49/0.72    (![B:$i,A:$i]:
% 0.49/0.72     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.49/0.72       ( zip_tseitin_0 @ B @ A ) ))).
% 0.49/0.72  thf('29', plain,
% 0.49/0.72      (![X23 : $i, X24 : $i]:
% 0.49/0.72         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.49/0.72  thf('30', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.49/0.72  thf(zf_stmt_3, axiom,
% 0.49/0.72    (![C:$i,B:$i,A:$i]:
% 0.49/0.72     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.49/0.72       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.49/0.72  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.49/0.72  thf(zf_stmt_5, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.72       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.49/0.72         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.49/0.72           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.49/0.72             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.49/0.72  thf('31', plain,
% 0.49/0.72      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.49/0.72         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.49/0.72          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.49/0.72          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.49/0.72  thf('32', plain,
% 0.49/0.72      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['30', '31'])).
% 0.49/0.72  thf('33', plain,
% 0.49/0.72      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['29', '32'])).
% 0.49/0.72  thf('34', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('35', plain,
% 0.49/0.72      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.49/0.72         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.49/0.72          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 0.49/0.72          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.49/0.72  thf('36', plain,
% 0.49/0.72      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.49/0.72        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['34', '35'])).
% 0.49/0.72  thf('37', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(redefinition_k1_relset_1, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.72       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.49/0.72  thf('38', plain,
% 0.49/0.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.49/0.72         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.49/0.72          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.49/0.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.49/0.72  thf('39', plain,
% 0.49/0.72      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.49/0.72      inference('sup-', [status(thm)], ['37', '38'])).
% 0.49/0.72  thf('40', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.49/0.72      inference('demod', [status(thm)], ['6', '9'])).
% 0.49/0.72  thf(t55_funct_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.72       ( ( v2_funct_1 @ A ) =>
% 0.49/0.72         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.49/0.72           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.49/0.72  thf('41', plain,
% 0.49/0.72      (![X12 : $i]:
% 0.49/0.72         (~ (v2_funct_1 @ X12)
% 0.49/0.72          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 0.49/0.72          | ~ (v1_funct_1 @ X12)
% 0.49/0.72          | ~ (v1_relat_1 @ X12))),
% 0.49/0.72      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.49/0.72  thf('42', plain,
% 0.49/0.72      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.49/0.72        | ~ (v1_relat_1 @ sk_C)
% 0.49/0.72        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.72        | ~ (v2_funct_1 @ sk_C))),
% 0.49/0.72      inference('sup+', [status(thm)], ['40', '41'])).
% 0.49/0.72  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.49/0.72  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('45', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('46', plain,
% 0.49/0.72      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.49/0.72      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.49/0.72  thf('47', plain,
% 0.49/0.72      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.49/0.72      inference('demod', [status(thm)], ['39', '46'])).
% 0.49/0.72  thf('48', plain,
% 0.49/0.72      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.49/0.72        | ((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C))))),
% 0.49/0.72      inference('demod', [status(thm)], ['36', '47'])).
% 0.49/0.72  thf('49', plain,
% 0.49/0.72      ((((sk_B) = (k1_xboole_0))
% 0.49/0.72        | ((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['33', '48'])).
% 0.49/0.72  thf(t3_funct_2, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.72       ( ( v1_funct_1 @ A ) & 
% 0.49/0.72         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.49/0.72         ( m1_subset_1 @
% 0.49/0.72           A @ 
% 0.49/0.72           ( k1_zfmisc_1 @
% 0.49/0.72             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.49/0.72  thf('50', plain,
% 0.49/0.72      (![X31 : $i]:
% 0.49/0.72         ((v1_funct_2 @ X31 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))
% 0.49/0.72          | ~ (v1_funct_1 @ X31)
% 0.49/0.72          | ~ (v1_relat_1 @ X31))),
% 0.49/0.72      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.49/0.72  thf('51', plain,
% 0.49/0.72      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ 
% 0.49/0.72         (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)
% 0.49/0.72        | ((sk_B) = (k1_xboole_0))
% 0.49/0.72        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.49/0.72        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C)))),
% 0.49/0.72      inference('sup+', [status(thm)], ['49', '50'])).
% 0.49/0.72  thf('52', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.49/0.72      inference('demod', [status(thm)], ['6', '9'])).
% 0.49/0.72  thf('53', plain,
% 0.49/0.72      (![X12 : $i]:
% 0.49/0.72         (~ (v2_funct_1 @ X12)
% 0.49/0.72          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 0.49/0.72          | ~ (v1_funct_1 @ X12)
% 0.49/0.72          | ~ (v1_relat_1 @ X12))),
% 0.49/0.72      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.49/0.72  thf('54', plain,
% 0.49/0.72      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.49/0.72        | ~ (v1_relat_1 @ sk_C)
% 0.49/0.72        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.72        | ~ (v2_funct_1 @ sk_C))),
% 0.49/0.72      inference('sup+', [status(thm)], ['52', '53'])).
% 0.49/0.72  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.49/0.72  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('57', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('58', plain,
% 0.49/0.72      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.49/0.72      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.49/0.72  thf('59', plain,
% 0.49/0.72      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(redefinition_k2_relset_1, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.72       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.49/0.72  thf('60', plain,
% 0.49/0.72      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.49/0.72         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 0.49/0.72          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.49/0.72      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.49/0.72  thf('61', plain,
% 0.49/0.72      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.49/0.72      inference('sup-', [status(thm)], ['59', '60'])).
% 0.49/0.72  thf('62', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('63', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.49/0.72      inference('sup+', [status(thm)], ['61', '62'])).
% 0.49/0.72  thf('64', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.49/0.72      inference('demod', [status(thm)], ['58', '63'])).
% 0.49/0.72  thf('65', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.49/0.72      inference('demod', [status(thm)], ['6', '9'])).
% 0.49/0.72  thf('66', plain,
% 0.49/0.72      (![X11 : $i]:
% 0.49/0.72         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 0.49/0.72          | ~ (v1_funct_1 @ X11)
% 0.49/0.72          | ~ (v1_relat_1 @ X11))),
% 0.49/0.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.49/0.72  thf('67', plain,
% 0.49/0.72      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.49/0.72        | ~ (v1_relat_1 @ sk_C)
% 0.49/0.72        | ~ (v1_funct_1 @ sk_C))),
% 0.49/0.72      inference('sup+', [status(thm)], ['65', '66'])).
% 0.49/0.72  thf('68', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.49/0.72  thf('69', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('70', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.49/0.72      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.49/0.72  thf('71', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.49/0.72      inference('demod', [status(thm)], ['6', '9'])).
% 0.49/0.72  thf('72', plain,
% 0.49/0.72      (![X11 : $i]:
% 0.49/0.72         ((v1_funct_1 @ (k2_funct_1 @ X11))
% 0.49/0.72          | ~ (v1_funct_1 @ X11)
% 0.49/0.72          | ~ (v1_relat_1 @ X11))),
% 0.49/0.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.49/0.72  thf('73', plain,
% 0.49/0.72      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.49/0.72        | ~ (v1_relat_1 @ sk_C)
% 0.49/0.72        | ~ (v1_funct_1 @ sk_C))),
% 0.49/0.72      inference('sup+', [status(thm)], ['71', '72'])).
% 0.49/0.72  thf('74', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.49/0.72  thf('75', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('76', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.49/0.72      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.49/0.72  thf('77', plain,
% 0.49/0.72      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)
% 0.49/0.72        | ((sk_B) = (k1_xboole_0)))),
% 0.49/0.72      inference('demod', [status(thm)], ['51', '64', '70', '76'])).
% 0.49/0.72  thf('78', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.49/0.72      inference('demod', [status(thm)], ['6', '9'])).
% 0.49/0.72  thf('79', plain,
% 0.49/0.72      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.49/0.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.49/0.72      inference('split', [status(esa)], ['0'])).
% 0.49/0.72  thf('80', plain,
% 0.49/0.72      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))
% 0.49/0.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['78', '79'])).
% 0.49/0.72  thf('81', plain,
% 0.49/0.72      ((((sk_B) = (k1_xboole_0)))
% 0.49/0.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['77', '80'])).
% 0.49/0.72  thf('82', plain,
% 0.49/0.72      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 0.49/0.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.49/0.72      inference('demod', [status(thm)], ['27', '28', '81'])).
% 0.49/0.72  thf('83', plain,
% 0.49/0.72      ((((sk_B) = (k1_xboole_0)))
% 0.49/0.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['77', '80'])).
% 0.49/0.72  thf('84', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.49/0.72      inference('sup+', [status(thm)], ['61', '62'])).
% 0.49/0.72  thf(fc9_relat_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.49/0.72       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.49/0.72  thf('85', plain,
% 0.49/0.72      (![X7 : $i]:
% 0.49/0.72         (~ (v1_xboole_0 @ (k2_relat_1 @ X7))
% 0.49/0.72          | ~ (v1_relat_1 @ X7)
% 0.49/0.72          | (v1_xboole_0 @ X7))),
% 0.49/0.72      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.49/0.72  thf('86', plain,
% 0.49/0.72      ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C) | ~ (v1_relat_1 @ sk_C))),
% 0.49/0.72      inference('sup-', [status(thm)], ['84', '85'])).
% 0.49/0.72  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.49/0.72  thf('88', plain, ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C))),
% 0.49/0.72      inference('demod', [status(thm)], ['86', '87'])).
% 0.49/0.72  thf('89', plain,
% 0.49/0.72      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_C)))
% 0.49/0.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['83', '88'])).
% 0.49/0.72  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.49/0.72  thf('90', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.49/0.72  thf('91', plain,
% 0.49/0.72      (((v1_xboole_0 @ sk_C))
% 0.49/0.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.49/0.72      inference('demod', [status(thm)], ['89', '90'])).
% 0.49/0.72  thf(l13_xboole_0, axiom,
% 0.49/0.72    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.49/0.72  thf('92', plain,
% 0.49/0.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.49/0.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.49/0.72  thf('93', plain,
% 0.49/0.72      ((((sk_C) = (k1_xboole_0)))
% 0.49/0.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['91', '92'])).
% 0.49/0.72  thf('94', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.49/0.72  thf('95', plain,
% 0.49/0.72      (![X10 : $i]:
% 0.49/0.72         (~ (v2_funct_1 @ X10)
% 0.49/0.72          | ((k2_funct_1 @ X10) = (k4_relat_1 @ X10))
% 0.49/0.72          | ~ (v1_funct_1 @ X10)
% 0.49/0.72          | ~ (v1_relat_1 @ X10))),
% 0.49/0.72      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.49/0.72  thf('96', plain,
% 0.49/0.72      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.49/0.72        | ((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))
% 0.49/0.72        | ~ (v2_funct_1 @ k1_xboole_0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['94', '95'])).
% 0.49/0.72  thf('97', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.49/0.72  thf('98', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.49/0.72  thf(cc2_funct_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.72       ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) ))).
% 0.49/0.72  thf('99', plain,
% 0.49/0.72      (![X9 : $i]:
% 0.49/0.72         ((v2_funct_1 @ X9)
% 0.49/0.72          | ~ (v1_funct_1 @ X9)
% 0.49/0.72          | ~ (v1_relat_1 @ X9)
% 0.49/0.72          | ~ (v1_xboole_0 @ X9))),
% 0.49/0.72      inference('cnf', [status(esa)], [cc2_funct_1])).
% 0.49/0.72  thf('100', plain,
% 0.49/0.72      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.49/0.72        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.49/0.72        | (v2_funct_1 @ k1_xboole_0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['98', '99'])).
% 0.49/0.72  thf('101', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.49/0.72  thf('102', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.49/0.72  thf('103', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.49/0.72      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.49/0.72  thf('104', plain,
% 0.49/0.72      (((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 0.49/0.72      inference('demod', [status(thm)], ['96', '97', '103'])).
% 0.49/0.72  thf('105', plain,
% 0.49/0.72      (![X12 : $i]:
% 0.49/0.72         (~ (v2_funct_1 @ X12)
% 0.49/0.72          | ((k1_relat_1 @ X12) = (k2_relat_1 @ (k2_funct_1 @ X12)))
% 0.49/0.72          | ~ (v1_funct_1 @ X12)
% 0.49/0.72          | ~ (v1_relat_1 @ X12))),
% 0.49/0.72      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.49/0.72  thf('106', plain,
% 0.49/0.72      ((((k1_relat_1 @ k1_xboole_0) = (k2_relat_1 @ (k4_relat_1 @ k1_xboole_0)))
% 0.49/0.72        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.49/0.72        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.49/0.72        | ~ (v2_funct_1 @ k1_xboole_0))),
% 0.49/0.72      inference('sup+', [status(thm)], ['104', '105'])).
% 0.49/0.72  thf('107', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.72      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.49/0.72  thf('108', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.49/0.72  thf('109', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.49/0.72  thf('110', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.49/0.72      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.49/0.72  thf('111', plain,
% 0.49/0.72      (((k1_xboole_0) = (k2_relat_1 @ (k4_relat_1 @ k1_xboole_0)))),
% 0.49/0.72      inference('demod', [status(thm)], ['106', '107', '108', '109', '110'])).
% 0.49/0.72  thf('112', plain,
% 0.49/0.72      (![X7 : $i]:
% 0.49/0.72         (~ (v1_xboole_0 @ (k2_relat_1 @ X7))
% 0.49/0.72          | ~ (v1_relat_1 @ X7)
% 0.49/0.72          | (v1_xboole_0 @ X7))),
% 0.49/0.72      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.49/0.72  thf('113', plain,
% 0.49/0.72      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.49/0.72        | (v1_xboole_0 @ (k4_relat_1 @ k1_xboole_0))
% 0.49/0.72        | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['111', '112'])).
% 0.49/0.72  thf('114', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.49/0.72  thf('115', plain,
% 0.49/0.72      (((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 0.49/0.72      inference('demod', [status(thm)], ['96', '97', '103'])).
% 0.49/0.72  thf('116', plain,
% 0.49/0.72      (![X11 : $i]:
% 0.49/0.72         ((v1_relat_1 @ (k2_funct_1 @ X11))
% 0.49/0.72          | ~ (v1_funct_1 @ X11)
% 0.49/0.72          | ~ (v1_relat_1 @ X11))),
% 0.49/0.72      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.49/0.72  thf('117', plain,
% 0.49/0.72      (((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 0.49/0.72        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.49/0.72        | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.49/0.72      inference('sup+', [status(thm)], ['115', '116'])).
% 0.49/0.72  thf('118', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.49/0.72  thf('119', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [t45_ordinal1])).
% 0.49/0.72  thf('120', plain, ((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))),
% 0.49/0.72      inference('demod', [status(thm)], ['117', '118', '119'])).
% 0.49/0.72  thf('121', plain, ((v1_xboole_0 @ (k4_relat_1 @ k1_xboole_0))),
% 0.49/0.72      inference('demod', [status(thm)], ['113', '114', '120'])).
% 0.49/0.72  thf('122', plain,
% 0.49/0.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.49/0.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.49/0.72  thf('123', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['121', '122'])).
% 0.49/0.72  thf('124', plain,
% 0.49/0.72      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A))
% 0.49/0.72         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.49/0.72      inference('demod', [status(thm)], ['82', '93', '123'])).
% 0.49/0.72  thf('125', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['26', '124'])).
% 0.49/0.72  thf('126', plain,
% 0.49/0.72      (~
% 0.49/0.72       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.72         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.49/0.72       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.49/0.72       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.49/0.72      inference('split', [status(esa)], ['0'])).
% 0.49/0.72  thf('127', plain,
% 0.49/0.72      (~
% 0.49/0.72       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.72         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.49/0.72      inference('sat_resolution*', [status(thm)], ['18', '125', '126'])).
% 0.49/0.72  thf('128', plain,
% 0.49/0.72      (~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.49/0.72          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.49/0.72      inference('simpl_trail', [status(thm)], ['11', '127'])).
% 0.49/0.72  thf('129', plain,
% 0.49/0.72      (![X23 : $i, X24 : $i]:
% 0.49/0.72         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.49/0.72  thf('130', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.49/0.72  thf('131', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.49/0.72      inference('sup+', [status(thm)], ['129', '130'])).
% 0.49/0.72  thf('132', plain, ((~ (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C))),
% 0.49/0.72      inference('demod', [status(thm)], ['86', '87'])).
% 0.49/0.72  thf('133', plain,
% 0.49/0.72      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_C))),
% 0.49/0.72      inference('sup-', [status(thm)], ['131', '132'])).
% 0.49/0.72  thf(fc14_relat_1, axiom,
% 0.49/0.72    (![A:$i]:
% 0.49/0.72     ( ( v1_xboole_0 @ A ) =>
% 0.49/0.72       ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) ) & 
% 0.49/0.72         ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ))).
% 0.49/0.72  thf('134', plain,
% 0.49/0.72      (![X6 : $i]: ((v1_xboole_0 @ (k4_relat_1 @ X6)) | ~ (v1_xboole_0 @ X6))),
% 0.49/0.72      inference('cnf', [status(esa)], [fc14_relat_1])).
% 0.49/0.72  thf('135', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.49/0.72      inference('demod', [status(thm)], ['6', '9'])).
% 0.49/0.72  thf('136', plain,
% 0.49/0.72      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.49/0.72      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.49/0.72  thf('137', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.49/0.72      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.49/0.72  thf('138', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.49/0.72      inference('sup+', [status(thm)], ['136', '137'])).
% 0.49/0.72  thf(t3_subset, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.49/0.72  thf('139', plain,
% 0.49/0.72      (![X2 : $i, X4 : $i]:
% 0.49/0.72         ((m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.49/0.72      inference('cnf', [status(esa)], [t3_subset])).
% 0.49/0.72  thf('140', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['138', '139'])).
% 0.49/0.72  thf('141', plain,
% 0.49/0.72      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.72           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.49/0.72         <= (~
% 0.49/0.72             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.72               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.49/0.72      inference('split', [status(esa)], ['0'])).
% 0.49/0.72  thf('142', plain,
% 0.49/0.72      ((~ (v1_xboole_0 @ (k2_funct_1 @ sk_C)))
% 0.49/0.72         <= (~
% 0.49/0.72             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.72               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['140', '141'])).
% 0.49/0.72  thf('143', plain,
% 0.49/0.72      ((~ (v1_xboole_0 @ (k4_relat_1 @ sk_C)))
% 0.49/0.72         <= (~
% 0.49/0.72             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.72               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['135', '142'])).
% 0.49/0.72  thf('144', plain,
% 0.49/0.72      ((~ (v1_xboole_0 @ sk_C))
% 0.49/0.72         <= (~
% 0.49/0.72             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.72               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['134', '143'])).
% 0.49/0.72  thf('145', plain,
% 0.49/0.72      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 0.49/0.72         <= (~
% 0.49/0.72             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.72               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['133', '144'])).
% 0.49/0.72  thf('146', plain,
% 0.49/0.72      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['30', '31'])).
% 0.49/0.72  thf('147', plain,
% 0.49/0.72      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A))
% 0.49/0.72         <= (~
% 0.49/0.72             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.72               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['145', '146'])).
% 0.49/0.72  thf('148', plain,
% 0.49/0.72      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.49/0.72        | ((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C))))),
% 0.49/0.72      inference('demod', [status(thm)], ['36', '47'])).
% 0.49/0.72  thf('149', plain,
% 0.49/0.72      ((((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C))))
% 0.49/0.72         <= (~
% 0.49/0.72             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.72               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.49/0.72      inference('sup-', [status(thm)], ['147', '148'])).
% 0.49/0.72  thf('150', plain,
% 0.49/0.72      (![X31 : $i]:
% 0.49/0.72         ((m1_subset_1 @ X31 @ 
% 0.49/0.72           (k1_zfmisc_1 @ 
% 0.49/0.72            (k2_zfmisc_1 @ (k1_relat_1 @ X31) @ (k2_relat_1 @ X31))))
% 0.49/0.72          | ~ (v1_funct_1 @ X31)
% 0.49/0.72          | ~ (v1_relat_1 @ X31))),
% 0.49/0.72      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.49/0.72  thf('151', plain,
% 0.49/0.72      ((((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.49/0.72          (k1_zfmisc_1 @ 
% 0.49/0.72           (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)))
% 0.49/0.72         | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.49/0.72         | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))))
% 0.49/0.72         <= (~
% 0.49/0.72             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.72               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.49/0.72      inference('sup+', [status(thm)], ['149', '150'])).
% 0.49/0.72  thf('152', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.49/0.72      inference('demod', [status(thm)], ['58', '63'])).
% 0.49/0.72  thf('153', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.49/0.72      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.49/0.72  thf('154', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.49/0.72      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.49/0.72  thf('155', plain,
% 0.49/0.72      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.49/0.72         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.49/0.72         <= (~
% 0.49/0.72             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.72               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.49/0.72      inference('demod', [status(thm)], ['151', '152', '153', '154'])).
% 0.49/0.72  thf('156', plain,
% 0.49/0.72      (~
% 0.49/0.72       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.49/0.72         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.49/0.72      inference('sat_resolution*', [status(thm)], ['18', '125', '126'])).
% 0.49/0.72  thf('157', plain,
% 0.49/0.72      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.49/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.49/0.72      inference('simpl_trail', [status(thm)], ['155', '156'])).
% 0.49/0.72  thf('158', plain, ($false), inference('demod', [status(thm)], ['128', '157'])).
% 0.49/0.72  
% 0.49/0.72  % SZS output end Refutation
% 0.49/0.72  
% 0.59/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
