%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VzKxrfPIdT

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:47 EST 2020

% Result     : Theorem 4.28s
% Output     : Refutation 4.28s
% Verified   : 
% Statistics : Number of formulae       :  251 (5707 expanded)
%              Number of leaves         :   42 (1755 expanded)
%              Depth                    :   42
%              Number of atoms          : 1876 (82230 expanded)
%              Number of equality atoms :  103 (3055 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('6',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,
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

thf('14',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('24',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k1_relat_1 @ X21 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('28',plain,(
    ! [X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('29',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('30',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relat_1 @ X21 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('31',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('34',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('38',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relat_1 @ X21 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['38','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['36','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('48',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['31','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('55',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['30','58'])).

thf('60',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['34','35'])).

thf('61',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('62',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('63',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','60','61','62','63','64'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('66',plain,(
    ! [X39: $i] :
      ( ( v1_funct_2 @ X39 @ ( k1_relat_1 @ X39 ) @ ( k2_relat_1 @ X39 ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('67',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['29','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['28','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['27','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['76','77','78','79'])).

thf('81',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','80'])).

thf('82',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('83',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','83'])).

thf('85',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('87',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('88',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('90',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) @ sk_C )
      | ( ( k2_zfmisc_1 @ sk_A @ sk_B )
        = sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('92',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('93',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['92'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('94',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('95',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('96',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('98',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['92'])).

thf('99',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['91','93','96','97','98'])).

thf('100',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['84','99'])).

thf('101',plain,(
    ! [X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('102',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('103',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['91','93','96','97','98'])).

thf('104',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','60','61','62','63','64'])).

thf('105',plain,
    ( ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('107',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X39: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X39 ) @ ( k2_relat_1 @ X39 ) ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('109',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X0 )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) ) @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
        = ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['107','112'])).

thf('114',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('115',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('117',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('118',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['114'])).

thf('119',plain,
    ( ( ( k1_xboole_0
        = ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['113','115','116','117','118'])).

thf('120',plain,
    ( ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['102','119'])).

thf('121',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['114'])).

thf('122',plain,(
    ! [X18: $i,X19: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('123',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k1_xboole_0 = sk_C )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['91','93','96','97','98'])).

thf('125',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( ~ ( v1_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['120','123','126'])).

thf('128',plain,
    ( ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k2_funct_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['101','127'])).

thf('129',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['121','122'])).

thf('130',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('131',plain,
    ( ( k1_xboole_0
      = ( k2_funct_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('133',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('136',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('137',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['121','122'])).

thf('141',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['139','140'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('142',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('143',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['134','143'])).

thf('145',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X32 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('149',plain,(
    ! [X31: $i] :
      ( zip_tseitin_0 @ X31 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('151',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['149','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['147','153'])).

thf('155',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['100','131','154'])).

thf('156',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('157',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['12','155','156'])).

thf('158',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','157'])).

thf('159',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k1_relat_1 @ X21 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('160',plain,(
    ! [X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('161',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('162',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','60','61','62','63','64'])).

thf('163',plain,(
    ! [X39: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X39 ) @ ( k2_relat_1 @ X39 ) ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('164',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['162','163'])).

thf('165',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['161','164'])).

thf('166',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('167',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference(demod,[status(thm)],['165','166','167'])).

thf('169',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['160','168'])).

thf('170',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('171',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('173',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['159','172'])).

thf('174',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('175',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('176',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['34','35'])).

thf('177',plain,(
    ! [X20: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('178',plain,(
    ! [X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('179',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relat_1 @ X21 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('180',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('181',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['114'])).

thf('182',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('184',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['182','183'])).

thf('185',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['179','186'])).

thf('188',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['178','187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['177','189'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['176','191'])).

thf('193',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('194',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( ( k2_funct_1 @ sk_C )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['192','193','194','195'])).

thf('197',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['1','157'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('200',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B @ X0 ) ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['175','200'])).

thf('202',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['174','201'])).

thf('203',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('204',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['173','202','203','204','205'])).

thf('207',plain,(
    $false ),
    inference(demod,[status(thm)],['158','206'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VzKxrfPIdT
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:39:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.28/4.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.28/4.48  % Solved by: fo/fo7.sh
% 4.28/4.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.28/4.48  % done 4819 iterations in 4.023s
% 4.28/4.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.28/4.48  % SZS output start Refutation
% 4.28/4.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.28/4.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.28/4.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.28/4.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.28/4.48  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 4.28/4.48  thf(sk_B_type, type, sk_B: $i).
% 4.28/4.48  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.28/4.48  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.28/4.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.28/4.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.28/4.48  thf(sk_C_type, type, sk_C: $i).
% 4.28/4.48  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.28/4.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.28/4.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.28/4.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.28/4.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.28/4.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.28/4.48  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.28/4.48  thf(sk_A_type, type, sk_A: $i).
% 4.28/4.48  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.28/4.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.28/4.48  thf(t31_funct_2, conjecture,
% 4.28/4.48    (![A:$i,B:$i,C:$i]:
% 4.28/4.48     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.28/4.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.28/4.48       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 4.28/4.48         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 4.28/4.48           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 4.28/4.48           ( m1_subset_1 @
% 4.28/4.48             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 4.28/4.48  thf(zf_stmt_0, negated_conjecture,
% 4.28/4.48    (~( ![A:$i,B:$i,C:$i]:
% 4.28/4.48        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.28/4.48            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.28/4.48          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 4.28/4.48            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 4.28/4.48              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 4.28/4.48              ( m1_subset_1 @
% 4.28/4.48                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 4.28/4.48    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 4.28/4.48  thf('0', plain,
% 4.28/4.48      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.28/4.48        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 4.28/4.48        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.28/4.48             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('1', plain,
% 4.28/4.48      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.28/4.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 4.28/4.48         <= (~
% 4.28/4.48             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.28/4.48               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 4.28/4.48      inference('split', [status(esa)], ['0'])).
% 4.28/4.48  thf('2', plain,
% 4.28/4.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf(cc2_relat_1, axiom,
% 4.28/4.48    (![A:$i]:
% 4.28/4.48     ( ( v1_relat_1 @ A ) =>
% 4.28/4.48       ( ![B:$i]:
% 4.28/4.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 4.28/4.48  thf('3', plain,
% 4.28/4.48      (![X14 : $i, X15 : $i]:
% 4.28/4.48         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 4.28/4.48          | (v1_relat_1 @ X14)
% 4.28/4.48          | ~ (v1_relat_1 @ X15))),
% 4.28/4.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.28/4.48  thf('4', plain,
% 4.28/4.48      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 4.28/4.48      inference('sup-', [status(thm)], ['2', '3'])).
% 4.28/4.48  thf(fc6_relat_1, axiom,
% 4.28/4.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.28/4.48  thf('5', plain,
% 4.28/4.48      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 4.28/4.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.28/4.48  thf('6', plain, ((v1_relat_1 @ sk_C)),
% 4.28/4.48      inference('demod', [status(thm)], ['4', '5'])).
% 4.28/4.48  thf(dt_k2_funct_1, axiom,
% 4.28/4.48    (![A:$i]:
% 4.28/4.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.28/4.48       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 4.28/4.48         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 4.28/4.48  thf('7', plain,
% 4.28/4.48      (![X20 : $i]:
% 4.28/4.48         ((v1_funct_1 @ (k2_funct_1 @ X20))
% 4.28/4.48          | ~ (v1_funct_1 @ X20)
% 4.28/4.48          | ~ (v1_relat_1 @ X20))),
% 4.28/4.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.28/4.48  thf('8', plain,
% 4.28/4.48      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 4.28/4.48         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.28/4.48      inference('split', [status(esa)], ['0'])).
% 4.28/4.48  thf('9', plain,
% 4.28/4.48      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 4.28/4.48         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.28/4.48      inference('sup-', [status(thm)], ['7', '8'])).
% 4.28/4.48  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('11', plain,
% 4.28/4.48      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 4.28/4.48      inference('demod', [status(thm)], ['9', '10'])).
% 4.28/4.48  thf('12', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['6', '11'])).
% 4.28/4.48  thf('13', plain,
% 4.28/4.48      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 4.28/4.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.28/4.48      inference('split', [status(esa)], ['0'])).
% 4.28/4.48  thf(d1_funct_2, axiom,
% 4.28/4.48    (![A:$i,B:$i,C:$i]:
% 4.28/4.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.28/4.48       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.28/4.48           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.28/4.48             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.28/4.48         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.28/4.48           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.28/4.48             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.28/4.48  thf(zf_stmt_1, axiom,
% 4.28/4.48    (![B:$i,A:$i]:
% 4.28/4.48     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.28/4.48       ( zip_tseitin_0 @ B @ A ) ))).
% 4.28/4.48  thf('14', plain,
% 4.28/4.48      (![X31 : $i, X32 : $i]:
% 4.28/4.48         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.28/4.48  thf('15', plain,
% 4.28/4.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.28/4.48  thf(zf_stmt_3, axiom,
% 4.28/4.48    (![C:$i,B:$i,A:$i]:
% 4.28/4.48     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.28/4.48       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.28/4.48  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 4.28/4.48  thf(zf_stmt_5, axiom,
% 4.28/4.48    (![A:$i,B:$i,C:$i]:
% 4.28/4.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.28/4.48       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.28/4.48         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.28/4.48           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.28/4.48             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.28/4.48  thf('16', plain,
% 4.28/4.48      (![X36 : $i, X37 : $i, X38 : $i]:
% 4.28/4.48         (~ (zip_tseitin_0 @ X36 @ X37)
% 4.28/4.48          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 4.28/4.48          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.28/4.48  thf('17', plain,
% 4.28/4.48      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.28/4.48      inference('sup-', [status(thm)], ['15', '16'])).
% 4.28/4.48  thf('18', plain,
% 4.28/4.48      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 4.28/4.48      inference('sup-', [status(thm)], ['14', '17'])).
% 4.28/4.48  thf('19', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('20', plain,
% 4.28/4.48      (![X33 : $i, X34 : $i, X35 : $i]:
% 4.28/4.48         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 4.28/4.48          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 4.28/4.48          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.28/4.48  thf('21', plain,
% 4.28/4.48      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 4.28/4.48        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['19', '20'])).
% 4.28/4.48  thf('22', plain,
% 4.28/4.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf(redefinition_k1_relset_1, axiom,
% 4.28/4.48    (![A:$i,B:$i,C:$i]:
% 4.28/4.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.28/4.48       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 4.28/4.48  thf('23', plain,
% 4.28/4.48      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.28/4.48         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 4.28/4.48          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 4.28/4.48      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.28/4.48  thf('24', plain,
% 4.28/4.48      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 4.28/4.48      inference('sup-', [status(thm)], ['22', '23'])).
% 4.28/4.48  thf('25', plain,
% 4.28/4.48      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 4.28/4.48      inference('demod', [status(thm)], ['21', '24'])).
% 4.28/4.48  thf('26', plain,
% 4.28/4.48      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['18', '25'])).
% 4.28/4.48  thf(t55_funct_1, axiom,
% 4.28/4.48    (![A:$i]:
% 4.28/4.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.28/4.48       ( ( v2_funct_1 @ A ) =>
% 4.28/4.48         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 4.28/4.48           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 4.28/4.48  thf('27', plain,
% 4.28/4.48      (![X21 : $i]:
% 4.28/4.48         (~ (v2_funct_1 @ X21)
% 4.28/4.48          | ((k1_relat_1 @ X21) = (k2_relat_1 @ (k2_funct_1 @ X21)))
% 4.28/4.48          | ~ (v1_funct_1 @ X21)
% 4.28/4.48          | ~ (v1_relat_1 @ X21))),
% 4.28/4.48      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.28/4.48  thf('28', plain,
% 4.28/4.48      (![X20 : $i]:
% 4.28/4.48         ((v1_funct_1 @ (k2_funct_1 @ X20))
% 4.28/4.48          | ~ (v1_funct_1 @ X20)
% 4.28/4.48          | ~ (v1_relat_1 @ X20))),
% 4.28/4.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.28/4.48  thf('29', plain,
% 4.28/4.48      (![X20 : $i]:
% 4.28/4.48         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 4.28/4.48          | ~ (v1_funct_1 @ X20)
% 4.28/4.48          | ~ (v1_relat_1 @ X20))),
% 4.28/4.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.28/4.48  thf('30', plain,
% 4.28/4.48      (![X21 : $i]:
% 4.28/4.48         (~ (v2_funct_1 @ X21)
% 4.28/4.48          | ((k2_relat_1 @ X21) = (k1_relat_1 @ (k2_funct_1 @ X21)))
% 4.28/4.48          | ~ (v1_funct_1 @ X21)
% 4.28/4.48          | ~ (v1_relat_1 @ X21))),
% 4.28/4.48      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.28/4.48  thf('31', plain,
% 4.28/4.48      (![X20 : $i]:
% 4.28/4.48         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 4.28/4.48          | ~ (v1_funct_1 @ X20)
% 4.28/4.48          | ~ (v1_relat_1 @ X20))),
% 4.28/4.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.28/4.48  thf('32', plain,
% 4.28/4.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf(redefinition_k2_relset_1, axiom,
% 4.28/4.48    (![A:$i,B:$i,C:$i]:
% 4.28/4.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.28/4.48       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.28/4.48  thf('33', plain,
% 4.28/4.48      (![X28 : $i, X29 : $i, X30 : $i]:
% 4.28/4.48         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 4.28/4.48          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 4.28/4.48      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.28/4.48  thf('34', plain,
% 4.28/4.48      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 4.28/4.48      inference('sup-', [status(thm)], ['32', '33'])).
% 4.28/4.48  thf('35', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('36', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.28/4.48      inference('sup+', [status(thm)], ['34', '35'])).
% 4.28/4.48  thf('37', plain,
% 4.28/4.48      (![X20 : $i]:
% 4.28/4.48         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 4.28/4.48          | ~ (v1_funct_1 @ X20)
% 4.28/4.48          | ~ (v1_relat_1 @ X20))),
% 4.28/4.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.28/4.48  thf('38', plain,
% 4.28/4.48      (![X21 : $i]:
% 4.28/4.48         (~ (v2_funct_1 @ X21)
% 4.28/4.48          | ((k2_relat_1 @ X21) = (k1_relat_1 @ (k2_funct_1 @ X21)))
% 4.28/4.48          | ~ (v1_funct_1 @ X21)
% 4.28/4.48          | ~ (v1_relat_1 @ X21))),
% 4.28/4.48      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.28/4.48  thf(d10_xboole_0, axiom,
% 4.28/4.48    (![A:$i,B:$i]:
% 4.28/4.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.28/4.48  thf('39', plain,
% 4.28/4.48      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 4.28/4.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.28/4.48  thf('40', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 4.28/4.48      inference('simplify', [status(thm)], ['39'])).
% 4.28/4.48  thf(d18_relat_1, axiom,
% 4.28/4.48    (![A:$i,B:$i]:
% 4.28/4.48     ( ( v1_relat_1 @ B ) =>
% 4.28/4.48       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 4.28/4.48  thf('41', plain,
% 4.28/4.48      (![X16 : $i, X17 : $i]:
% 4.28/4.48         (~ (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 4.28/4.48          | (v4_relat_1 @ X16 @ X17)
% 4.28/4.48          | ~ (v1_relat_1 @ X16))),
% 4.28/4.48      inference('cnf', [status(esa)], [d18_relat_1])).
% 4.28/4.48  thf('42', plain,
% 4.28/4.48      (![X0 : $i]:
% 4.28/4.48         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['40', '41'])).
% 4.28/4.48  thf('43', plain,
% 4.28/4.48      (![X0 : $i]:
% 4.28/4.48         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 4.28/4.48          | ~ (v1_relat_1 @ X0)
% 4.28/4.48          | ~ (v1_funct_1 @ X0)
% 4.28/4.48          | ~ (v2_funct_1 @ X0)
% 4.28/4.48          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 4.28/4.48      inference('sup+', [status(thm)], ['38', '42'])).
% 4.28/4.48  thf('44', plain,
% 4.28/4.48      (![X0 : $i]:
% 4.28/4.48         (~ (v1_relat_1 @ X0)
% 4.28/4.48          | ~ (v1_funct_1 @ X0)
% 4.28/4.48          | ~ (v2_funct_1 @ X0)
% 4.28/4.48          | ~ (v1_funct_1 @ X0)
% 4.28/4.48          | ~ (v1_relat_1 @ X0)
% 4.28/4.48          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['37', '43'])).
% 4.28/4.48  thf('45', plain,
% 4.28/4.48      (![X0 : $i]:
% 4.28/4.48         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 4.28/4.48          | ~ (v2_funct_1 @ X0)
% 4.28/4.48          | ~ (v1_funct_1 @ X0)
% 4.28/4.48          | ~ (v1_relat_1 @ X0))),
% 4.28/4.48      inference('simplify', [status(thm)], ['44'])).
% 4.28/4.48  thf('46', plain,
% 4.28/4.48      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 4.28/4.48        | ~ (v1_relat_1 @ sk_C)
% 4.28/4.48        | ~ (v1_funct_1 @ sk_C)
% 4.28/4.48        | ~ (v2_funct_1 @ sk_C))),
% 4.28/4.48      inference('sup+', [status(thm)], ['36', '45'])).
% 4.28/4.48  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 4.28/4.48      inference('demod', [status(thm)], ['4', '5'])).
% 4.28/4.48  thf('48', plain, ((v1_funct_1 @ sk_C)),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('49', plain, ((v2_funct_1 @ sk_C)),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('50', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 4.28/4.48      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 4.28/4.48  thf('51', plain,
% 4.28/4.48      (![X16 : $i, X17 : $i]:
% 4.28/4.48         (~ (v4_relat_1 @ X16 @ X17)
% 4.28/4.48          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 4.28/4.48          | ~ (v1_relat_1 @ X16))),
% 4.28/4.48      inference('cnf', [status(esa)], [d18_relat_1])).
% 4.28/4.48  thf('52', plain,
% 4.28/4.48      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 4.28/4.48        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 4.28/4.48      inference('sup-', [status(thm)], ['50', '51'])).
% 4.28/4.48  thf('53', plain,
% 4.28/4.48      ((~ (v1_relat_1 @ sk_C)
% 4.28/4.48        | ~ (v1_funct_1 @ sk_C)
% 4.28/4.48        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 4.28/4.48      inference('sup-', [status(thm)], ['31', '52'])).
% 4.28/4.48  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 4.28/4.48      inference('demod', [status(thm)], ['4', '5'])).
% 4.28/4.48  thf('55', plain, ((v1_funct_1 @ sk_C)),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('56', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 4.28/4.48      inference('demod', [status(thm)], ['53', '54', '55'])).
% 4.28/4.48  thf('57', plain,
% 4.28/4.48      (![X0 : $i, X2 : $i]:
% 4.28/4.48         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.28/4.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.28/4.48  thf('58', plain,
% 4.28/4.48      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 4.28/4.48        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 4.28/4.48      inference('sup-', [status(thm)], ['56', '57'])).
% 4.28/4.48  thf('59', plain,
% 4.28/4.48      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 4.28/4.48        | ~ (v1_relat_1 @ sk_C)
% 4.28/4.48        | ~ (v1_funct_1 @ sk_C)
% 4.28/4.48        | ~ (v2_funct_1 @ sk_C)
% 4.28/4.48        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 4.28/4.48      inference('sup-', [status(thm)], ['30', '58'])).
% 4.28/4.48  thf('60', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.28/4.48      inference('sup+', [status(thm)], ['34', '35'])).
% 4.28/4.48  thf('61', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 4.28/4.48      inference('simplify', [status(thm)], ['39'])).
% 4.28/4.48  thf('62', plain, ((v1_relat_1 @ sk_C)),
% 4.28/4.48      inference('demod', [status(thm)], ['4', '5'])).
% 4.28/4.48  thf('63', plain, ((v1_funct_1 @ sk_C)),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('64', plain, ((v2_funct_1 @ sk_C)),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('65', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.28/4.48      inference('demod', [status(thm)], ['59', '60', '61', '62', '63', '64'])).
% 4.28/4.48  thf(t3_funct_2, axiom,
% 4.28/4.48    (![A:$i]:
% 4.28/4.48     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.28/4.48       ( ( v1_funct_1 @ A ) & 
% 4.28/4.48         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 4.28/4.48         ( m1_subset_1 @
% 4.28/4.48           A @ 
% 4.28/4.48           ( k1_zfmisc_1 @
% 4.28/4.48             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 4.28/4.48  thf('66', plain,
% 4.28/4.48      (![X39 : $i]:
% 4.28/4.48         ((v1_funct_2 @ X39 @ (k1_relat_1 @ X39) @ (k2_relat_1 @ X39))
% 4.28/4.48          | ~ (v1_funct_1 @ X39)
% 4.28/4.48          | ~ (v1_relat_1 @ X39))),
% 4.28/4.48      inference('cnf', [status(esa)], [t3_funct_2])).
% 4.28/4.48  thf('67', plain,
% 4.28/4.48      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 4.28/4.48         (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 4.28/4.48        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 4.28/4.48        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.28/4.48      inference('sup+', [status(thm)], ['65', '66'])).
% 4.28/4.48  thf('68', plain,
% 4.28/4.48      ((~ (v1_relat_1 @ sk_C)
% 4.28/4.48        | ~ (v1_funct_1 @ sk_C)
% 4.28/4.48        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.28/4.48        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 4.28/4.48           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 4.28/4.48      inference('sup-', [status(thm)], ['29', '67'])).
% 4.28/4.48  thf('69', plain, ((v1_relat_1 @ sk_C)),
% 4.28/4.48      inference('demod', [status(thm)], ['4', '5'])).
% 4.28/4.48  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('71', plain,
% 4.28/4.48      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.28/4.48        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 4.28/4.48           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 4.28/4.48      inference('demod', [status(thm)], ['68', '69', '70'])).
% 4.28/4.48  thf('72', plain,
% 4.28/4.48      ((~ (v1_relat_1 @ sk_C)
% 4.28/4.48        | ~ (v1_funct_1 @ sk_C)
% 4.28/4.48        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 4.28/4.48           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 4.28/4.48      inference('sup-', [status(thm)], ['28', '71'])).
% 4.28/4.48  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 4.28/4.48      inference('demod', [status(thm)], ['4', '5'])).
% 4.28/4.48  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('75', plain,
% 4.28/4.48      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ 
% 4.28/4.48        (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.28/4.48      inference('demod', [status(thm)], ['72', '73', '74'])).
% 4.28/4.48  thf('76', plain,
% 4.28/4.48      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))
% 4.28/4.48        | ~ (v1_relat_1 @ sk_C)
% 4.28/4.48        | ~ (v1_funct_1 @ sk_C)
% 4.28/4.48        | ~ (v2_funct_1 @ sk_C))),
% 4.28/4.48      inference('sup+', [status(thm)], ['27', '75'])).
% 4.28/4.48  thf('77', plain, ((v1_relat_1 @ sk_C)),
% 4.28/4.48      inference('demod', [status(thm)], ['4', '5'])).
% 4.28/4.48  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('79', plain, ((v2_funct_1 @ sk_C)),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('80', plain,
% 4.28/4.48      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 4.28/4.48      inference('demod', [status(thm)], ['76', '77', '78', '79'])).
% 4.28/4.48  thf('81', plain,
% 4.28/4.48      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 4.28/4.48        | ((sk_B) = (k1_xboole_0)))),
% 4.28/4.48      inference('sup+', [status(thm)], ['26', '80'])).
% 4.28/4.48  thf('82', plain,
% 4.28/4.48      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 4.28/4.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.28/4.48      inference('split', [status(esa)], ['0'])).
% 4.28/4.48  thf('83', plain,
% 4.28/4.48      ((((sk_B) = (k1_xboole_0)))
% 4.28/4.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['81', '82'])).
% 4.28/4.48  thf('84', plain,
% 4.28/4.48      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ k1_xboole_0 @ sk_A))
% 4.28/4.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.28/4.48      inference('demod', [status(thm)], ['13', '83'])).
% 4.28/4.48  thf('85', plain,
% 4.28/4.48      ((((sk_B) = (k1_xboole_0)))
% 4.28/4.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['81', '82'])).
% 4.28/4.48  thf('86', plain,
% 4.28/4.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf(t3_subset, axiom,
% 4.28/4.48    (![A:$i,B:$i]:
% 4.28/4.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.28/4.48  thf('87', plain,
% 4.28/4.48      (![X8 : $i, X9 : $i]:
% 4.28/4.48         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 4.28/4.48      inference('cnf', [status(esa)], [t3_subset])).
% 4.28/4.48  thf('88', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 4.28/4.48      inference('sup-', [status(thm)], ['86', '87'])).
% 4.28/4.48  thf('89', plain,
% 4.28/4.48      (![X0 : $i, X2 : $i]:
% 4.28/4.48         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.28/4.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.28/4.48  thf('90', plain,
% 4.28/4.48      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C)
% 4.28/4.48        | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['88', '89'])).
% 4.28/4.48  thf('91', plain,
% 4.28/4.48      (((~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0) @ sk_C)
% 4.28/4.48         | ((k2_zfmisc_1 @ sk_A @ sk_B) = (sk_C))))
% 4.28/4.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['85', '90'])).
% 4.28/4.48  thf(t113_zfmisc_1, axiom,
% 4.28/4.48    (![A:$i,B:$i]:
% 4.28/4.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 4.28/4.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.28/4.48  thf('92', plain,
% 4.28/4.48      (![X5 : $i, X6 : $i]:
% 4.28/4.48         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 4.28/4.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.28/4.48  thf('93', plain,
% 4.28/4.48      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 4.28/4.48      inference('simplify', [status(thm)], ['92'])).
% 4.28/4.48  thf(t4_subset_1, axiom,
% 4.28/4.48    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 4.28/4.48  thf('94', plain,
% 4.28/4.48      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 4.28/4.48      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.28/4.48  thf('95', plain,
% 4.28/4.48      (![X8 : $i, X9 : $i]:
% 4.28/4.48         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 4.28/4.48      inference('cnf', [status(esa)], [t3_subset])).
% 4.28/4.48  thf('96', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.28/4.48      inference('sup-', [status(thm)], ['94', '95'])).
% 4.28/4.48  thf('97', plain,
% 4.28/4.48      ((((sk_B) = (k1_xboole_0)))
% 4.28/4.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['81', '82'])).
% 4.28/4.48  thf('98', plain,
% 4.28/4.48      (![X5 : $i]: ((k2_zfmisc_1 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 4.28/4.48      inference('simplify', [status(thm)], ['92'])).
% 4.28/4.48  thf('99', plain,
% 4.28/4.48      ((((k1_xboole_0) = (sk_C)))
% 4.28/4.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.28/4.48      inference('demod', [status(thm)], ['91', '93', '96', '97', '98'])).
% 4.28/4.48  thf('100', plain,
% 4.28/4.48      ((~ (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ sk_A))
% 4.28/4.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.28/4.48      inference('demod', [status(thm)], ['84', '99'])).
% 4.28/4.48  thf('101', plain,
% 4.28/4.48      (![X20 : $i]:
% 4.28/4.48         ((v1_funct_1 @ (k2_funct_1 @ X20))
% 4.28/4.48          | ~ (v1_funct_1 @ X20)
% 4.28/4.48          | ~ (v1_relat_1 @ X20))),
% 4.28/4.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.28/4.48  thf('102', plain,
% 4.28/4.48      (![X20 : $i]:
% 4.28/4.48         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 4.28/4.48          | ~ (v1_funct_1 @ X20)
% 4.28/4.48          | ~ (v1_relat_1 @ X20))),
% 4.28/4.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.28/4.48  thf('103', plain,
% 4.28/4.48      ((((k1_xboole_0) = (sk_C)))
% 4.28/4.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.28/4.48      inference('demod', [status(thm)], ['91', '93', '96', '97', '98'])).
% 4.28/4.48  thf('104', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.28/4.48      inference('demod', [status(thm)], ['59', '60', '61', '62', '63', '64'])).
% 4.28/4.48  thf('105', plain,
% 4.28/4.48      ((((sk_B) = (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0))))
% 4.28/4.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.28/4.48      inference('sup+', [status(thm)], ['103', '104'])).
% 4.28/4.48  thf('106', plain,
% 4.28/4.48      ((((sk_B) = (k1_xboole_0)))
% 4.28/4.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['81', '82'])).
% 4.28/4.48  thf('107', plain,
% 4.28/4.48      ((((k1_xboole_0) = (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0))))
% 4.28/4.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.28/4.48      inference('demod', [status(thm)], ['105', '106'])).
% 4.28/4.48  thf('108', plain,
% 4.28/4.48      (![X39 : $i]:
% 4.28/4.48         ((m1_subset_1 @ X39 @ 
% 4.28/4.48           (k1_zfmisc_1 @ 
% 4.28/4.48            (k2_zfmisc_1 @ (k1_relat_1 @ X39) @ (k2_relat_1 @ X39))))
% 4.28/4.48          | ~ (v1_funct_1 @ X39)
% 4.28/4.48          | ~ (v1_relat_1 @ X39))),
% 4.28/4.48      inference('cnf', [status(esa)], [t3_funct_2])).
% 4.28/4.48  thf('109', plain,
% 4.28/4.48      (![X8 : $i, X9 : $i]:
% 4.28/4.48         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 4.28/4.48      inference('cnf', [status(esa)], [t3_subset])).
% 4.28/4.48  thf('110', plain,
% 4.28/4.48      (![X0 : $i]:
% 4.28/4.48         (~ (v1_relat_1 @ X0)
% 4.28/4.48          | ~ (v1_funct_1 @ X0)
% 4.28/4.48          | (r1_tarski @ X0 @ 
% 4.28/4.48             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 4.28/4.48      inference('sup-', [status(thm)], ['108', '109'])).
% 4.28/4.48  thf('111', plain,
% 4.28/4.48      (![X0 : $i, X2 : $i]:
% 4.28/4.48         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.28/4.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.28/4.48  thf('112', plain,
% 4.28/4.48      (![X0 : $i]:
% 4.28/4.48         (~ (v1_funct_1 @ X0)
% 4.28/4.48          | ~ (v1_relat_1 @ X0)
% 4.28/4.48          | ~ (r1_tarski @ 
% 4.28/4.48               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X0)
% 4.28/4.48          | ((k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) = (X0)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['110', '111'])).
% 4.28/4.48  thf('113', plain,
% 4.28/4.48      (((~ (r1_tarski @ 
% 4.28/4.48            (k2_zfmisc_1 @ k1_xboole_0 @ 
% 4.28/4.48             (k2_relat_1 @ (k2_funct_1 @ k1_xboole_0))) @ 
% 4.28/4.48            (k2_funct_1 @ k1_xboole_0))
% 4.28/4.48         | ((k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0)) @ 
% 4.28/4.48             (k2_relat_1 @ (k2_funct_1 @ k1_xboole_0)))
% 4.28/4.48             = (k2_funct_1 @ k1_xboole_0))
% 4.28/4.48         | ~ (v1_relat_1 @ (k2_funct_1 @ k1_xboole_0))
% 4.28/4.48         | ~ (v1_funct_1 @ (k2_funct_1 @ k1_xboole_0))))
% 4.28/4.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['107', '112'])).
% 4.28/4.48  thf('114', plain,
% 4.28/4.48      (![X5 : $i, X6 : $i]:
% 4.28/4.48         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 4.28/4.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.28/4.48  thf('115', plain,
% 4.28/4.48      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 4.28/4.48      inference('simplify', [status(thm)], ['114'])).
% 4.28/4.48  thf('116', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.28/4.48      inference('sup-', [status(thm)], ['94', '95'])).
% 4.28/4.48  thf('117', plain,
% 4.28/4.48      ((((k1_xboole_0) = (k1_relat_1 @ (k2_funct_1 @ k1_xboole_0))))
% 4.28/4.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.28/4.48      inference('demod', [status(thm)], ['105', '106'])).
% 4.28/4.48  thf('118', plain,
% 4.28/4.48      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 4.28/4.48      inference('simplify', [status(thm)], ['114'])).
% 4.28/4.48  thf('119', plain,
% 4.28/4.48      (((((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))
% 4.28/4.48         | ~ (v1_relat_1 @ (k2_funct_1 @ k1_xboole_0))
% 4.28/4.48         | ~ (v1_funct_1 @ (k2_funct_1 @ k1_xboole_0))))
% 4.28/4.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.28/4.48      inference('demod', [status(thm)], ['113', '115', '116', '117', '118'])).
% 4.28/4.48  thf('120', plain,
% 4.28/4.48      (((~ (v1_relat_1 @ k1_xboole_0)
% 4.28/4.48         | ~ (v1_funct_1 @ k1_xboole_0)
% 4.28/4.48         | ~ (v1_funct_1 @ (k2_funct_1 @ k1_xboole_0))
% 4.28/4.48         | ((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))))
% 4.28/4.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['102', '119'])).
% 4.28/4.48  thf('121', plain,
% 4.28/4.48      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 4.28/4.48      inference('simplify', [status(thm)], ['114'])).
% 4.28/4.48  thf('122', plain,
% 4.28/4.48      (![X18 : $i, X19 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X18 @ X19))),
% 4.28/4.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.28/4.48  thf('123', plain, ((v1_relat_1 @ k1_xboole_0)),
% 4.28/4.48      inference('sup+', [status(thm)], ['121', '122'])).
% 4.28/4.48  thf('124', plain,
% 4.28/4.48      ((((k1_xboole_0) = (sk_C)))
% 4.28/4.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.28/4.48      inference('demod', [status(thm)], ['91', '93', '96', '97', '98'])).
% 4.28/4.48  thf('125', plain, ((v1_funct_1 @ sk_C)),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('126', plain,
% 4.28/4.48      (((v1_funct_1 @ k1_xboole_0))
% 4.28/4.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.28/4.48      inference('sup+', [status(thm)], ['124', '125'])).
% 4.28/4.48  thf('127', plain,
% 4.28/4.48      (((~ (v1_funct_1 @ (k2_funct_1 @ k1_xboole_0))
% 4.28/4.48         | ((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))))
% 4.28/4.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.28/4.48      inference('demod', [status(thm)], ['120', '123', '126'])).
% 4.28/4.48  thf('128', plain,
% 4.28/4.48      (((~ (v1_relat_1 @ k1_xboole_0)
% 4.28/4.48         | ~ (v1_funct_1 @ k1_xboole_0)
% 4.28/4.48         | ((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0))))
% 4.28/4.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.28/4.48      inference('sup-', [status(thm)], ['101', '127'])).
% 4.28/4.48  thf('129', plain, ((v1_relat_1 @ k1_xboole_0)),
% 4.28/4.48      inference('sup+', [status(thm)], ['121', '122'])).
% 4.28/4.48  thf('130', plain,
% 4.28/4.48      (((v1_funct_1 @ k1_xboole_0))
% 4.28/4.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.28/4.48      inference('sup+', [status(thm)], ['124', '125'])).
% 4.28/4.48  thf('131', plain,
% 4.28/4.48      ((((k1_xboole_0) = (k2_funct_1 @ k1_xboole_0)))
% 4.28/4.48         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 4.28/4.48      inference('demod', [status(thm)], ['128', '129', '130'])).
% 4.28/4.48  thf('132', plain,
% 4.28/4.48      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 4.28/4.48      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.28/4.48  thf('133', plain,
% 4.28/4.48      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.28/4.48         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 4.28/4.48          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 4.28/4.48      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 4.28/4.48  thf('134', plain,
% 4.28/4.48      (![X0 : $i, X1 : $i]:
% 4.28/4.48         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 4.28/4.48      inference('sup-', [status(thm)], ['132', '133'])).
% 4.28/4.48  thf('135', plain,
% 4.28/4.48      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 4.28/4.48      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.28/4.48  thf(cc2_relset_1, axiom,
% 4.28/4.48    (![A:$i,B:$i,C:$i]:
% 4.28/4.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.28/4.48       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.28/4.48  thf('136', plain,
% 4.28/4.48      (![X22 : $i, X23 : $i, X24 : $i]:
% 4.28/4.48         ((v4_relat_1 @ X22 @ X23)
% 4.28/4.48          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 4.28/4.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.28/4.48  thf('137', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 4.28/4.48      inference('sup-', [status(thm)], ['135', '136'])).
% 4.28/4.48  thf('138', plain,
% 4.28/4.48      (![X16 : $i, X17 : $i]:
% 4.28/4.48         (~ (v4_relat_1 @ X16 @ X17)
% 4.28/4.48          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 4.28/4.48          | ~ (v1_relat_1 @ X16))),
% 4.28/4.48      inference('cnf', [status(esa)], [d18_relat_1])).
% 4.28/4.48  thf('139', plain,
% 4.28/4.48      (![X0 : $i]:
% 4.28/4.48         (~ (v1_relat_1 @ k1_xboole_0)
% 4.28/4.48          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 4.28/4.48      inference('sup-', [status(thm)], ['137', '138'])).
% 4.28/4.48  thf('140', plain, ((v1_relat_1 @ k1_xboole_0)),
% 4.28/4.48      inference('sup+', [status(thm)], ['121', '122'])).
% 4.28/4.48  thf('141', plain,
% 4.28/4.48      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 4.28/4.48      inference('demod', [status(thm)], ['139', '140'])).
% 4.28/4.48  thf(t3_xboole_1, axiom,
% 4.28/4.48    (![A:$i]:
% 4.28/4.48     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 4.28/4.48  thf('142', plain,
% 4.28/4.48      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 4.28/4.48      inference('cnf', [status(esa)], [t3_xboole_1])).
% 4.28/4.48  thf('143', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.28/4.48      inference('sup-', [status(thm)], ['141', '142'])).
% 4.28/4.48  thf('144', plain,
% 4.28/4.48      (![X0 : $i, X1 : $i]:
% 4.28/4.48         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 4.28/4.48      inference('demod', [status(thm)], ['134', '143'])).
% 4.28/4.48  thf('145', plain,
% 4.28/4.48      (![X33 : $i, X34 : $i, X35 : $i]:
% 4.28/4.48         (((X33) != (k1_relset_1 @ X33 @ X34 @ X35))
% 4.28/4.48          | (v1_funct_2 @ X35 @ X33 @ X34)
% 4.28/4.48          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.28/4.48  thf('146', plain,
% 4.28/4.48      (![X0 : $i, X1 : $i]:
% 4.28/4.48         (((X1) != (k1_xboole_0))
% 4.28/4.48          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 4.28/4.48          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 4.28/4.48      inference('sup-', [status(thm)], ['144', '145'])).
% 4.28/4.48  thf('147', plain,
% 4.28/4.48      (![X0 : $i]:
% 4.28/4.48         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 4.28/4.48          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 4.28/4.48      inference('simplify', [status(thm)], ['146'])).
% 4.28/4.48  thf('148', plain,
% 4.28/4.48      (![X31 : $i, X32 : $i]:
% 4.28/4.48         ((zip_tseitin_0 @ X31 @ X32) | ((X32) != (k1_xboole_0)))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.28/4.48  thf('149', plain, (![X31 : $i]: (zip_tseitin_0 @ X31 @ k1_xboole_0)),
% 4.28/4.48      inference('simplify', [status(thm)], ['148'])).
% 4.28/4.48  thf('150', plain,
% 4.28/4.48      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 4.28/4.48      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.28/4.48  thf('151', plain,
% 4.28/4.48      (![X36 : $i, X37 : $i, X38 : $i]:
% 4.28/4.48         (~ (zip_tseitin_0 @ X36 @ X37)
% 4.28/4.48          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 4.28/4.48          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.28/4.48  thf('152', plain,
% 4.28/4.48      (![X0 : $i, X1 : $i]:
% 4.28/4.48         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 4.28/4.48      inference('sup-', [status(thm)], ['150', '151'])).
% 4.28/4.48  thf('153', plain,
% 4.28/4.48      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 4.28/4.48      inference('sup-', [status(thm)], ['149', '152'])).
% 4.28/4.48  thf('154', plain,
% 4.28/4.48      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 4.28/4.48      inference('demod', [status(thm)], ['147', '153'])).
% 4.28/4.48  thf('155', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 4.28/4.48      inference('demod', [status(thm)], ['100', '131', '154'])).
% 4.28/4.48  thf('156', plain,
% 4.28/4.48      (~
% 4.28/4.48       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.28/4.48         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 4.28/4.48       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 4.28/4.48       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.28/4.48      inference('split', [status(esa)], ['0'])).
% 4.28/4.48  thf('157', plain,
% 4.28/4.48      (~
% 4.28/4.48       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.28/4.48         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 4.28/4.48      inference('sat_resolution*', [status(thm)], ['12', '155', '156'])).
% 4.28/4.48  thf('158', plain,
% 4.28/4.48      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.28/4.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.28/4.48      inference('simpl_trail', [status(thm)], ['1', '157'])).
% 4.28/4.48  thf('159', plain,
% 4.28/4.48      (![X21 : $i]:
% 4.28/4.48         (~ (v2_funct_1 @ X21)
% 4.28/4.48          | ((k1_relat_1 @ X21) = (k2_relat_1 @ (k2_funct_1 @ X21)))
% 4.28/4.48          | ~ (v1_funct_1 @ X21)
% 4.28/4.48          | ~ (v1_relat_1 @ X21))),
% 4.28/4.48      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.28/4.48  thf('160', plain,
% 4.28/4.48      (![X20 : $i]:
% 4.28/4.48         ((v1_funct_1 @ (k2_funct_1 @ X20))
% 4.28/4.48          | ~ (v1_funct_1 @ X20)
% 4.28/4.48          | ~ (v1_relat_1 @ X20))),
% 4.28/4.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.28/4.48  thf('161', plain,
% 4.28/4.48      (![X20 : $i]:
% 4.28/4.48         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 4.28/4.48          | ~ (v1_funct_1 @ X20)
% 4.28/4.48          | ~ (v1_relat_1 @ X20))),
% 4.28/4.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.28/4.48  thf('162', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.28/4.48      inference('demod', [status(thm)], ['59', '60', '61', '62', '63', '64'])).
% 4.28/4.48  thf('163', plain,
% 4.28/4.48      (![X39 : $i]:
% 4.28/4.48         ((m1_subset_1 @ X39 @ 
% 4.28/4.48           (k1_zfmisc_1 @ 
% 4.28/4.48            (k2_zfmisc_1 @ (k1_relat_1 @ X39) @ (k2_relat_1 @ X39))))
% 4.28/4.48          | ~ (v1_funct_1 @ X39)
% 4.28/4.48          | ~ (v1_relat_1 @ X39))),
% 4.28/4.48      inference('cnf', [status(esa)], [t3_funct_2])).
% 4.28/4.48  thf('164', plain,
% 4.28/4.48      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.28/4.48         (k1_zfmisc_1 @ 
% 4.28/4.48          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 4.28/4.48        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 4.28/4.48        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 4.28/4.48      inference('sup+', [status(thm)], ['162', '163'])).
% 4.28/4.48  thf('165', plain,
% 4.28/4.48      ((~ (v1_relat_1 @ sk_C)
% 4.28/4.48        | ~ (v1_funct_1 @ sk_C)
% 4.28/4.48        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.28/4.48        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.28/4.48           (k1_zfmisc_1 @ 
% 4.28/4.48            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 4.28/4.48      inference('sup-', [status(thm)], ['161', '164'])).
% 4.28/4.48  thf('166', plain, ((v1_relat_1 @ sk_C)),
% 4.28/4.48      inference('demod', [status(thm)], ['4', '5'])).
% 4.28/4.48  thf('167', plain, ((v1_funct_1 @ sk_C)),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('168', plain,
% 4.28/4.48      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 4.28/4.48        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.28/4.48           (k1_zfmisc_1 @ 
% 4.28/4.48            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 4.28/4.48      inference('demod', [status(thm)], ['165', '166', '167'])).
% 4.28/4.48  thf('169', plain,
% 4.28/4.48      ((~ (v1_relat_1 @ sk_C)
% 4.28/4.48        | ~ (v1_funct_1 @ sk_C)
% 4.28/4.48        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.28/4.48           (k1_zfmisc_1 @ 
% 4.28/4.48            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 4.28/4.48      inference('sup-', [status(thm)], ['160', '168'])).
% 4.28/4.48  thf('170', plain, ((v1_relat_1 @ sk_C)),
% 4.28/4.48      inference('demod', [status(thm)], ['4', '5'])).
% 4.28/4.48  thf('171', plain, ((v1_funct_1 @ sk_C)),
% 4.28/4.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.48  thf('172', plain,
% 4.28/4.48      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.28/4.48        (k1_zfmisc_1 @ 
% 4.28/4.48         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 4.28/4.48      inference('demod', [status(thm)], ['169', '170', '171'])).
% 4.28/4.48  thf('173', plain,
% 4.28/4.48      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.28/4.48         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))
% 4.28/4.48        | ~ (v1_relat_1 @ sk_C)
% 4.28/4.48        | ~ (v1_funct_1 @ sk_C)
% 4.28/4.48        | ~ (v2_funct_1 @ sk_C))),
% 4.28/4.48      inference('sup+', [status(thm)], ['159', '172'])).
% 4.28/4.48  thf('174', plain,
% 4.28/4.48      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 4.28/4.48      inference('demod', [status(thm)], ['21', '24'])).
% 4.28/4.48  thf('175', plain,
% 4.28/4.48      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 4.28/4.48      inference('sup-', [status(thm)], ['15', '16'])).
% 4.28/4.48  thf('176', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 4.28/4.48      inference('sup+', [status(thm)], ['34', '35'])).
% 4.28/4.48  thf('177', plain,
% 4.28/4.48      (![X20 : $i]:
% 4.28/4.48         ((v1_relat_1 @ (k2_funct_1 @ X20))
% 4.28/4.48          | ~ (v1_funct_1 @ X20)
% 4.28/4.48          | ~ (v1_relat_1 @ X20))),
% 4.28/4.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.28/4.48  thf('178', plain,
% 4.28/4.48      (![X20 : $i]:
% 4.28/4.48         ((v1_funct_1 @ (k2_funct_1 @ X20))
% 4.28/4.48          | ~ (v1_funct_1 @ X20)
% 4.28/4.48          | ~ (v1_relat_1 @ X20))),
% 4.28/4.48      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 4.28/4.48  thf('179', plain,
% 4.28/4.49      (![X21 : $i]:
% 4.28/4.49         (~ (v2_funct_1 @ X21)
% 4.28/4.49          | ((k2_relat_1 @ X21) = (k1_relat_1 @ (k2_funct_1 @ X21)))
% 4.28/4.49          | ~ (v1_funct_1 @ X21)
% 4.28/4.49          | ~ (v1_relat_1 @ X21))),
% 4.28/4.49      inference('cnf', [status(esa)], [t55_funct_1])).
% 4.28/4.49  thf('180', plain,
% 4.28/4.49      (![X31 : $i, X32 : $i]:
% 4.28/4.49         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 4.28/4.49      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.28/4.49  thf('181', plain,
% 4.28/4.49      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 4.28/4.49      inference('simplify', [status(thm)], ['114'])).
% 4.28/4.49  thf('182', plain,
% 4.28/4.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.28/4.49         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 4.28/4.49      inference('sup+', [status(thm)], ['180', '181'])).
% 4.28/4.49  thf('183', plain,
% 4.28/4.49      (![X0 : $i]:
% 4.28/4.49         (~ (v1_relat_1 @ X0)
% 4.28/4.49          | ~ (v1_funct_1 @ X0)
% 4.28/4.49          | (r1_tarski @ X0 @ 
% 4.28/4.49             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 4.28/4.49      inference('sup-', [status(thm)], ['108', '109'])).
% 4.28/4.49  thf('184', plain,
% 4.28/4.49      (![X0 : $i, X1 : $i]:
% 4.28/4.49         ((r1_tarski @ X0 @ k1_xboole_0)
% 4.28/4.49          | (zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 4.28/4.49          | ~ (v1_funct_1 @ X0)
% 4.28/4.49          | ~ (v1_relat_1 @ X0))),
% 4.28/4.49      inference('sup+', [status(thm)], ['182', '183'])).
% 4.28/4.49  thf('185', plain,
% 4.28/4.49      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 4.28/4.49      inference('cnf', [status(esa)], [t3_xboole_1])).
% 4.28/4.49  thf('186', plain,
% 4.28/4.49      (![X0 : $i, X1 : $i]:
% 4.28/4.49         (~ (v1_relat_1 @ X0)
% 4.28/4.49          | ~ (v1_funct_1 @ X0)
% 4.28/4.49          | (zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 4.28/4.49          | ((X0) = (k1_xboole_0)))),
% 4.28/4.49      inference('sup-', [status(thm)], ['184', '185'])).
% 4.28/4.49  thf('187', plain,
% 4.28/4.49      (![X0 : $i, X1 : $i]:
% 4.28/4.49         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 4.28/4.49          | ~ (v1_relat_1 @ X0)
% 4.28/4.49          | ~ (v1_funct_1 @ X0)
% 4.28/4.49          | ~ (v2_funct_1 @ X0)
% 4.28/4.49          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 4.28/4.49          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 4.28/4.49          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 4.28/4.49      inference('sup+', [status(thm)], ['179', '186'])).
% 4.28/4.49  thf('188', plain,
% 4.28/4.49      (![X0 : $i, X1 : $i]:
% 4.28/4.49         (~ (v1_relat_1 @ X0)
% 4.28/4.49          | ~ (v1_funct_1 @ X0)
% 4.28/4.49          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 4.28/4.49          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 4.28/4.49          | ~ (v2_funct_1 @ X0)
% 4.28/4.49          | ~ (v1_funct_1 @ X0)
% 4.28/4.49          | ~ (v1_relat_1 @ X0)
% 4.28/4.49          | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1))),
% 4.28/4.49      inference('sup-', [status(thm)], ['178', '187'])).
% 4.28/4.49  thf('189', plain,
% 4.28/4.49      (![X0 : $i, X1 : $i]:
% 4.28/4.49         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 4.28/4.49          | ~ (v2_funct_1 @ X0)
% 4.28/4.49          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 4.28/4.49          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 4.28/4.49          | ~ (v1_funct_1 @ X0)
% 4.28/4.49          | ~ (v1_relat_1 @ X0))),
% 4.28/4.49      inference('simplify', [status(thm)], ['188'])).
% 4.28/4.49  thf('190', plain,
% 4.28/4.49      (![X0 : $i, X1 : $i]:
% 4.28/4.49         (~ (v1_relat_1 @ X0)
% 4.28/4.49          | ~ (v1_funct_1 @ X0)
% 4.28/4.49          | ~ (v1_relat_1 @ X0)
% 4.28/4.49          | ~ (v1_funct_1 @ X0)
% 4.28/4.49          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 4.28/4.49          | ~ (v2_funct_1 @ X0)
% 4.28/4.49          | (zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1))),
% 4.28/4.49      inference('sup-', [status(thm)], ['177', '189'])).
% 4.28/4.49  thf('191', plain,
% 4.28/4.49      (![X0 : $i, X1 : $i]:
% 4.28/4.49         ((zip_tseitin_0 @ (k2_relat_1 @ X0) @ X1)
% 4.28/4.49          | ~ (v2_funct_1 @ X0)
% 4.28/4.49          | ((k2_funct_1 @ X0) = (k1_xboole_0))
% 4.28/4.49          | ~ (v1_funct_1 @ X0)
% 4.28/4.49          | ~ (v1_relat_1 @ X0))),
% 4.28/4.49      inference('simplify', [status(thm)], ['190'])).
% 4.28/4.49  thf('192', plain,
% 4.28/4.49      (![X0 : $i]:
% 4.28/4.49         ((zip_tseitin_0 @ sk_B @ X0)
% 4.28/4.49          | ~ (v1_relat_1 @ sk_C)
% 4.28/4.49          | ~ (v1_funct_1 @ sk_C)
% 4.28/4.49          | ((k2_funct_1 @ sk_C) = (k1_xboole_0))
% 4.28/4.49          | ~ (v2_funct_1 @ sk_C))),
% 4.28/4.49      inference('sup+', [status(thm)], ['176', '191'])).
% 4.28/4.49  thf('193', plain, ((v1_relat_1 @ sk_C)),
% 4.28/4.49      inference('demod', [status(thm)], ['4', '5'])).
% 4.28/4.49  thf('194', plain, ((v1_funct_1 @ sk_C)),
% 4.28/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.49  thf('195', plain, ((v2_funct_1 @ sk_C)),
% 4.28/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.49  thf('196', plain,
% 4.28/4.49      (![X0 : $i]:
% 4.28/4.49         ((zip_tseitin_0 @ sk_B @ X0) | ((k2_funct_1 @ sk_C) = (k1_xboole_0)))),
% 4.28/4.49      inference('demod', [status(thm)], ['192', '193', '194', '195'])).
% 4.28/4.49  thf('197', plain,
% 4.28/4.49      (~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.28/4.49          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.28/4.49      inference('simpl_trail', [status(thm)], ['1', '157'])).
% 4.28/4.49  thf('198', plain,
% 4.28/4.49      (![X0 : $i]:
% 4.28/4.49         (~ (m1_subset_1 @ k1_xboole_0 @ 
% 4.28/4.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 4.28/4.49          | (zip_tseitin_0 @ sk_B @ X0))),
% 4.28/4.49      inference('sup-', [status(thm)], ['196', '197'])).
% 4.28/4.49  thf('199', plain,
% 4.28/4.49      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 4.28/4.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.28/4.49  thf('200', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0)),
% 4.28/4.49      inference('demod', [status(thm)], ['198', '199'])).
% 4.28/4.49  thf('201', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 4.28/4.49      inference('demod', [status(thm)], ['175', '200'])).
% 4.28/4.49  thf('202', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 4.28/4.49      inference('demod', [status(thm)], ['174', '201'])).
% 4.28/4.49  thf('203', plain, ((v1_relat_1 @ sk_C)),
% 4.28/4.49      inference('demod', [status(thm)], ['4', '5'])).
% 4.28/4.49  thf('204', plain, ((v1_funct_1 @ sk_C)),
% 4.28/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.49  thf('205', plain, ((v2_funct_1 @ sk_C)),
% 4.28/4.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.28/4.49  thf('206', plain,
% 4.28/4.49      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.28/4.49        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 4.28/4.49      inference('demod', [status(thm)], ['173', '202', '203', '204', '205'])).
% 4.28/4.49  thf('207', plain, ($false), inference('demod', [status(thm)], ['158', '206'])).
% 4.28/4.49  
% 4.28/4.49  % SZS output end Refutation
% 4.28/4.49  
% 4.28/4.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
