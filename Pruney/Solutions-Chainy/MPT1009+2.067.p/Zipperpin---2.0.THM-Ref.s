%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5Ef7QyG7lA

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:58 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 286 expanded)
%              Number of leaves         :   41 ( 105 expanded)
%              Depth                    :   12
%              Number of atoms          :  761 (3973 expanded)
%              Number of equality atoms :   59 ( 219 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k7_relset_1 @ X25 @ X26 @ X24 @ X27 )
        = ( k9_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ ( k1_tarski @ sk_A ) @ sk_B ),
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

thf('7',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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

thf('11',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['8','15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','19'])).

thf('21',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['8','15','18'])).

thf(t62_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( X36 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ ( k1_tarski @ X38 ) @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X38 ) @ X36 ) ) )
      | ( ( k2_relset_1 @ ( k1_tarski @ X38 ) @ X36 @ X37 )
        = ( k1_tarski @ ( k1_funct_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[t62_funct_2])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) )
      | ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ X0 @ X1 )
        = ( k1_tarski @ ( k1_funct_1 @ X1 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( k1_tarski @ sk_A ) @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['8','15','18'])).

thf('25',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['8','15','18'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_D ) @ X0 @ X1 )
        = ( k1_tarski @ ( k1_funct_1 @ X1 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( k1_relat_1 @ sk_D ) @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_B )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_2 @ sk_D @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['8','15','18'])).

thf('31',plain,(
    v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('34',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['8','15','18'])).

thf('36',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28','31','36'])).

thf('38',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('41',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v4_relat_1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('42',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('46',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('47',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) )
        = ( k9_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('50',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['45','46'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['8','15','18'])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf(t147_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) )).

thf('55',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X6 @ X7 ) @ ( k9_relat_1 @ X6 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t147_relat_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['45','46'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['4','39','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5Ef7QyG7lA
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:39:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.72/0.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.72/0.90  % Solved by: fo/fo7.sh
% 0.72/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.72/0.90  % done 251 iterations in 0.446s
% 0.72/0.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.72/0.90  % SZS output start Refutation
% 0.72/0.90  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.72/0.90  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.72/0.90  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.72/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.72/0.90  thf(sk_D_type, type, sk_D: $i).
% 0.72/0.90  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.72/0.90  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.72/0.90  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.72/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.72/0.90  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.72/0.90  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.72/0.90  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.72/0.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.72/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.72/0.90  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.72/0.90  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.72/0.90  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.72/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.72/0.90  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.72/0.90  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.72/0.90  thf(sk_C_type, type, sk_C: $i).
% 0.72/0.90  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.72/0.90  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.72/0.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.72/0.90  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.72/0.90  thf(t64_funct_2, conjecture,
% 0.72/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.72/0.90     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.72/0.90         ( m1_subset_1 @
% 0.72/0.90           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.72/0.90       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.72/0.90         ( r1_tarski @
% 0.72/0.90           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.72/0.90           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.72/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.72/0.90    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.72/0.90        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.72/0.90            ( m1_subset_1 @
% 0.72/0.90              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.72/0.90          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.72/0.90            ( r1_tarski @
% 0.72/0.90              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.72/0.90              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.72/0.90    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.72/0.90  thf('0', plain,
% 0.72/0.90      (~ (r1_tarski @ 
% 0.72/0.90          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.72/0.90          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('1', plain,
% 0.72/0.90      ((m1_subset_1 @ sk_D @ 
% 0.72/0.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf(redefinition_k7_relset_1, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.72/0.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.72/0.90       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.72/0.90  thf('2', plain,
% 0.72/0.90      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.72/0.90         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.72/0.90          | ((k7_relset_1 @ X25 @ X26 @ X24 @ X27) = (k9_relat_1 @ X24 @ X27)))),
% 0.72/0.90      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.72/0.90  thf('3', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.72/0.90           = (k9_relat_1 @ sk_D @ X0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['1', '2'])).
% 0.72/0.90  thf('4', plain,
% 0.72/0.90      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.72/0.90          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.72/0.90      inference('demod', [status(thm)], ['0', '3'])).
% 0.72/0.90  thf('5', plain,
% 0.72/0.90      ((m1_subset_1 @ sk_D @ 
% 0.72/0.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('6', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf(d1_funct_2, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.72/0.90       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.72/0.90           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.72/0.90             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.72/0.90         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.72/0.90           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.72/0.90             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.72/0.90  thf(zf_stmt_1, axiom,
% 0.72/0.90    (![C:$i,B:$i,A:$i]:
% 0.72/0.90     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.72/0.90       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.72/0.90  thf('7', plain,
% 0.72/0.90      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.72/0.90         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 0.72/0.90          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 0.72/0.90          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.72/0.90  thf('8', plain,
% 0.72/0.90      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.72/0.90        | ((k1_tarski @ sk_A)
% 0.72/0.90            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['6', '7'])).
% 0.72/0.90  thf(zf_stmt_2, axiom,
% 0.72/0.90    (![B:$i,A:$i]:
% 0.72/0.90     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.72/0.90       ( zip_tseitin_0 @ B @ A ) ))).
% 0.72/0.90  thf('9', plain,
% 0.72/0.90      (![X28 : $i, X29 : $i]:
% 0.72/0.90         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.72/0.90  thf('10', plain,
% 0.72/0.90      ((m1_subset_1 @ sk_D @ 
% 0.72/0.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.72/0.90  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.72/0.90  thf(zf_stmt_5, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.72/0.90       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.72/0.90         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.72/0.90           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.72/0.90             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.72/0.90  thf('11', plain,
% 0.72/0.90      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.72/0.90         (~ (zip_tseitin_0 @ X33 @ X34)
% 0.72/0.90          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 0.72/0.90          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.72/0.90  thf('12', plain,
% 0.72/0.90      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.72/0.90        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['10', '11'])).
% 0.72/0.90  thf('13', plain,
% 0.72/0.90      ((((sk_B) = (k1_xboole_0))
% 0.72/0.90        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['9', '12'])).
% 0.72/0.90  thf('14', plain, (((sk_B) != (k1_xboole_0))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('15', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))),
% 0.72/0.90      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.72/0.90  thf('16', plain,
% 0.72/0.90      ((m1_subset_1 @ sk_D @ 
% 0.72/0.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf(redefinition_k1_relset_1, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.72/0.90       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.72/0.90  thf('17', plain,
% 0.72/0.90      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.72/0.90         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.72/0.90          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.72/0.90      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.72/0.90  thf('18', plain,
% 0.72/0.90      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.72/0.90      inference('sup-', [status(thm)], ['16', '17'])).
% 0.72/0.90  thf('19', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.72/0.90      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.72/0.90  thf('20', plain,
% 0.72/0.90      ((m1_subset_1 @ sk_D @ 
% 0.72/0.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.72/0.90      inference('demod', [status(thm)], ['5', '19'])).
% 0.72/0.90  thf('21', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.72/0.90      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.72/0.90  thf(t62_funct_2, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.72/0.90         ( m1_subset_1 @
% 0.72/0.90           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.72/0.90       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.72/0.90         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.72/0.90           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.72/0.90  thf('22', plain,
% 0.72/0.90      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.72/0.90         (((X36) = (k1_xboole_0))
% 0.72/0.90          | ~ (v1_funct_1 @ X37)
% 0.72/0.90          | ~ (v1_funct_2 @ X37 @ (k1_tarski @ X38) @ X36)
% 0.72/0.90          | ~ (m1_subset_1 @ X37 @ 
% 0.72/0.90               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ X38) @ X36)))
% 0.72/0.90          | ((k2_relset_1 @ (k1_tarski @ X38) @ X36 @ X37)
% 0.72/0.90              = (k1_tarski @ (k1_funct_1 @ X37 @ X38))))),
% 0.72/0.90      inference('cnf', [status(esa)], [t62_funct_2])).
% 0.72/0.90  thf('23', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (~ (m1_subset_1 @ X1 @ 
% 0.72/0.90             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0)))
% 0.72/0.90          | ((k2_relset_1 @ (k1_tarski @ sk_A) @ X0 @ X1)
% 0.72/0.90              = (k1_tarski @ (k1_funct_1 @ X1 @ sk_A)))
% 0.72/0.90          | ~ (v1_funct_2 @ X1 @ (k1_tarski @ sk_A) @ X0)
% 0.72/0.90          | ~ (v1_funct_1 @ X1)
% 0.72/0.90          | ((X0) = (k1_xboole_0)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['21', '22'])).
% 0.72/0.90  thf('24', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.72/0.90      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.72/0.90  thf('25', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.72/0.90      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.72/0.90  thf('26', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         (~ (m1_subset_1 @ X1 @ 
% 0.72/0.90             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0)))
% 0.72/0.90          | ((k2_relset_1 @ (k1_relat_1 @ sk_D) @ X0 @ X1)
% 0.72/0.90              = (k1_tarski @ (k1_funct_1 @ X1 @ sk_A)))
% 0.72/0.90          | ~ (v1_funct_2 @ X1 @ (k1_relat_1 @ sk_D) @ X0)
% 0.72/0.90          | ~ (v1_funct_1 @ X1)
% 0.72/0.90          | ((X0) = (k1_xboole_0)))),
% 0.72/0.90      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.72/0.90  thf('27', plain,
% 0.72/0.90      ((((sk_B) = (k1_xboole_0))
% 0.72/0.90        | ~ (v1_funct_1 @ sk_D)
% 0.72/0.90        | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_B)
% 0.72/0.90        | ((k2_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D)
% 0.72/0.90            = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A))))),
% 0.72/0.90      inference('sup-', [status(thm)], ['20', '26'])).
% 0.72/0.90  thf('28', plain, ((v1_funct_1 @ sk_D)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('29', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('30', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.72/0.90      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.72/0.90  thf('31', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_B)),
% 0.72/0.90      inference('demod', [status(thm)], ['29', '30'])).
% 0.72/0.90  thf('32', plain,
% 0.72/0.90      ((m1_subset_1 @ sk_D @ 
% 0.72/0.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf(redefinition_k2_relset_1, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.72/0.90       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.72/0.90  thf('33', plain,
% 0.72/0.90      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.72/0.90         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.72/0.90          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.72/0.90      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.72/0.90  thf('34', plain,
% 0.72/0.90      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.72/0.90      inference('sup-', [status(thm)], ['32', '33'])).
% 0.72/0.90  thf('35', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.72/0.90      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.72/0.90  thf('36', plain,
% 0.72/0.90      (((k2_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.72/0.90      inference('demod', [status(thm)], ['34', '35'])).
% 0.72/0.90  thf('37', plain,
% 0.72/0.90      ((((sk_B) = (k1_xboole_0))
% 0.72/0.90        | ((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A))))),
% 0.72/0.90      inference('demod', [status(thm)], ['27', '28', '31', '36'])).
% 0.72/0.90  thf('38', plain, (((sk_B) != (k1_xboole_0))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('39', plain,
% 0.72/0.90      (((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.72/0.90      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.72/0.90  thf('40', plain,
% 0.72/0.90      ((m1_subset_1 @ sk_D @ 
% 0.72/0.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf(cc2_relset_1, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.72/0.90       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.72/0.90  thf('41', plain,
% 0.72/0.90      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.72/0.90         ((v4_relat_1 @ X15 @ X16)
% 0.72/0.90          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.72/0.90      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.72/0.90  thf('42', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.72/0.90      inference('sup-', [status(thm)], ['40', '41'])).
% 0.72/0.90  thf(t209_relat_1, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.72/0.90       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.72/0.90  thf('43', plain,
% 0.72/0.90      (![X10 : $i, X11 : $i]:
% 0.72/0.90         (((X10) = (k7_relat_1 @ X10 @ X11))
% 0.72/0.90          | ~ (v4_relat_1 @ X10 @ X11)
% 0.72/0.90          | ~ (v1_relat_1 @ X10))),
% 0.72/0.90      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.72/0.90  thf('44', plain,
% 0.72/0.90      ((~ (v1_relat_1 @ sk_D)
% 0.72/0.90        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A))))),
% 0.72/0.90      inference('sup-', [status(thm)], ['42', '43'])).
% 0.72/0.90  thf('45', plain,
% 0.72/0.90      ((m1_subset_1 @ sk_D @ 
% 0.72/0.90        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf(cc1_relset_1, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.72/0.90       ( v1_relat_1 @ C ) ))).
% 0.72/0.90  thf('46', plain,
% 0.72/0.90      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.72/0.90         ((v1_relat_1 @ X12)
% 0.72/0.90          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.72/0.90      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.72/0.90  thf('47', plain, ((v1_relat_1 @ sk_D)),
% 0.72/0.90      inference('sup-', [status(thm)], ['45', '46'])).
% 0.72/0.90  thf('48', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.72/0.90      inference('demod', [status(thm)], ['44', '47'])).
% 0.72/0.90  thf(t148_relat_1, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( v1_relat_1 @ B ) =>
% 0.72/0.90       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.72/0.90  thf('49', plain,
% 0.72/0.90      (![X8 : $i, X9 : $i]:
% 0.72/0.90         (((k2_relat_1 @ (k7_relat_1 @ X8 @ X9)) = (k9_relat_1 @ X8 @ X9))
% 0.72/0.90          | ~ (v1_relat_1 @ X8))),
% 0.72/0.90      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.72/0.90  thf('50', plain,
% 0.72/0.90      ((((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))
% 0.72/0.90        | ~ (v1_relat_1 @ sk_D))),
% 0.72/0.90      inference('sup+', [status(thm)], ['48', '49'])).
% 0.72/0.90  thf('51', plain, ((v1_relat_1 @ sk_D)),
% 0.72/0.90      inference('sup-', [status(thm)], ['45', '46'])).
% 0.72/0.90  thf('52', plain,
% 0.72/0.90      (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.72/0.90      inference('demod', [status(thm)], ['50', '51'])).
% 0.72/0.90  thf('53', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.72/0.90      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.72/0.90  thf('54', plain,
% 0.72/0.90      (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 0.72/0.90      inference('demod', [status(thm)], ['52', '53'])).
% 0.72/0.90  thf(t147_relat_1, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( v1_relat_1 @ B ) =>
% 0.72/0.90       ( r1_tarski @
% 0.72/0.90         ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ))).
% 0.72/0.90  thf('55', plain,
% 0.72/0.90      (![X6 : $i, X7 : $i]:
% 0.72/0.90         ((r1_tarski @ (k9_relat_1 @ X6 @ X7) @ 
% 0.72/0.90           (k9_relat_1 @ X6 @ (k1_relat_1 @ X6)))
% 0.72/0.90          | ~ (v1_relat_1 @ X6))),
% 0.72/0.90      inference('cnf', [status(esa)], [t147_relat_1])).
% 0.72/0.90  thf('56', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         ((r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))
% 0.72/0.90          | ~ (v1_relat_1 @ sk_D))),
% 0.72/0.90      inference('sup+', [status(thm)], ['54', '55'])).
% 0.72/0.90  thf('57', plain, ((v1_relat_1 @ sk_D)),
% 0.72/0.90      inference('sup-', [status(thm)], ['45', '46'])).
% 0.72/0.90  thf('58', plain,
% 0.72/0.90      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))),
% 0.72/0.90      inference('demod', [status(thm)], ['56', '57'])).
% 0.72/0.90  thf('59', plain, ($false),
% 0.72/0.90      inference('demod', [status(thm)], ['4', '39', '58'])).
% 0.72/0.90  
% 0.72/0.90  % SZS output end Refutation
% 0.72/0.90  
% 0.72/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
