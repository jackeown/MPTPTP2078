%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uu63r6BfIt

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:09 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 295 expanded)
%              Number of leaves         :   42 ( 108 expanded)
%              Depth                    :   12
%              Number of atoms          :  776 (4018 expanded)
%              Number of equality atoms :   59 ( 219 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

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
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k7_relset_1 @ X26 @ X27 @ X25 @ X28 )
        = ( k9_relat_1 @ X25 @ X28 ) ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
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
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ ( k1_tarski @ X39 ) @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X39 ) @ X37 ) ) )
      | ( ( k2_relset_1 @ ( k1_tarski @ X39 ) @ X37 @ X38 )
        = ( k1_tarski @ ( k1_funct_1 @ X38 @ X39 ) ) ) ) ),
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
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ( X14
        = ( k7_relat_1 @ X14 @ X15 ) )
      | ~ ( v4_relat_1 @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('46',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('48',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('49',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','49'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('51',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) )
        = ( k9_relat_1 @ X12 @ X13 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('52',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['47','48'])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['8','15','18'])).

thf('56',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(t147_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) )).

thf('57',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X10 @ X11 ) @ ( k9_relat_1 @ X10 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t147_relat_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['47','48'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['4','39','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uu63r6BfIt
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:10:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.74/0.94  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.74/0.94  % Solved by: fo/fo7.sh
% 0.74/0.94  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.94  % done 250 iterations in 0.478s
% 0.74/0.94  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.74/0.94  % SZS output start Refutation
% 0.74/0.94  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.74/0.94  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.74/0.94  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.74/0.94  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.74/0.94  thf(sk_B_type, type, sk_B: $i).
% 0.74/0.94  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.74/0.94  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.74/0.94  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.74/0.94  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.74/0.94  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.74/0.94  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.94  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.74/0.94  thf(sk_D_type, type, sk_D: $i).
% 0.74/0.94  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.74/0.94  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.74/0.94  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.74/0.94  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.74/0.94  thf(sk_C_type, type, sk_C: $i).
% 0.74/0.94  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.74/0.94  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.74/0.94  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.74/0.94  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.74/0.94  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.74/0.94  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.74/0.94  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.74/0.94  thf(t64_funct_2, conjecture,
% 0.74/0.94    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.94     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.74/0.94         ( m1_subset_1 @
% 0.74/0.94           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.74/0.94       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.74/0.94         ( r1_tarski @
% 0.74/0.94           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.74/0.94           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.74/0.94  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.94    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.94        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.74/0.94            ( m1_subset_1 @
% 0.74/0.94              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.74/0.94          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.74/0.94            ( r1_tarski @
% 0.74/0.94              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.74/0.94              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.74/0.94    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.74/0.94  thf('0', plain,
% 0.74/0.94      (~ (r1_tarski @ 
% 0.74/0.94          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.74/0.94          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('1', plain,
% 0.74/0.94      ((m1_subset_1 @ sk_D @ 
% 0.74/0.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf(redefinition_k7_relset_1, axiom,
% 0.74/0.94    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.94       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.74/0.94  thf('2', plain,
% 0.74/0.94      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.74/0.94         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.74/0.94          | ((k7_relset_1 @ X26 @ X27 @ X25 @ X28) = (k9_relat_1 @ X25 @ X28)))),
% 0.74/0.94      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.74/0.94  thf('3', plain,
% 0.74/0.94      (![X0 : $i]:
% 0.74/0.94         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.74/0.94           = (k9_relat_1 @ sk_D @ X0))),
% 0.74/0.94      inference('sup-', [status(thm)], ['1', '2'])).
% 0.74/0.94  thf('4', plain,
% 0.74/0.94      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.74/0.94          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.74/0.94      inference('demod', [status(thm)], ['0', '3'])).
% 0.74/0.94  thf('5', plain,
% 0.74/0.94      ((m1_subset_1 @ sk_D @ 
% 0.74/0.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('6', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf(d1_funct_2, axiom,
% 0.74/0.94    (![A:$i,B:$i,C:$i]:
% 0.74/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.94       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.74/0.94           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.74/0.94             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.74/0.94         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.74/0.94           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.74/0.94             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.74/0.94  thf(zf_stmt_1, axiom,
% 0.74/0.94    (![C:$i,B:$i,A:$i]:
% 0.74/0.94     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.74/0.94       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.74/0.94  thf('7', plain,
% 0.74/0.94      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.74/0.94         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.74/0.94          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 0.74/0.94          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.74/0.94  thf('8', plain,
% 0.74/0.94      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.74/0.94        | ((k1_tarski @ sk_A)
% 0.74/0.94            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D)))),
% 0.74/0.94      inference('sup-', [status(thm)], ['6', '7'])).
% 0.74/0.94  thf(zf_stmt_2, axiom,
% 0.74/0.94    (![B:$i,A:$i]:
% 0.74/0.94     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.74/0.94       ( zip_tseitin_0 @ B @ A ) ))).
% 0.74/0.94  thf('9', plain,
% 0.74/0.94      (![X29 : $i, X30 : $i]:
% 0.74/0.94         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.74/0.94  thf('10', plain,
% 0.74/0.94      ((m1_subset_1 @ sk_D @ 
% 0.74/0.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.74/0.94  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.74/0.94  thf(zf_stmt_5, axiom,
% 0.74/0.94    (![A:$i,B:$i,C:$i]:
% 0.74/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.94       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.74/0.94         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.74/0.94           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.74/0.94             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.74/0.94  thf('11', plain,
% 0.74/0.94      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.74/0.94         (~ (zip_tseitin_0 @ X34 @ X35)
% 0.74/0.94          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 0.74/0.94          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.74/0.94  thf('12', plain,
% 0.74/0.94      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.74/0.94        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.74/0.94      inference('sup-', [status(thm)], ['10', '11'])).
% 0.74/0.94  thf('13', plain,
% 0.74/0.94      ((((sk_B) = (k1_xboole_0))
% 0.74/0.94        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A)))),
% 0.74/0.94      inference('sup-', [status(thm)], ['9', '12'])).
% 0.74/0.94  thf('14', plain, (((sk_B) != (k1_xboole_0))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('15', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))),
% 0.74/0.94      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.74/0.94  thf('16', plain,
% 0.74/0.94      ((m1_subset_1 @ sk_D @ 
% 0.74/0.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf(redefinition_k1_relset_1, axiom,
% 0.74/0.94    (![A:$i,B:$i,C:$i]:
% 0.74/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.94       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.74/0.94  thf('17', plain,
% 0.74/0.94      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.74/0.94         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.74/0.94          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.74/0.94      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.74/0.94  thf('18', plain,
% 0.74/0.94      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.74/0.94      inference('sup-', [status(thm)], ['16', '17'])).
% 0.74/0.94  thf('19', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.74/0.94      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.74/0.94  thf('20', plain,
% 0.74/0.94      ((m1_subset_1 @ sk_D @ 
% 0.74/0.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.74/0.94      inference('demod', [status(thm)], ['5', '19'])).
% 0.74/0.94  thf('21', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.74/0.94      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.74/0.94  thf(t62_funct_2, axiom,
% 0.74/0.94    (![A:$i,B:$i,C:$i]:
% 0.74/0.94     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.74/0.94         ( m1_subset_1 @
% 0.74/0.94           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.74/0.94       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.74/0.94         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.74/0.94           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.74/0.94  thf('22', plain,
% 0.74/0.94      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.74/0.94         (((X37) = (k1_xboole_0))
% 0.74/0.94          | ~ (v1_funct_1 @ X38)
% 0.74/0.94          | ~ (v1_funct_2 @ X38 @ (k1_tarski @ X39) @ X37)
% 0.74/0.94          | ~ (m1_subset_1 @ X38 @ 
% 0.74/0.94               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ X39) @ X37)))
% 0.74/0.94          | ((k2_relset_1 @ (k1_tarski @ X39) @ X37 @ X38)
% 0.74/0.94              = (k1_tarski @ (k1_funct_1 @ X38 @ X39))))),
% 0.74/0.94      inference('cnf', [status(esa)], [t62_funct_2])).
% 0.74/0.94  thf('23', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         (~ (m1_subset_1 @ X1 @ 
% 0.74/0.94             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0)))
% 0.74/0.94          | ((k2_relset_1 @ (k1_tarski @ sk_A) @ X0 @ X1)
% 0.74/0.94              = (k1_tarski @ (k1_funct_1 @ X1 @ sk_A)))
% 0.74/0.94          | ~ (v1_funct_2 @ X1 @ (k1_tarski @ sk_A) @ X0)
% 0.74/0.94          | ~ (v1_funct_1 @ X1)
% 0.74/0.94          | ((X0) = (k1_xboole_0)))),
% 0.74/0.94      inference('sup-', [status(thm)], ['21', '22'])).
% 0.74/0.94  thf('24', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.74/0.94      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.74/0.94  thf('25', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.74/0.94      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.74/0.94  thf('26', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i]:
% 0.74/0.94         (~ (m1_subset_1 @ X1 @ 
% 0.74/0.94             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0)))
% 0.74/0.94          | ((k2_relset_1 @ (k1_relat_1 @ sk_D) @ X0 @ X1)
% 0.74/0.94              = (k1_tarski @ (k1_funct_1 @ X1 @ sk_A)))
% 0.74/0.94          | ~ (v1_funct_2 @ X1 @ (k1_relat_1 @ sk_D) @ X0)
% 0.74/0.94          | ~ (v1_funct_1 @ X1)
% 0.74/0.94          | ((X0) = (k1_xboole_0)))),
% 0.74/0.94      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.74/0.94  thf('27', plain,
% 0.74/0.94      ((((sk_B) = (k1_xboole_0))
% 0.74/0.94        | ~ (v1_funct_1 @ sk_D)
% 0.74/0.94        | ~ (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_B)
% 0.74/0.94        | ((k2_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D)
% 0.74/0.94            = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A))))),
% 0.74/0.94      inference('sup-', [status(thm)], ['20', '26'])).
% 0.74/0.94  thf('28', plain, ((v1_funct_1 @ sk_D)),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('29', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('30', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.74/0.94      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.74/0.94  thf('31', plain, ((v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_B)),
% 0.74/0.94      inference('demod', [status(thm)], ['29', '30'])).
% 0.74/0.94  thf('32', plain,
% 0.74/0.94      ((m1_subset_1 @ sk_D @ 
% 0.74/0.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf(redefinition_k2_relset_1, axiom,
% 0.74/0.94    (![A:$i,B:$i,C:$i]:
% 0.74/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.94       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.74/0.94  thf('33', plain,
% 0.74/0.94      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.74/0.94         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 0.74/0.94          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.74/0.94      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.74/0.94  thf('34', plain,
% 0.74/0.94      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.74/0.94      inference('sup-', [status(thm)], ['32', '33'])).
% 0.74/0.94  thf('35', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.74/0.94      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.74/0.94  thf('36', plain,
% 0.74/0.94      (((k2_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.74/0.94      inference('demod', [status(thm)], ['34', '35'])).
% 0.74/0.94  thf('37', plain,
% 0.74/0.94      ((((sk_B) = (k1_xboole_0))
% 0.74/0.94        | ((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A))))),
% 0.74/0.94      inference('demod', [status(thm)], ['27', '28', '31', '36'])).
% 0.74/0.94  thf('38', plain, (((sk_B) != (k1_xboole_0))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('39', plain,
% 0.74/0.94      (((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.74/0.94      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.74/0.94  thf('40', plain,
% 0.74/0.94      ((m1_subset_1 @ sk_D @ 
% 0.74/0.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf(cc2_relset_1, axiom,
% 0.74/0.94    (![A:$i,B:$i,C:$i]:
% 0.74/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.94       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.74/0.94  thf('41', plain,
% 0.74/0.94      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.74/0.94         ((v4_relat_1 @ X16 @ X17)
% 0.74/0.94          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.74/0.94      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.74/0.94  thf('42', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.74/0.94      inference('sup-', [status(thm)], ['40', '41'])).
% 0.74/0.94  thf(t209_relat_1, axiom,
% 0.74/0.94    (![A:$i,B:$i]:
% 0.74/0.94     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.74/0.94       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.74/0.94  thf('43', plain,
% 0.74/0.94      (![X14 : $i, X15 : $i]:
% 0.74/0.94         (((X14) = (k7_relat_1 @ X14 @ X15))
% 0.74/0.94          | ~ (v4_relat_1 @ X14 @ X15)
% 0.74/0.94          | ~ (v1_relat_1 @ X14))),
% 0.74/0.94      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.74/0.94  thf('44', plain,
% 0.74/0.94      ((~ (v1_relat_1 @ sk_D)
% 0.74/0.94        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A))))),
% 0.74/0.94      inference('sup-', [status(thm)], ['42', '43'])).
% 0.74/0.94  thf('45', plain,
% 0.74/0.94      ((m1_subset_1 @ sk_D @ 
% 0.74/0.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf(cc2_relat_1, axiom,
% 0.74/0.94    (![A:$i]:
% 0.74/0.94     ( ( v1_relat_1 @ A ) =>
% 0.74/0.94       ( ![B:$i]:
% 0.74/0.94         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.74/0.94  thf('46', plain,
% 0.74/0.94      (![X6 : $i, X7 : $i]:
% 0.74/0.94         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.74/0.94          | (v1_relat_1 @ X6)
% 0.74/0.94          | ~ (v1_relat_1 @ X7))),
% 0.74/0.94      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.74/0.94  thf('47', plain,
% 0.74/0.94      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.74/0.94        | (v1_relat_1 @ sk_D))),
% 0.74/0.94      inference('sup-', [status(thm)], ['45', '46'])).
% 0.74/0.94  thf(fc6_relat_1, axiom,
% 0.74/0.94    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.74/0.94  thf('48', plain,
% 0.74/0.94      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.74/0.94      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.74/0.94  thf('49', plain, ((v1_relat_1 @ sk_D)),
% 0.74/0.94      inference('demod', [status(thm)], ['47', '48'])).
% 0.74/0.94  thf('50', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.74/0.94      inference('demod', [status(thm)], ['44', '49'])).
% 0.74/0.94  thf(t148_relat_1, axiom,
% 0.74/0.94    (![A:$i,B:$i]:
% 0.74/0.94     ( ( v1_relat_1 @ B ) =>
% 0.74/0.94       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.74/0.94  thf('51', plain,
% 0.74/0.94      (![X12 : $i, X13 : $i]:
% 0.74/0.94         (((k2_relat_1 @ (k7_relat_1 @ X12 @ X13)) = (k9_relat_1 @ X12 @ X13))
% 0.74/0.94          | ~ (v1_relat_1 @ X12))),
% 0.74/0.94      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.74/0.94  thf('52', plain,
% 0.74/0.94      ((((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))
% 0.74/0.94        | ~ (v1_relat_1 @ sk_D))),
% 0.74/0.94      inference('sup+', [status(thm)], ['50', '51'])).
% 0.74/0.94  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 0.74/0.94      inference('demod', [status(thm)], ['47', '48'])).
% 0.74/0.94  thf('54', plain,
% 0.74/0.94      (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.74/0.94      inference('demod', [status(thm)], ['52', '53'])).
% 0.74/0.94  thf('55', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.74/0.94      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.74/0.94  thf('56', plain,
% 0.74/0.94      (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 0.74/0.94      inference('demod', [status(thm)], ['54', '55'])).
% 0.74/0.94  thf(t147_relat_1, axiom,
% 0.74/0.94    (![A:$i,B:$i]:
% 0.74/0.94     ( ( v1_relat_1 @ B ) =>
% 0.74/0.94       ( r1_tarski @
% 0.74/0.94         ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ))).
% 0.74/0.94  thf('57', plain,
% 0.74/0.94      (![X10 : $i, X11 : $i]:
% 0.74/0.94         ((r1_tarski @ (k9_relat_1 @ X10 @ X11) @ 
% 0.74/0.94           (k9_relat_1 @ X10 @ (k1_relat_1 @ X10)))
% 0.74/0.94          | ~ (v1_relat_1 @ X10))),
% 0.74/0.94      inference('cnf', [status(esa)], [t147_relat_1])).
% 0.74/0.94  thf('58', plain,
% 0.74/0.94      (![X0 : $i]:
% 0.74/0.94         ((r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))
% 0.74/0.94          | ~ (v1_relat_1 @ sk_D))),
% 0.74/0.94      inference('sup+', [status(thm)], ['56', '57'])).
% 0.74/0.94  thf('59', plain, ((v1_relat_1 @ sk_D)),
% 0.74/0.94      inference('demod', [status(thm)], ['47', '48'])).
% 0.74/0.94  thf('60', plain,
% 0.74/0.94      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))),
% 0.74/0.94      inference('demod', [status(thm)], ['58', '59'])).
% 0.74/0.94  thf('61', plain, ($false),
% 0.74/0.94      inference('demod', [status(thm)], ['4', '39', '60'])).
% 0.74/0.94  
% 0.74/0.94  % SZS output end Refutation
% 0.74/0.94  
% 0.77/0.95  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
