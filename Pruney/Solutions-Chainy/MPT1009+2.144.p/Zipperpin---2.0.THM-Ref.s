%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w7rtejlx68

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:09 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 682 expanded)
%              Number of leaves         :   47 ( 225 expanded)
%              Depth                    :   21
%              Number of atoms          : 1149 (10104 expanded)
%              Number of equality atoms :   60 ( 485 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k7_relset_1 @ X19 @ X20 @ X18 @ X21 )
        = ( k9_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D_1 @ ( k1_tarski @ sk_A ) @ sk_B ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','19'])).

thf('21',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
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
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ ( k1_tarski @ X48 ) @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ X48 ) @ X46 ) ) )
      | ( ( k2_relset_1 @ ( k1_tarski @ X48 ) @ X46 @ X47 )
        = ( k1_tarski @ ( k1_funct_1 @ X47 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[t62_funct_2])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ X0 ) ) )
      | ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ X0 @ X1 )
        = ( k1_tarski @ ( k1_funct_1 @ X1 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( k1_tarski @ sk_A ) @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','15','18'])).

thf('25',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','15','18'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ X0 ) ) )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ X0 @ X1 )
        = ( k1_tarski @ ( k1_funct_1 @ X1 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X1 @ ( k1_relat_1 @ sk_D_1 ) @ X0 )
      | ~ ( v1_funct_1 @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_funct_2 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_2 @ sk_D_1 @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','15','18'])).

thf('31',plain,(
    v1_funct_2 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('34',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','15','18'])).

thf('36',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_D_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28','31','36'])).

thf('38',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_D_1 )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf(t5_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_relat_1 @ C ) )
     => ( ( ! [D: $i] :
              ( ( r2_hidden @ D @ A )
             => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
          & ( ( k1_relat_1 @ C )
            = A ) )
       => ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
          & ( v1_funct_2 @ C @ A @ B )
          & ( v1_funct_1 @ C ) ) ) ) )).

thf(zf_stmt_6,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_hidden @ D @ A )
       => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
     => ( zip_tseitin_2 @ D @ C @ B @ A ) ) )).

thf('40',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( zip_tseitin_2 @ X36 @ X37 @ X38 @ X39 )
      | ( r2_hidden @ X36 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf(zf_stmt_7,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ C @ B @ A )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( zip_tseitin_2 @ D @ C @ B @ A ) )
       => ( zip_tseitin_3 @ C @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( ( k1_relat_1 @ X44 )
       != X43 )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X44 @ X45 @ X43 ) @ X44 @ X45 @ X43 )
      | ( zip_tseitin_3 @ X44 @ X45 @ X43 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('42',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ~ ( v1_funct_1 @ X44 )
      | ( zip_tseitin_3 @ X44 @ X45 @ ( k1_relat_1 @ X44 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X44 @ X45 @ ( k1_relat_1 @ X44 ) ) @ X44 @ X45 @ ( k1_relat_1 @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ( zip_tseitin_3 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','19'])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('45',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X49 @ X50 )
      | ( X51 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X52 @ X49 ) @ ( k2_relset_1 @ X50 @ X51 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k2_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 ) )
      | ~ ( v1_funct_2 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('48',plain,(
    v1_funct_2 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B ),
    inference(demod,[status(thm)],['29','30'])).

thf('49',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k2_relat_1 @ sk_D_1 ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ X0 ) @ ( k2_relat_1 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['43','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('55',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('57',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('58',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['53','58','59'])).

thf('61',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( zip_tseitin_2 @ X36 @ X37 @ X38 @ X39 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X37 @ X36 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) @ sk_D_1 @ ( k2_relat_1 @ sk_D_1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ~ ( v1_funct_1 @ X44 )
      | ( zip_tseitin_3 @ X44 @ X45 @ ( k1_relat_1 @ X44 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X44 @ X45 @ ( k1_relat_1 @ X44 ) ) @ X44 @ X45 @ ( k1_relat_1 @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('64',plain,
    ( ( zip_tseitin_3 @ sk_D_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_relat_1 @ sk_D_1 ) )
    | ( zip_tseitin_3 @ sk_D_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_relat_1 @ sk_D_1 ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['56','57'])).

thf('67',plain,
    ( ( zip_tseitin_3 @ sk_D_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_relat_1 @ sk_D_1 ) )
    | ( zip_tseitin_3 @ sk_D_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    zip_tseitin_3 @ sk_D_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ~ ( zip_tseitin_3 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('70',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(t44_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r1_tarski @ ( k7_relset_1 @ A @ B @ D @ C ) @ B ) ) )).

thf('71',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k7_relset_1 @ X30 @ X31 @ X32 @ X33 ) @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t44_funct_2])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ ( k2_relat_1 @ sk_D_1 ) )
      | ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ ( k2_relat_1 @ sk_D_1 ) @ sk_D_1 @ X0 ) @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    zip_tseitin_3 @ sk_D_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['67'])).

thf('75',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( v1_funct_2 @ X40 @ X42 @ X41 )
      | ~ ( zip_tseitin_3 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('76',plain,(
    v1_funct_2 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ ( k2_relat_1 @ sk_D_1 ) @ sk_D_1 @ X0 ) @ ( k2_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['72','73','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('79',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k7_relset_1 @ X19 @ X20 @ X18 @ X21 )
        = ( k9_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ ( k2_relat_1 @ sk_D_1 ) @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ X0 ) @ ( k2_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['77','80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['4','39','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w7rtejlx68
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:09:01 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.77/0.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/0.98  % Solved by: fo/fo7.sh
% 0.77/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.98  % done 289 iterations in 0.522s
% 0.77/0.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/0.98  % SZS output start Refutation
% 0.77/0.98  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.77/0.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.77/0.98  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.77/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.98  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.77/0.98  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.77/0.98  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.77/0.98  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.77/0.98  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 0.77/0.98  thf(sk_C_type, type, sk_C: $i).
% 0.77/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.98  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 0.77/0.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/0.98  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.77/0.98  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.77/0.98  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.77/0.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.77/0.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.77/0.98  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.77/0.98  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.77/0.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.77/0.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.77/0.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/0.98  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.77/0.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.77/0.98  thf(t64_funct_2, conjecture,
% 0.77/0.98    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.98     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.77/0.98         ( m1_subset_1 @
% 0.77/0.98           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.77/0.98       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.77/0.98         ( r1_tarski @
% 0.77/0.98           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.77/0.98           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.77/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.98    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.98        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.77/0.98            ( m1_subset_1 @
% 0.77/0.98              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.77/0.98          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.77/0.98            ( r1_tarski @
% 0.77/0.98              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.77/0.98              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.77/0.98    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.77/0.98  thf('0', plain,
% 0.77/0.98      (~ (r1_tarski @ 
% 0.77/0.98          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.77/0.98          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('1', plain,
% 0.77/0.98      ((m1_subset_1 @ sk_D_1 @ 
% 0.77/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf(redefinition_k7_relset_1, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.98       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.77/0.98  thf('2', plain,
% 0.77/0.98      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.77/0.98         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.77/0.98          | ((k7_relset_1 @ X19 @ X20 @ X18 @ X21) = (k9_relat_1 @ X18 @ X21)))),
% 0.77/0.98      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.77/0.98  thf('3', plain,
% 0.77/0.98      (![X0 : $i]:
% 0.77/0.98         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ X0)
% 0.77/0.98           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.77/0.98      inference('sup-', [status(thm)], ['1', '2'])).
% 0.77/0.98  thf('4', plain,
% 0.77/0.98      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 0.77/0.98          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.77/0.98      inference('demod', [status(thm)], ['0', '3'])).
% 0.77/0.98  thf('5', plain,
% 0.77/0.98      ((m1_subset_1 @ sk_D_1 @ 
% 0.77/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('6', plain, ((v1_funct_2 @ sk_D_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf(d1_funct_2, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i]:
% 0.77/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.98       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.77/0.98           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.77/0.98             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.77/0.98         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.77/0.98           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.77/0.98             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.77/0.98  thf(zf_stmt_1, axiom,
% 0.77/0.98    (![C:$i,B:$i,A:$i]:
% 0.77/0.98     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.77/0.98       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.77/0.98  thf('7', plain,
% 0.77/0.98      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.77/0.98         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.77/0.98          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 0.77/0.98          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.77/0.98  thf('8', plain,
% 0.77/0.98      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.77/0.98        | ((k1_tarski @ sk_A)
% 0.77/0.98            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1)))),
% 0.77/0.98      inference('sup-', [status(thm)], ['6', '7'])).
% 0.77/0.98  thf(zf_stmt_2, axiom,
% 0.77/0.98    (![B:$i,A:$i]:
% 0.77/0.98     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.77/0.98       ( zip_tseitin_0 @ B @ A ) ))).
% 0.77/0.98  thf('9', plain,
% 0.77/0.98      (![X22 : $i, X23 : $i]:
% 0.77/0.98         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.77/0.98  thf('10', plain,
% 0.77/0.98      ((m1_subset_1 @ sk_D_1 @ 
% 0.77/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.77/0.98  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.77/0.98  thf(zf_stmt_5, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i]:
% 0.77/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.98       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.77/0.98         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.77/0.98           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.77/0.98             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.77/0.98  thf('11', plain,
% 0.77/0.98      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.77/0.98         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.77/0.98          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.77/0.98          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.77/0.98  thf('12', plain,
% 0.77/0.98      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.77/0.98        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.77/0.98      inference('sup-', [status(thm)], ['10', '11'])).
% 0.77/0.98  thf('13', plain,
% 0.77/0.98      ((((sk_B) = (k1_xboole_0))
% 0.77/0.98        | (zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.77/0.98      inference('sup-', [status(thm)], ['9', '12'])).
% 0.77/0.98  thf('14', plain, (((sk_B) != (k1_xboole_0))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('15', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))),
% 0.77/0.98      inference('simplify_reflect-', [status(thm)], ['13', '14'])).
% 0.77/0.98  thf('16', plain,
% 0.77/0.98      ((m1_subset_1 @ sk_D_1 @ 
% 0.77/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf(redefinition_k1_relset_1, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i]:
% 0.77/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.98       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.77/0.98  thf('17', plain,
% 0.77/0.98      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.77/0.98         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 0.77/0.98          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.77/0.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.77/0.98  thf('18', plain,
% 0.77/0.98      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1)
% 0.77/0.98         = (k1_relat_1 @ sk_D_1))),
% 0.77/0.98      inference('sup-', [status(thm)], ['16', '17'])).
% 0.77/0.98  thf('19', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.77/0.98      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.77/0.98  thf('20', plain,
% 0.77/0.98      ((m1_subset_1 @ sk_D_1 @ 
% 0.77/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ sk_B)))),
% 0.77/0.98      inference('demod', [status(thm)], ['5', '19'])).
% 0.77/0.98  thf('21', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.77/0.98      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.77/0.98  thf(t62_funct_2, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i]:
% 0.77/0.98     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.77/0.98         ( m1_subset_1 @
% 0.77/0.98           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.77/0.98       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.77/0.98         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.77/0.98           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.77/0.98  thf('22', plain,
% 0.77/0.98      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.77/0.98         (((X46) = (k1_xboole_0))
% 0.77/0.98          | ~ (v1_funct_1 @ X47)
% 0.77/0.98          | ~ (v1_funct_2 @ X47 @ (k1_tarski @ X48) @ X46)
% 0.77/0.98          | ~ (m1_subset_1 @ X47 @ 
% 0.77/0.98               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ X48) @ X46)))
% 0.77/0.98          | ((k2_relset_1 @ (k1_tarski @ X48) @ X46 @ X47)
% 0.77/0.98              = (k1_tarski @ (k1_funct_1 @ X47 @ X48))))),
% 0.77/0.98      inference('cnf', [status(esa)], [t62_funct_2])).
% 0.77/0.98  thf('23', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i]:
% 0.77/0.98         (~ (m1_subset_1 @ X1 @ 
% 0.77/0.98             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ X0)))
% 0.77/0.98          | ((k2_relset_1 @ (k1_tarski @ sk_A) @ X0 @ X1)
% 0.77/0.98              = (k1_tarski @ (k1_funct_1 @ X1 @ sk_A)))
% 0.77/0.98          | ~ (v1_funct_2 @ X1 @ (k1_tarski @ sk_A) @ X0)
% 0.77/0.98          | ~ (v1_funct_1 @ X1)
% 0.77/0.98          | ((X0) = (k1_xboole_0)))),
% 0.77/0.98      inference('sup-', [status(thm)], ['21', '22'])).
% 0.77/0.98  thf('24', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.77/0.98      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.77/0.98  thf('25', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.77/0.98      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.77/0.98  thf('26', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i]:
% 0.77/0.98         (~ (m1_subset_1 @ X1 @ 
% 0.77/0.98             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ X0)))
% 0.77/0.98          | ((k2_relset_1 @ (k1_relat_1 @ sk_D_1) @ X0 @ X1)
% 0.77/0.98              = (k1_tarski @ (k1_funct_1 @ X1 @ sk_A)))
% 0.77/0.98          | ~ (v1_funct_2 @ X1 @ (k1_relat_1 @ sk_D_1) @ X0)
% 0.77/0.98          | ~ (v1_funct_1 @ X1)
% 0.77/0.98          | ((X0) = (k1_xboole_0)))),
% 0.77/0.98      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.77/0.98  thf('27', plain,
% 0.77/0.98      ((((sk_B) = (k1_xboole_0))
% 0.77/0.98        | ~ (v1_funct_1 @ sk_D_1)
% 0.77/0.98        | ~ (v1_funct_2 @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_B)
% 0.77/0.98        | ((k2_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1)
% 0.77/0.98            = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A))))),
% 0.77/0.98      inference('sup-', [status(thm)], ['20', '26'])).
% 0.77/0.98  thf('28', plain, ((v1_funct_1 @ sk_D_1)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('29', plain, ((v1_funct_2 @ sk_D_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('30', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.77/0.98      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.77/0.98  thf('31', plain, ((v1_funct_2 @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_B)),
% 0.77/0.98      inference('demod', [status(thm)], ['29', '30'])).
% 0.77/0.98  thf('32', plain,
% 0.77/0.98      ((m1_subset_1 @ sk_D_1 @ 
% 0.77/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf(redefinition_k2_relset_1, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i]:
% 0.77/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.77/0.98       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.77/0.98  thf('33', plain,
% 0.77/0.98      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.77/0.98         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.77/0.98          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.77/0.98      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.77/0.98  thf('34', plain,
% 0.77/0.98      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1)
% 0.77/0.98         = (k2_relat_1 @ sk_D_1))),
% 0.77/0.98      inference('sup-', [status(thm)], ['32', '33'])).
% 0.77/0.98  thf('35', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.77/0.98      inference('demod', [status(thm)], ['8', '15', '18'])).
% 0.77/0.98  thf('36', plain,
% 0.77/0.98      (((k2_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1)
% 0.77/0.98         = (k2_relat_1 @ sk_D_1))),
% 0.77/0.98      inference('demod', [status(thm)], ['34', '35'])).
% 0.77/0.98  thf('37', plain,
% 0.77/0.98      ((((sk_B) = (k1_xboole_0))
% 0.77/0.98        | ((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A))))),
% 0.77/0.98      inference('demod', [status(thm)], ['27', '28', '31', '36'])).
% 0.77/0.98  thf('38', plain, (((sk_B) != (k1_xboole_0))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('39', plain,
% 0.77/0.98      (((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.77/0.98      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.77/0.98  thf(t5_funct_2, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i]:
% 0.77/0.98     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.77/0.98       ( ( ( ![D:$i]:
% 0.77/0.98             ( ( r2_hidden @ D @ A ) =>
% 0.77/0.98               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 0.77/0.98           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.77/0.98         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.77/0.98           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 0.77/0.98  thf(zf_stmt_6, axiom,
% 0.77/0.98    (![D:$i,C:$i,B:$i,A:$i]:
% 0.77/0.98     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 0.77/0.98       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 0.77/0.98  thf('40', plain,
% 0.77/0.98      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.77/0.98         ((zip_tseitin_2 @ X36 @ X37 @ X38 @ X39) | (r2_hidden @ X36 @ X39))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.77/0.98  thf(zf_stmt_7, type, zip_tseitin_3 : $i > $i > $i > $o).
% 0.77/0.98  thf(zf_stmt_8, axiom,
% 0.77/0.98    (![C:$i,B:$i,A:$i]:
% 0.77/0.98     ( ( zip_tseitin_3 @ C @ B @ A ) =>
% 0.77/0.98       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.77/0.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.77/0.98  thf(zf_stmt_9, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 0.77/0.98  thf(zf_stmt_10, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i]:
% 0.77/0.98     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.77/0.98       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.77/0.98           ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) =>
% 0.77/0.98         ( zip_tseitin_3 @ C @ B @ A ) ) ))).
% 0.77/0.98  thf('41', plain,
% 0.77/0.98      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.77/0.98         (((k1_relat_1 @ X44) != (X43))
% 0.77/0.98          | ~ (zip_tseitin_2 @ (sk_D @ X44 @ X45 @ X43) @ X44 @ X45 @ X43)
% 0.77/0.98          | (zip_tseitin_3 @ X44 @ X45 @ X43)
% 0.77/0.98          | ~ (v1_funct_1 @ X44)
% 0.77/0.98          | ~ (v1_relat_1 @ X44))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_10])).
% 0.77/0.98  thf('42', plain,
% 0.77/0.98      (![X44 : $i, X45 : $i]:
% 0.77/0.98         (~ (v1_relat_1 @ X44)
% 0.77/0.98          | ~ (v1_funct_1 @ X44)
% 0.77/0.98          | (zip_tseitin_3 @ X44 @ X45 @ (k1_relat_1 @ X44))
% 0.77/0.98          | ~ (zip_tseitin_2 @ (sk_D @ X44 @ X45 @ (k1_relat_1 @ X44)) @ X44 @ 
% 0.77/0.98               X45 @ (k1_relat_1 @ X44)))),
% 0.77/0.98      inference('simplify', [status(thm)], ['41'])).
% 0.77/0.98  thf('43', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i]:
% 0.77/0.98         ((r2_hidden @ (sk_D @ X0 @ X1 @ (k1_relat_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.77/0.98          | (zip_tseitin_3 @ X0 @ X1 @ (k1_relat_1 @ X0))
% 0.77/0.98          | ~ (v1_funct_1 @ X0)
% 0.77/0.98          | ~ (v1_relat_1 @ X0))),
% 0.77/0.98      inference('sup-', [status(thm)], ['40', '42'])).
% 0.77/0.98  thf('44', plain,
% 0.77/0.98      ((m1_subset_1 @ sk_D_1 @ 
% 0.77/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ sk_B)))),
% 0.77/0.98      inference('demod', [status(thm)], ['5', '19'])).
% 0.77/0.98  thf(t6_funct_2, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.98     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.77/0.98         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.77/0.98       ( ( r2_hidden @ C @ A ) =>
% 0.77/0.98         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.77/0.98           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.77/0.98  thf('45', plain,
% 0.77/0.98      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 0.77/0.98         (~ (r2_hidden @ X49 @ X50)
% 0.77/0.98          | ((X51) = (k1_xboole_0))
% 0.77/0.98          | ~ (v1_funct_1 @ X52)
% 0.77/0.98          | ~ (v1_funct_2 @ X52 @ X50 @ X51)
% 0.77/0.98          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 0.77/0.98          | (r2_hidden @ (k1_funct_1 @ X52 @ X49) @ 
% 0.77/0.98             (k2_relset_1 @ X50 @ X51 @ X52)))),
% 0.77/0.98      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.77/0.98  thf('46', plain,
% 0.77/0.98      (![X0 : $i]:
% 0.77/0.98         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ 
% 0.77/0.98           (k2_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1))
% 0.77/0.98          | ~ (v1_funct_2 @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_B)
% 0.77/0.98          | ~ (v1_funct_1 @ sk_D_1)
% 0.77/0.98          | ((sk_B) = (k1_xboole_0))
% 0.77/0.98          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.77/0.98      inference('sup-', [status(thm)], ['44', '45'])).
% 0.77/0.98  thf('47', plain,
% 0.77/0.98      (((k2_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1)
% 0.77/0.98         = (k2_relat_1 @ sk_D_1))),
% 0.77/0.98      inference('demod', [status(thm)], ['34', '35'])).
% 0.77/0.98  thf('48', plain, ((v1_funct_2 @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_B)),
% 0.77/0.98      inference('demod', [status(thm)], ['29', '30'])).
% 0.77/0.98  thf('49', plain, ((v1_funct_1 @ sk_D_1)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('50', plain,
% 0.77/0.98      (![X0 : $i]:
% 0.77/0.98         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k2_relat_1 @ sk_D_1))
% 0.77/0.98          | ((sk_B) = (k1_xboole_0))
% 0.77/0.98          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.77/0.98      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 0.77/0.98  thf('51', plain, (((sk_B) != (k1_xboole_0))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('52', plain,
% 0.77/0.98      (![X0 : $i]:
% 0.77/0.98         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ X0) @ (k2_relat_1 @ sk_D_1))
% 0.77/0.98          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.77/0.98      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 0.77/0.98  thf('53', plain,
% 0.77/0.98      (![X0 : $i]:
% 0.77/0.98         (~ (v1_relat_1 @ sk_D_1)
% 0.77/0.98          | ~ (v1_funct_1 @ sk_D_1)
% 0.77/0.98          | (zip_tseitin_3 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.77/0.98          | (r2_hidden @ 
% 0.77/0.98             (k1_funct_1 @ sk_D_1 @ 
% 0.77/0.98              (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))) @ 
% 0.77/0.98             (k2_relat_1 @ sk_D_1)))),
% 0.77/0.98      inference('sup-', [status(thm)], ['43', '52'])).
% 0.77/0.98  thf('54', plain,
% 0.77/0.98      ((m1_subset_1 @ sk_D_1 @ 
% 0.77/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf(cc2_relat_1, axiom,
% 0.77/0.98    (![A:$i]:
% 0.77/0.98     ( ( v1_relat_1 @ A ) =>
% 0.77/0.98       ( ![B:$i]:
% 0.77/0.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.77/0.98  thf('55', plain,
% 0.77/0.98      (![X3 : $i, X4 : $i]:
% 0.77/0.98         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.77/0.98          | (v1_relat_1 @ X3)
% 0.77/0.98          | ~ (v1_relat_1 @ X4))),
% 0.77/0.98      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.77/0.98  thf('56', plain,
% 0.77/0.98      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.77/0.98        | (v1_relat_1 @ sk_D_1))),
% 0.77/0.98      inference('sup-', [status(thm)], ['54', '55'])).
% 0.77/0.98  thf(fc6_relat_1, axiom,
% 0.77/0.98    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.77/0.98  thf('57', plain,
% 0.77/0.98      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.77/0.98      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.77/0.98  thf('58', plain, ((v1_relat_1 @ sk_D_1)),
% 0.77/0.98      inference('demod', [status(thm)], ['56', '57'])).
% 0.77/0.98  thf('59', plain, ((v1_funct_1 @ sk_D_1)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('60', plain,
% 0.77/0.98      (![X0 : $i]:
% 0.77/0.98         ((zip_tseitin_3 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.77/0.98          | (r2_hidden @ 
% 0.77/0.98             (k1_funct_1 @ sk_D_1 @ 
% 0.77/0.98              (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))) @ 
% 0.77/0.98             (k2_relat_1 @ sk_D_1)))),
% 0.77/0.98      inference('demod', [status(thm)], ['53', '58', '59'])).
% 0.77/0.98  thf('61', plain,
% 0.77/0.98      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.77/0.98         ((zip_tseitin_2 @ X36 @ X37 @ X38 @ X39)
% 0.77/0.98          | ~ (r2_hidden @ (k1_funct_1 @ X37 @ X36) @ X38))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.77/0.98  thf('62', plain,
% 0.77/0.98      (![X0 : $i, X1 : $i]:
% 0.77/0.98         ((zip_tseitin_3 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.77/0.98          | (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1)) @ 
% 0.77/0.98             sk_D_1 @ (k2_relat_1 @ sk_D_1) @ X1))),
% 0.77/0.98      inference('sup-', [status(thm)], ['60', '61'])).
% 0.77/0.98  thf('63', plain,
% 0.77/0.98      (![X44 : $i, X45 : $i]:
% 0.77/0.98         (~ (v1_relat_1 @ X44)
% 0.77/0.98          | ~ (v1_funct_1 @ X44)
% 0.77/0.98          | (zip_tseitin_3 @ X44 @ X45 @ (k1_relat_1 @ X44))
% 0.77/0.98          | ~ (zip_tseitin_2 @ (sk_D @ X44 @ X45 @ (k1_relat_1 @ X44)) @ X44 @ 
% 0.77/0.98               X45 @ (k1_relat_1 @ X44)))),
% 0.77/0.98      inference('simplify', [status(thm)], ['41'])).
% 0.77/0.98  thf('64', plain,
% 0.77/0.98      (((zip_tseitin_3 @ sk_D_1 @ (k2_relat_1 @ sk_D_1) @ (k1_relat_1 @ sk_D_1))
% 0.77/0.98        | (zip_tseitin_3 @ sk_D_1 @ (k2_relat_1 @ sk_D_1) @ 
% 0.77/0.98           (k1_relat_1 @ sk_D_1))
% 0.77/0.98        | ~ (v1_funct_1 @ sk_D_1)
% 0.77/0.98        | ~ (v1_relat_1 @ sk_D_1))),
% 0.77/0.98      inference('sup-', [status(thm)], ['62', '63'])).
% 0.77/0.98  thf('65', plain, ((v1_funct_1 @ sk_D_1)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('66', plain, ((v1_relat_1 @ sk_D_1)),
% 0.77/0.98      inference('demod', [status(thm)], ['56', '57'])).
% 0.77/0.98  thf('67', plain,
% 0.77/0.98      (((zip_tseitin_3 @ sk_D_1 @ (k2_relat_1 @ sk_D_1) @ (k1_relat_1 @ sk_D_1))
% 0.77/0.98        | (zip_tseitin_3 @ sk_D_1 @ (k2_relat_1 @ sk_D_1) @ 
% 0.77/0.98           (k1_relat_1 @ sk_D_1)))),
% 0.77/0.98      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.77/0.98  thf('68', plain,
% 0.77/0.98      ((zip_tseitin_3 @ sk_D_1 @ (k2_relat_1 @ sk_D_1) @ (k1_relat_1 @ sk_D_1))),
% 0.77/0.98      inference('simplify', [status(thm)], ['67'])).
% 0.77/0.98  thf('69', plain,
% 0.77/0.98      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.77/0.98         ((m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 0.77/0.98          | ~ (zip_tseitin_3 @ X40 @ X41 @ X42))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.77/0.98  thf('70', plain,
% 0.77/0.98      ((m1_subset_1 @ sk_D_1 @ 
% 0.77/0.98        (k1_zfmisc_1 @ 
% 0.77/0.98         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ (k2_relat_1 @ sk_D_1))))),
% 0.77/0.98      inference('sup-', [status(thm)], ['68', '69'])).
% 0.77/0.98  thf(t44_funct_2, axiom,
% 0.77/0.98    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.98     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.77/0.98         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.77/0.98       ( r1_tarski @ ( k7_relset_1 @ A @ B @ D @ C ) @ B ) ))).
% 0.77/0.98  thf('71', plain,
% 0.77/0.98      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.77/0.98         ((r1_tarski @ (k7_relset_1 @ X30 @ X31 @ X32 @ X33) @ X31)
% 0.77/0.98          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.77/0.98          | ~ (v1_funct_2 @ X32 @ X30 @ X31)
% 0.77/0.98          | ~ (v1_funct_1 @ X32))),
% 0.77/0.98      inference('cnf', [status(esa)], [t44_funct_2])).
% 0.77/0.98  thf('72', plain,
% 0.77/0.98      (![X0 : $i]:
% 0.77/0.98         (~ (v1_funct_1 @ sk_D_1)
% 0.77/0.98          | ~ (v1_funct_2 @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ 
% 0.77/0.98               (k2_relat_1 @ sk_D_1))
% 0.77/0.98          | (r1_tarski @ 
% 0.77/0.98             (k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ (k2_relat_1 @ sk_D_1) @ 
% 0.77/0.98              sk_D_1 @ X0) @ 
% 0.77/0.98             (k2_relat_1 @ sk_D_1)))),
% 0.77/0.98      inference('sup-', [status(thm)], ['70', '71'])).
% 0.77/0.98  thf('73', plain, ((v1_funct_1 @ sk_D_1)),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.98  thf('74', plain,
% 0.77/0.98      ((zip_tseitin_3 @ sk_D_1 @ (k2_relat_1 @ sk_D_1) @ (k1_relat_1 @ sk_D_1))),
% 0.77/0.98      inference('simplify', [status(thm)], ['67'])).
% 0.77/0.98  thf('75', plain,
% 0.77/0.98      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.77/0.98         ((v1_funct_2 @ X40 @ X42 @ X41) | ~ (zip_tseitin_3 @ X40 @ X41 @ X42))),
% 0.77/0.98      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.77/0.98  thf('76', plain,
% 0.77/0.98      ((v1_funct_2 @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ (k2_relat_1 @ sk_D_1))),
% 0.77/0.98      inference('sup-', [status(thm)], ['74', '75'])).
% 0.77/0.98  thf('77', plain,
% 0.77/0.98      (![X0 : $i]:
% 0.77/0.98         (r1_tarski @ 
% 0.77/0.98          (k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ (k2_relat_1 @ sk_D_1) @ 
% 0.77/0.98           sk_D_1 @ X0) @ 
% 0.77/0.98          (k2_relat_1 @ sk_D_1))),
% 0.77/0.98      inference('demod', [status(thm)], ['72', '73', '76'])).
% 0.77/0.98  thf('78', plain,
% 0.77/0.98      ((m1_subset_1 @ sk_D_1 @ 
% 0.77/0.98        (k1_zfmisc_1 @ 
% 0.77/0.98         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ (k2_relat_1 @ sk_D_1))))),
% 0.77/0.98      inference('sup-', [status(thm)], ['68', '69'])).
% 0.77/0.98  thf('79', plain,
% 0.77/0.98      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.77/0.98         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.77/0.98          | ((k7_relset_1 @ X19 @ X20 @ X18 @ X21) = (k9_relat_1 @ X18 @ X21)))),
% 0.77/0.98      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.77/0.98  thf('80', plain,
% 0.77/0.98      (![X0 : $i]:
% 0.77/0.98         ((k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ (k2_relat_1 @ sk_D_1) @ 
% 0.77/0.98           sk_D_1 @ X0) = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.77/0.98      inference('sup-', [status(thm)], ['78', '79'])).
% 0.77/0.98  thf('81', plain,
% 0.77/0.98      (![X0 : $i]:
% 0.77/0.98         (r1_tarski @ (k9_relat_1 @ sk_D_1 @ X0) @ (k2_relat_1 @ sk_D_1))),
% 0.77/0.98      inference('demod', [status(thm)], ['77', '80'])).
% 0.77/0.98  thf('82', plain, ($false),
% 0.77/0.98      inference('demod', [status(thm)], ['4', '39', '81'])).
% 0.77/0.98  
% 0.77/0.98  % SZS output end Refutation
% 0.77/0.98  
% 0.77/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
