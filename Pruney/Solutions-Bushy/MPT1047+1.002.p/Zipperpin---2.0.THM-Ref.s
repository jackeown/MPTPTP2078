%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1047+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fvoCXj1e2W

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:57 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 280 expanded)
%              Number of leaves         :   33 (  92 expanded)
%              Depth                    :   20
%              Number of atoms          : 1606 (5475 expanded)
%              Number of equality atoms :   72 ( 226 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X10: $i] :
      ( ( X10
        = ( k1_tarski @ X6 ) )
      | ( ( sk_C @ X10 @ X6 )
        = X6 )
      | ( r2_hidden @ ( sk_C @ X10 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf(t164_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
         => ( ( k5_partfun1 @ A @ ( k1_tarski @ B ) @ C )
            = ( k1_tarski @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
           => ( ( k5_partfun1 @ A @ ( k1_tarski @ B ) @ C )
              = ( k1_tarski @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t158_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( r2_hidden @ D @ ( k5_partfun1 @ A @ B @ C ) )
         => ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X37 @ ( k5_partfun1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_1 @ X37 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t158_funct_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C_1 )
      | ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( v1_funct_1 @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X6: $i,X10: $i] :
      ( ( X10
        = ( k1_tarski @ X6 ) )
      | ( ( sk_C @ X10 @ X6 )
        = X6 )
      | ( r2_hidden @ ( sk_C @ X10 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X37 @ ( k5_partfun1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t158_funct_2])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C_1 )
      | ( v1_funct_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( v1_funct_2 @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 ) @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X6: $i,X10: $i] :
      ( ( X10
        = ( k1_tarski @ X6 ) )
      | ( ( sk_C @ X10 @ X6 )
        = X6 )
      | ( r2_hidden @ ( sk_C @ X10 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X37 @ ( k5_partfun1 @ X38 @ X39 @ X40 ) )
      | ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t158_funct_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_C_1 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ~ ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( m1_subset_1 @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t66_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ ( k1_tarski @ B ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ ( k1_tarski @ B ) )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
         => ( r2_relset_1 @ A @ ( k1_tarski @ B ) @ C @ D ) ) ) )).

thf('22',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ ( k1_tarski @ X47 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ ( k1_tarski @ X47 ) ) ) )
      | ( r2_relset_1 @ X46 @ ( k1_tarski @ X47 ) @ X48 @ X45 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ ( k1_tarski @ X47 ) ) ) )
      | ~ ( v1_funct_2 @ X48 @ X46 @ ( k1_tarski @ X47 ) )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t66_funct_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ X0 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 ) @ sk_D )
      | ~ ( v1_funct_2 @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 ) @ sk_A @ ( k1_tarski @ sk_B ) )
      | ~ ( v1_funct_1 @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ~ ( v1_funct_1 @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 ) )
      | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 ) @ sk_D )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 ) @ sk_D )
      | ~ ( v1_funct_1 @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 ) )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 ) @ sk_D )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( m1_subset_1 @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('33',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( X27 = X30 )
      | ~ ( r2_relset_1 @ X28 @ X29 @ X27 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ~ ( r2_relset_1 @ sk_A @ ( k1_tarski @ sk_B ) @ ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 ) @ X1 )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 )
        = sk_D )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 )
        = sk_D )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 )
        = sk_D )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 )
        = X0 )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_D )
      | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ X0 )
        = sk_D ) ) ),
    inference(eq_fact,[status(thm)],['38'])).

thf('40',plain,
    ( ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ sk_D )
      = sk_D )
    | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
      = ( k1_tarski @ sk_D ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ sk_D )
    = sk_D ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X6: $i,X10: $i] :
      ( ( X10
        = ( k1_tarski @ X6 ) )
      | ( ( sk_C @ X10 @ X6 )
       != X6 )
      | ~ ( r2_hidden @ ( sk_C @ X10 @ X6 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
    | ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ sk_D )
     != sk_D )
    | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
      = ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t143_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k1_tarski @ B ) ) ) ) )
         => ( r1_partfun1 @ C @ D ) ) ) )).

thf('47',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ ( k1_tarski @ X35 ) ) ) )
      | ( r1_partfun1 @ X36 @ X33 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ ( k1_tarski @ X35 ) ) ) )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t143_partfun1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r1_partfun1 @ X0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
      | ( r1_partfun1 @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r1_partfun1 @ sk_D @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    r1_partfun1 @ sk_D @ sk_C_1 ),
    inference(demod,[status(thm)],['51','52'])).

thf(symmetry_r1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_partfun1 @ A @ B )
       => ( r1_partfun1 @ B @ A ) ) ) )).

thf('54',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 )
      | ~ ( v1_relat_1 @ X32 )
      | ~ ( v1_funct_1 @ X32 )
      | ( r1_partfun1 @ X32 @ X31 )
      | ~ ( r1_partfun1 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_partfun1])).

thf('55',plain,
    ( ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('59',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('62',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference(demod,[status(thm)],['55','56','59','62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ C ) )
     => ! [D: $i] :
          ( ( D
            = ( k5_partfun1 @ A @ B @ C ) )
        <=> ! [E: $i] :
              ( ( r2_hidden @ E @ D )
            <=> ? [F: $i] :
                  ( ( v1_funct_1 @ F )
                  & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
                  & ( F = E )
                  & ( v1_partfun1 @ F @ A )
                  & ( r1_partfun1 @ C @ F ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ C @ B @ A )
    <=> ( ( r1_partfun1 @ C @ F )
        & ( v1_partfun1 @ F @ A )
        & ( F = E )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F ) ) ) )).

thf('66',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 @ X11 @ X14 @ X16 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X14 ) ) )
      | ( X12 != X13 )
      | ~ ( v1_partfun1 @ X12 @ X16 )
      | ~ ( r1_partfun1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('67',plain,(
    ! [X11: $i,X13: $i,X14: $i,X16: $i] :
      ( ~ ( r1_partfun1 @ X11 @ X13 )
      | ~ ( v1_partfun1 @ X13 @ X16 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ( zip_tseitin_0 @ X13 @ X13 @ X11 @ X14 @ X16 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
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

thf('71',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ( v1_partfun1 @ X3 @ X4 )
      | ~ ( v1_funct_2 @ X3 @ X4 @ X5 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('76',plain,(
    ! [X26: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('77',plain,(
    v1_partfun1 @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_D @ sk_D @ X0 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['68','69','77'])).

thf('79',plain,(
    zip_tseitin_0 @ sk_D @ sk_D @ sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['64','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( D
            = ( k5_partfun1 @ A @ B @ C ) )
        <=> ! [E: $i] :
              ( ( r2_hidden @ E @ D )
            <=> ? [F: $i] :
                  ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) )).

thf('81',plain,(
    ! [X18: $i,X19: $i,X20: $i,X22: $i,X24: $i,X25: $i] :
      ( ( X22
       != ( k5_partfun1 @ X20 @ X19 @ X18 ) )
      | ( r2_hidden @ X24 @ X22 )
      | ~ ( zip_tseitin_0 @ X25 @ X24 @ X18 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('82',plain,(
    ! [X18: $i,X19: $i,X20: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) )
      | ~ ( zip_tseitin_0 @ X25 @ X24 @ X18 @ X19 @ X20 )
      | ( r2_hidden @ X24 @ ( k5_partfun1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['80','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    r2_hidden @ sk_D @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['79','85'])).

thf('87',plain,
    ( ( sk_C @ ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 ) @ sk_D )
    = sk_D ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('88',plain,
    ( ( sk_D != sk_D )
    | ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
      = ( k1_tarski @ sk_D ) ) ),
    inference(demod,[status(thm)],['44','86','87'])).

thf('89',plain,
    ( ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
    = ( k1_tarski @ sk_D ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ( k5_partfun1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_C_1 )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['89','90'])).


%------------------------------------------------------------------------------
