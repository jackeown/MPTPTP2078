%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1VprGvq369

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:22 EST 2020

% Result     : Theorem 0.64s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 574 expanded)
%              Number of leaves         :   39 ( 191 expanded)
%              Depth                    :   14
%              Number of atoms          : 1631 (12014 expanded)
%              Number of equality atoms :   49 ( 101 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t88_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ ( k6_partfun1 @ A ) )
        & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ ( k6_partfun1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ ( k6_partfun1 @ A ) )
          & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ ( k6_partfun1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_funct_2])).

thf('0',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k2_funct_2 @ X31 @ X30 )
        = ( k2_funct_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) )
      | ~ ( v3_funct_2 @ X30 @ X31 @ X31 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','10'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ X4 @ ( k2_funct_1 @ X4 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) )
        & ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A )
        & ( m1_subset_1 @ ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) )
      | ~ ( v3_funct_2 @ X21 @ X20 @ X20 )
      | ~ ( v1_funct_2 @ X21 @ X20 @ X20 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('20',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('21',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('23',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) )
      | ~ ( v3_funct_2 @ X21 @ X20 @ X20 )
      | ~ ( v1_funct_2 @ X21 @ X20 @ X20 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('30',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('35',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('36',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['27','36'])).

thf('38',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('39',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('41',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,
    ( ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('46',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X33 @ X33 @ X34 )
        = X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X33 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('47',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('51',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X10 @ X8 )
        = ( k1_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('52',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['47','48','49','52'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('54',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('55',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('57',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( r2_relset_1 @ X12 @ X13 @ X11 @ X14 )
      | ( X11 != X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('58',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_relset_1 @ X12 @ X13 @ X14 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('63',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('64',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('67',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v3_funct_2 @ X15 @ X16 @ X17 )
      | ( v2_funct_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('68',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['44','53','59','64','65','71'])).

thf('73',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('74',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['11','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('78',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('83',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['76','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( v1_funct_1 @ X15 )
      | ~ ( v3_funct_2 @ X15 @ X16 @ X17 )
      | ( v2_funct_2 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('89',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['89','90','91'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('93',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v2_funct_2 @ X19 @ X18 )
      | ( ( k2_relat_1 @ X19 )
        = X18 )
      | ~ ( v5_relat_1 @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('94',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('97',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v5_relat_1 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('98',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['94','95','98'])).

thf('100',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X4 ) @ X4 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('101',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['99','102'])).

thf('104',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['94','95','98'])).

thf('105',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('106',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63'])).

thf('108',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('109',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('110',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( X11 = X14 )
      | ~ ( r2_relset_1 @ X12 @ X13 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ X1 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ( k6_relat_1 @ sk_A )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X4: $i] :
      ( ~ ( v2_funct_1 @ X4 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X4 ) @ X4 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('114',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('115',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_relset_1 @ X12 @ X13 @ X14 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('116',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['113','116'])).

thf('118',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['94','95','98'])).

thf('119',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['62','63'])).

thf('120',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('122',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['117','118','119','120','121'])).

thf('123',plain,
    ( ( k6_relat_1 @ sk_A )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['112','122'])).

thf('124',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['85','86','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('126',plain,(
    $false ),
    inference(demod,[status(thm)],['75','124','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1VprGvq369
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:46:20 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.64/0.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.64/0.93  % Solved by: fo/fo7.sh
% 0.64/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.64/0.93  % done 754 iterations in 0.477s
% 0.64/0.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.64/0.93  % SZS output start Refutation
% 0.64/0.93  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.64/0.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.64/0.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.64/0.93  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.64/0.93  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.64/0.93  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.64/0.93  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.64/0.93  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.64/0.93  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.64/0.93  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.64/0.93  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.64/0.93  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.64/0.93  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.64/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.64/0.93  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.64/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.64/0.93  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.64/0.93  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.64/0.93  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.64/0.93  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.64/0.93  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.64/0.93  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.64/0.93  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.64/0.93  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.64/0.93  thf(t88_funct_2, conjecture,
% 0.64/0.93    (![A:$i,B:$i]:
% 0.64/0.93     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.64/0.93         ( v3_funct_2 @ B @ A @ A ) & 
% 0.64/0.93         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.64/0.93       ( ( r2_relset_1 @
% 0.64/0.93           A @ A @ 
% 0.64/0.93           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.64/0.93           ( k6_partfun1 @ A ) ) & 
% 0.64/0.93         ( r2_relset_1 @
% 0.64/0.93           A @ A @ 
% 0.64/0.93           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.64/0.93           ( k6_partfun1 @ A ) ) ) ))).
% 0.64/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.64/0.93    (~( ![A:$i,B:$i]:
% 0.64/0.93        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.64/0.93            ( v3_funct_2 @ B @ A @ A ) & 
% 0.64/0.93            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.64/0.93          ( ( r2_relset_1 @
% 0.64/0.93              A @ A @ 
% 0.64/0.93              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.64/0.93              ( k6_partfun1 @ A ) ) & 
% 0.64/0.93            ( r2_relset_1 @
% 0.64/0.93              A @ A @ 
% 0.64/0.93              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.64/0.93              ( k6_partfun1 @ A ) ) ) ) )),
% 0.64/0.93    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.64/0.93  thf('0', plain,
% 0.64/0.93      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.93           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.64/0.93            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.64/0.93           (k6_partfun1 @ sk_A))
% 0.64/0.93        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.93             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.64/0.93              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.64/0.93             (k6_partfun1 @ sk_A)))),
% 0.64/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.93  thf('1', plain,
% 0.64/0.93      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.93           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.64/0.93            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.64/0.93           (k6_partfun1 @ sk_A)))
% 0.64/0.93         <= (~
% 0.64/0.93             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.93               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.64/0.93                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.64/0.93               (k6_partfun1 @ sk_A))))),
% 0.64/0.93      inference('split', [status(esa)], ['0'])).
% 0.64/0.93  thf(redefinition_k6_partfun1, axiom,
% 0.64/0.93    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.64/0.93  thf('2', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.64/0.93      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.64/0.93  thf('3', plain,
% 0.64/0.93      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.93           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.64/0.93            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.64/0.93           (k6_relat_1 @ sk_A)))
% 0.64/0.93         <= (~
% 0.64/0.93             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.93               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.64/0.93                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.64/0.93               (k6_partfun1 @ sk_A))))),
% 0.64/0.93      inference('demod', [status(thm)], ['1', '2'])).
% 0.64/0.93  thf('4', plain,
% 0.64/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.93  thf(redefinition_k2_funct_2, axiom,
% 0.64/0.93    (![A:$i,B:$i]:
% 0.64/0.93     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.64/0.93         ( v3_funct_2 @ B @ A @ A ) & 
% 0.64/0.93         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.64/0.93       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.64/0.93  thf('5', plain,
% 0.64/0.93      (![X30 : $i, X31 : $i]:
% 0.64/0.93         (((k2_funct_2 @ X31 @ X30) = (k2_funct_1 @ X30))
% 0.64/0.93          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))
% 0.64/0.93          | ~ (v3_funct_2 @ X30 @ X31 @ X31)
% 0.64/0.93          | ~ (v1_funct_2 @ X30 @ X31 @ X31)
% 0.64/0.93          | ~ (v1_funct_1 @ X30))),
% 0.64/0.93      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.64/0.93  thf('6', plain,
% 0.64/0.93      ((~ (v1_funct_1 @ sk_B)
% 0.64/0.93        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.64/0.93        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.64/0.93        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.64/0.93      inference('sup-', [status(thm)], ['4', '5'])).
% 0.64/0.93  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 0.64/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.93  thf('8', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.64/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.93  thf('9', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.64/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.93  thf('10', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.64/0.93      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.64/0.93  thf('11', plain,
% 0.64/0.93      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.93           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.64/0.93            sk_B) @ 
% 0.64/0.93           (k6_relat_1 @ sk_A)))
% 0.64/0.93         <= (~
% 0.64/0.93             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.93               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.64/0.93                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.64/0.93               (k6_partfun1 @ sk_A))))),
% 0.64/0.93      inference('demod', [status(thm)], ['3', '10'])).
% 0.64/0.93  thf(t61_funct_1, axiom,
% 0.64/0.93    (![A:$i]:
% 0.64/0.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.64/0.93       ( ( v2_funct_1 @ A ) =>
% 0.64/0.93         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.64/0.93             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.64/0.93           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.64/0.93             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.64/0.93  thf('12', plain,
% 0.64/0.93      (![X4 : $i]:
% 0.64/0.93         (~ (v2_funct_1 @ X4)
% 0.64/0.93          | ((k5_relat_1 @ X4 @ (k2_funct_1 @ X4))
% 0.64/0.93              = (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.64/0.93          | ~ (v1_funct_1 @ X4)
% 0.64/0.93          | ~ (v1_relat_1 @ X4))),
% 0.64/0.93      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.64/0.93  thf('13', plain,
% 0.64/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.93  thf(dt_k2_funct_2, axiom,
% 0.64/0.93    (![A:$i,B:$i]:
% 0.64/0.93     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.64/0.93         ( v3_funct_2 @ B @ A @ A ) & 
% 0.64/0.93         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.64/0.93       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.64/0.93         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.64/0.93         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.64/0.93         ( m1_subset_1 @
% 0.64/0.93           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.64/0.93  thf('14', plain,
% 0.64/0.93      (![X20 : $i, X21 : $i]:
% 0.64/0.93         ((m1_subset_1 @ (k2_funct_2 @ X20 @ X21) @ 
% 0.64/0.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))
% 0.64/0.93          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))
% 0.64/0.93          | ~ (v3_funct_2 @ X21 @ X20 @ X20)
% 0.64/0.93          | ~ (v1_funct_2 @ X21 @ X20 @ X20)
% 0.64/0.93          | ~ (v1_funct_1 @ X21))),
% 0.64/0.93      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.64/0.93  thf('15', plain,
% 0.64/0.93      ((~ (v1_funct_1 @ sk_B)
% 0.64/0.93        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.64/0.93        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.64/0.93        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.64/0.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.64/0.93      inference('sup-', [status(thm)], ['13', '14'])).
% 0.64/0.93  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 0.64/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.93  thf('17', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.64/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.93  thf('18', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.64/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.93  thf('19', plain,
% 0.64/0.93      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.64/0.93        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.93      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.64/0.93  thf('20', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.64/0.93      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.64/0.93  thf('21', plain,
% 0.64/0.93      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.64/0.93        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.93      inference('demod', [status(thm)], ['19', '20'])).
% 0.64/0.93  thf('22', plain,
% 0.64/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.93  thf(redefinition_k1_partfun1, axiom,
% 0.64/0.93    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.64/0.93     ( ( ( v1_funct_1 @ E ) & 
% 0.64/0.93         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.64/0.93         ( v1_funct_1 @ F ) & 
% 0.64/0.93         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.64/0.93       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.64/0.93  thf('23', plain,
% 0.64/0.93      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.64/0.93         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.64/0.93          | ~ (v1_funct_1 @ X24)
% 0.64/0.93          | ~ (v1_funct_1 @ X27)
% 0.64/0.93          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.64/0.93          | ((k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 0.64/0.93              = (k5_relat_1 @ X24 @ X27)))),
% 0.64/0.93      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.64/0.93  thf('24', plain,
% 0.64/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.93         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.64/0.93            = (k5_relat_1 @ sk_B @ X0))
% 0.64/0.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.64/0.93          | ~ (v1_funct_1 @ X0)
% 0.64/0.93          | ~ (v1_funct_1 @ sk_B))),
% 0.64/0.93      inference('sup-', [status(thm)], ['22', '23'])).
% 0.64/0.93  thf('25', plain, ((v1_funct_1 @ sk_B)),
% 0.64/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.93  thf('26', plain,
% 0.64/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.93         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.64/0.93            = (k5_relat_1 @ sk_B @ X0))
% 0.64/0.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.64/0.93          | ~ (v1_funct_1 @ X0))),
% 0.64/0.93      inference('demod', [status(thm)], ['24', '25'])).
% 0.64/0.93  thf('27', plain,
% 0.64/0.93      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.64/0.93        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.64/0.93            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 0.64/0.93      inference('sup-', [status(thm)], ['21', '26'])).
% 0.64/0.93  thf('28', plain,
% 0.64/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.93  thf('29', plain,
% 0.64/0.93      (![X20 : $i, X21 : $i]:
% 0.64/0.93         ((v1_funct_1 @ (k2_funct_2 @ X20 @ X21))
% 0.64/0.93          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))
% 0.64/0.93          | ~ (v3_funct_2 @ X21 @ X20 @ X20)
% 0.64/0.93          | ~ (v1_funct_2 @ X21 @ X20 @ X20)
% 0.64/0.93          | ~ (v1_funct_1 @ X21))),
% 0.64/0.93      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.64/0.93  thf('30', plain,
% 0.64/0.93      ((~ (v1_funct_1 @ sk_B)
% 0.64/0.93        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.64/0.93        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.64/0.93        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.64/0.93      inference('sup-', [status(thm)], ['28', '29'])).
% 0.64/0.93  thf('31', plain, ((v1_funct_1 @ sk_B)),
% 0.64/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.93  thf('32', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.64/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.93  thf('33', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.64/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.93  thf('34', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.64/0.93      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.64/0.93  thf('35', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.64/0.93      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.64/0.93  thf('36', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.64/0.93      inference('demod', [status(thm)], ['34', '35'])).
% 0.64/0.93  thf('37', plain,
% 0.64/0.93      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 0.64/0.93         = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 0.64/0.93      inference('demod', [status(thm)], ['27', '36'])).
% 0.64/0.93  thf('38', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.64/0.93      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.64/0.93  thf('39', plain,
% 0.64/0.93      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.93           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.64/0.93            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.64/0.93           (k6_partfun1 @ sk_A)))
% 0.64/0.93         <= (~
% 0.64/0.93             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.93               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.64/0.93                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.64/0.93               (k6_partfun1 @ sk_A))))),
% 0.64/0.93      inference('split', [status(esa)], ['0'])).
% 0.64/0.93  thf('40', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.64/0.93      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.64/0.93  thf('41', plain,
% 0.64/0.93      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.93           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.64/0.93            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.64/0.93           (k6_relat_1 @ sk_A)))
% 0.64/0.93         <= (~
% 0.64/0.93             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.93               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.64/0.93                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.64/0.93               (k6_partfun1 @ sk_A))))),
% 0.64/0.93      inference('demod', [status(thm)], ['39', '40'])).
% 0.64/0.93  thf('42', plain,
% 0.64/0.93      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.93           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.64/0.93            (k2_funct_1 @ sk_B)) @ 
% 0.64/0.93           (k6_relat_1 @ sk_A)))
% 0.64/0.93         <= (~
% 0.64/0.93             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.93               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.64/0.93                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.64/0.93               (k6_partfun1 @ sk_A))))),
% 0.64/0.93      inference('sup-', [status(thm)], ['38', '41'])).
% 0.64/0.93  thf('43', plain,
% 0.64/0.93      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.93           (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_relat_1 @ sk_A)))
% 0.64/0.93         <= (~
% 0.64/0.93             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.93               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.64/0.93                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.64/0.93               (k6_partfun1 @ sk_A))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['37', '42'])).
% 0.75/0.93  thf('44', plain,
% 0.75/0.93      (((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 0.75/0.93            (k6_relat_1 @ sk_A))
% 0.75/0.93         | ~ (v1_relat_1 @ sk_B)
% 0.75/0.93         | ~ (v1_funct_1 @ sk_B)
% 0.75/0.93         | ~ (v2_funct_1 @ sk_B)))
% 0.75/0.93         <= (~
% 0.75/0.93             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.75/0.93               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.75/0.93                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.75/0.93               (k6_partfun1 @ sk_A))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['12', '43'])).
% 0.75/0.93  thf('45', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(t67_funct_2, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.75/0.93         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.75/0.93       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.75/0.93  thf('46', plain,
% 0.75/0.93      (![X33 : $i, X34 : $i]:
% 0.75/0.93         (((k1_relset_1 @ X33 @ X33 @ X34) = (X33))
% 0.75/0.93          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))
% 0.75/0.93          | ~ (v1_funct_2 @ X34 @ X33 @ X33)
% 0.75/0.93          | ~ (v1_funct_1 @ X34))),
% 0.75/0.93      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.75/0.93  thf('47', plain,
% 0.75/0.93      ((~ (v1_funct_1 @ sk_B)
% 0.75/0.93        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.75/0.93        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['45', '46'])).
% 0.75/0.93  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('49', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('50', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(redefinition_k1_relset_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.93       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.75/0.93  thf('51', plain,
% 0.75/0.93      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.75/0.93         (((k1_relset_1 @ X9 @ X10 @ X8) = (k1_relat_1 @ X8))
% 0.75/0.93          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.75/0.93      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.75/0.93  thf('52', plain,
% 0.75/0.93      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.75/0.93      inference('sup-', [status(thm)], ['50', '51'])).
% 0.75/0.93  thf('53', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.75/0.93      inference('demod', [status(thm)], ['47', '48', '49', '52'])).
% 0.75/0.93  thf(dt_k6_partfun1, axiom,
% 0.75/0.93    (![A:$i]:
% 0.75/0.93     ( ( m1_subset_1 @
% 0.75/0.93         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.75/0.93       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.75/0.93  thf('54', plain,
% 0.75/0.93      (![X23 : $i]:
% 0.75/0.93         (m1_subset_1 @ (k6_partfun1 @ X23) @ 
% 0.75/0.93          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 0.75/0.93      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.75/0.93  thf('55', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.75/0.93      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.75/0.93  thf('56', plain,
% 0.75/0.93      (![X23 : $i]:
% 0.75/0.93         (m1_subset_1 @ (k6_relat_1 @ X23) @ 
% 0.75/0.93          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 0.75/0.93      inference('demod', [status(thm)], ['54', '55'])).
% 0.75/0.93  thf(redefinition_r2_relset_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.93     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.75/0.93         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.93       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.75/0.93  thf('57', plain,
% 0.75/0.93      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.75/0.93         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.75/0.93          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.75/0.93          | (r2_relset_1 @ X12 @ X13 @ X11 @ X14)
% 0.75/0.93          | ((X11) != (X14)))),
% 0.75/0.93      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.75/0.93  thf('58', plain,
% 0.75/0.93      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.75/0.93         ((r2_relset_1 @ X12 @ X13 @ X14 @ X14)
% 0.75/0.93          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.75/0.93      inference('simplify', [status(thm)], ['57'])).
% 0.75/0.93  thf('59', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['56', '58'])).
% 0.75/0.93  thf('60', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(cc2_relat_1, axiom,
% 0.75/0.93    (![A:$i]:
% 0.75/0.93     ( ( v1_relat_1 @ A ) =>
% 0.75/0.93       ( ![B:$i]:
% 0.75/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.75/0.93  thf('61', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.75/0.93          | (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_relat_1 @ X1))),
% 0.75/0.93      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.75/0.93  thf('62', plain,
% 0.75/0.93      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.75/0.93      inference('sup-', [status(thm)], ['60', '61'])).
% 0.75/0.93  thf(fc6_relat_1, axiom,
% 0.75/0.93    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.75/0.93  thf('63', plain,
% 0.75/0.93      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.75/0.93      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.75/0.93  thf('64', plain, ((v1_relat_1 @ sk_B)),
% 0.75/0.93      inference('demod', [status(thm)], ['62', '63'])).
% 0.75/0.93  thf('65', plain, ((v1_funct_1 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('66', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(cc2_funct_2, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.93       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.75/0.93         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.75/0.93  thf('67', plain,
% 0.75/0.93      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.75/0.93         (~ (v1_funct_1 @ X15)
% 0.75/0.93          | ~ (v3_funct_2 @ X15 @ X16 @ X17)
% 0.75/0.93          | (v2_funct_1 @ X15)
% 0.75/0.93          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.75/0.93      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.75/0.93  thf('68', plain,
% 0.75/0.93      (((v2_funct_1 @ sk_B)
% 0.75/0.93        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.75/0.93        | ~ (v1_funct_1 @ sk_B))),
% 0.75/0.93      inference('sup-', [status(thm)], ['66', '67'])).
% 0.75/0.93  thf('69', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('70', plain, ((v1_funct_1 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('71', plain, ((v2_funct_1 @ sk_B)),
% 0.75/0.93      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.75/0.93  thf('72', plain,
% 0.75/0.93      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.75/0.93         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.75/0.93          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.75/0.93         (k6_partfun1 @ sk_A)))),
% 0.75/0.93      inference('demod', [status(thm)], ['44', '53', '59', '64', '65', '71'])).
% 0.75/0.93  thf('73', plain,
% 0.75/0.93      (~
% 0.75/0.93       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.75/0.93         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.75/0.93          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.75/0.93         (k6_partfun1 @ sk_A))) | 
% 0.75/0.93       ~
% 0.75/0.93       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.75/0.93         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.75/0.93          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.75/0.93         (k6_partfun1 @ sk_A)))),
% 0.75/0.93      inference('split', [status(esa)], ['0'])).
% 0.75/0.93  thf('74', plain,
% 0.75/0.93      (~
% 0.75/0.93       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.75/0.93         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.75/0.93          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.75/0.93         (k6_partfun1 @ sk_A)))),
% 0.75/0.93      inference('sat_resolution*', [status(thm)], ['72', '73'])).
% 0.75/0.93  thf('75', plain,
% 0.75/0.93      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.75/0.93          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.75/0.93          (k6_relat_1 @ sk_A))),
% 0.75/0.93      inference('simpl_trail', [status(thm)], ['11', '74'])).
% 0.75/0.93  thf('76', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('77', plain,
% 0.75/0.93      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.75/0.93        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.93      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.75/0.93  thf('78', plain,
% 0.75/0.93      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.75/0.93         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.75/0.93          | ~ (v1_funct_1 @ X24)
% 0.75/0.93          | ~ (v1_funct_1 @ X27)
% 0.75/0.93          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.75/0.93          | ((k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 0.75/0.93              = (k5_relat_1 @ X24 @ X27)))),
% 0.75/0.93      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.75/0.93  thf('79', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.75/0.93            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 0.75/0.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['77', '78'])).
% 0.75/0.93  thf('80', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.75/0.93      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.75/0.93  thf('81', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.75/0.93            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 0.75/0.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.75/0.93          | ~ (v1_funct_1 @ X0))),
% 0.75/0.93      inference('demod', [status(thm)], ['79', '80'])).
% 0.75/0.93  thf('82', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.75/0.93      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.75/0.93  thf('83', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.75/0.93      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.75/0.93  thf('84', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.93         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.75/0.93            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.75/0.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.75/0.93          | ~ (v1_funct_1 @ X0))),
% 0.75/0.93      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.75/0.93  thf('85', plain,
% 0.75/0.93      ((~ (v1_funct_1 @ sk_B)
% 0.75/0.93        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.75/0.93            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['76', '84'])).
% 0.75/0.93  thf('86', plain, ((v1_funct_1 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('87', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('88', plain,
% 0.75/0.93      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.75/0.93         (~ (v1_funct_1 @ X15)
% 0.75/0.93          | ~ (v3_funct_2 @ X15 @ X16 @ X17)
% 0.75/0.93          | (v2_funct_2 @ X15 @ X17)
% 0.75/0.93          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.75/0.93      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.75/0.93  thf('89', plain,
% 0.75/0.93      (((v2_funct_2 @ sk_B @ sk_A)
% 0.75/0.93        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.75/0.93        | ~ (v1_funct_1 @ sk_B))),
% 0.75/0.93      inference('sup-', [status(thm)], ['87', '88'])).
% 0.75/0.93  thf('90', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('91', plain, ((v1_funct_1 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('92', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.75/0.93      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.75/0.93  thf(d3_funct_2, axiom,
% 0.75/0.93    (![A:$i,B:$i]:
% 0.75/0.93     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.75/0.93       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.75/0.93  thf('93', plain,
% 0.75/0.93      (![X18 : $i, X19 : $i]:
% 0.75/0.93         (~ (v2_funct_2 @ X19 @ X18)
% 0.75/0.93          | ((k2_relat_1 @ X19) = (X18))
% 0.75/0.93          | ~ (v5_relat_1 @ X19 @ X18)
% 0.75/0.93          | ~ (v1_relat_1 @ X19))),
% 0.75/0.93      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.75/0.93  thf('94', plain,
% 0.75/0.93      ((~ (v1_relat_1 @ sk_B)
% 0.75/0.93        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.75/0.93        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['92', '93'])).
% 0.75/0.93  thf('95', plain, ((v1_relat_1 @ sk_B)),
% 0.75/0.93      inference('demod', [status(thm)], ['62', '63'])).
% 0.75/0.93  thf('96', plain,
% 0.75/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf(cc2_relset_1, axiom,
% 0.75/0.93    (![A:$i,B:$i,C:$i]:
% 0.75/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.93       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.75/0.93  thf('97', plain,
% 0.75/0.93      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.75/0.93         ((v5_relat_1 @ X5 @ X7)
% 0.75/0.93          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.75/0.93      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.75/0.93  thf('98', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.75/0.93      inference('sup-', [status(thm)], ['96', '97'])).
% 0.75/0.93  thf('99', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.75/0.93      inference('demod', [status(thm)], ['94', '95', '98'])).
% 0.75/0.93  thf('100', plain,
% 0.75/0.93      (![X4 : $i]:
% 0.75/0.93         (~ (v2_funct_1 @ X4)
% 0.75/0.93          | ((k5_relat_1 @ (k2_funct_1 @ X4) @ X4)
% 0.75/0.93              = (k6_relat_1 @ (k2_relat_1 @ X4)))
% 0.75/0.93          | ~ (v1_funct_1 @ X4)
% 0.75/0.93          | ~ (v1_relat_1 @ X4))),
% 0.75/0.93      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.75/0.93  thf('101', plain,
% 0.75/0.93      (![X23 : $i]:
% 0.75/0.93         (m1_subset_1 @ (k6_relat_1 @ X23) @ 
% 0.75/0.93          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 0.75/0.93      inference('demod', [status(thm)], ['54', '55'])).
% 0.75/0.93  thf('102', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 0.75/0.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.75/0.93          | ~ (v1_relat_1 @ X0)
% 0.75/0.93          | ~ (v1_funct_1 @ X0)
% 0.75/0.93          | ~ (v2_funct_1 @ X0))),
% 0.75/0.93      inference('sup+', [status(thm)], ['100', '101'])).
% 0.75/0.93  thf('103', plain,
% 0.75/0.93      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.75/0.93         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))
% 0.75/0.93        | ~ (v2_funct_1 @ sk_B)
% 0.75/0.93        | ~ (v1_funct_1 @ sk_B)
% 0.75/0.93        | ~ (v1_relat_1 @ sk_B))),
% 0.75/0.93      inference('sup+', [status(thm)], ['99', '102'])).
% 0.75/0.93  thf('104', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.75/0.93      inference('demod', [status(thm)], ['94', '95', '98'])).
% 0.75/0.93  thf('105', plain, ((v2_funct_1 @ sk_B)),
% 0.75/0.93      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.75/0.93  thf('106', plain, ((v1_funct_1 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('107', plain, ((v1_relat_1 @ sk_B)),
% 0.75/0.93      inference('demod', [status(thm)], ['62', '63'])).
% 0.75/0.93  thf('108', plain,
% 0.75/0.93      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.75/0.93        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.93      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 0.75/0.93  thf('109', plain,
% 0.75/0.93      (![X23 : $i]:
% 0.75/0.93         (m1_subset_1 @ (k6_relat_1 @ X23) @ 
% 0.75/0.93          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 0.75/0.93      inference('demod', [status(thm)], ['54', '55'])).
% 0.75/0.93  thf('110', plain,
% 0.75/0.93      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.75/0.93         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.75/0.93          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.75/0.93          | ((X11) = (X14))
% 0.75/0.93          | ~ (r2_relset_1 @ X12 @ X13 @ X11 @ X14))),
% 0.75/0.93      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.75/0.93  thf('111', plain,
% 0.75/0.93      (![X0 : $i, X1 : $i]:
% 0.75/0.93         (~ (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ X1)
% 0.75/0.93          | ((k6_relat_1 @ X0) = (X1))
% 0.75/0.93          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0))))),
% 0.75/0.93      inference('sup-', [status(thm)], ['109', '110'])).
% 0.75/0.93  thf('112', plain,
% 0.75/0.93      ((((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 0.75/0.93        | ~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.75/0.93             (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 0.75/0.93      inference('sup-', [status(thm)], ['108', '111'])).
% 0.75/0.93  thf('113', plain,
% 0.75/0.93      (![X4 : $i]:
% 0.75/0.93         (~ (v2_funct_1 @ X4)
% 0.75/0.93          | ((k5_relat_1 @ (k2_funct_1 @ X4) @ X4)
% 0.75/0.93              = (k6_relat_1 @ (k2_relat_1 @ X4)))
% 0.75/0.93          | ~ (v1_funct_1 @ X4)
% 0.75/0.93          | ~ (v1_relat_1 @ X4))),
% 0.75/0.93      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.75/0.93  thf('114', plain,
% 0.75/0.93      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.75/0.93        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.93      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 0.75/0.93  thf('115', plain,
% 0.75/0.93      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.75/0.93         ((r2_relset_1 @ X12 @ X13 @ X14 @ X14)
% 0.75/0.93          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.75/0.93      inference('simplify', [status(thm)], ['57'])).
% 0.75/0.93  thf('116', plain,
% 0.75/0.93      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.75/0.93        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.75/0.93        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 0.75/0.93      inference('sup-', [status(thm)], ['114', '115'])).
% 0.75/0.93  thf('117', plain,
% 0.75/0.93      (((r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k2_relat_1 @ sk_B)) @ 
% 0.75/0.93         (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))
% 0.75/0.93        | ~ (v1_relat_1 @ sk_B)
% 0.75/0.93        | ~ (v1_funct_1 @ sk_B)
% 0.75/0.93        | ~ (v2_funct_1 @ sk_B))),
% 0.75/0.93      inference('sup+', [status(thm)], ['113', '116'])).
% 0.75/0.93  thf('118', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.75/0.93      inference('demod', [status(thm)], ['94', '95', '98'])).
% 0.75/0.93  thf('119', plain, ((v1_relat_1 @ sk_B)),
% 0.75/0.93      inference('demod', [status(thm)], ['62', '63'])).
% 0.75/0.93  thf('120', plain, ((v1_funct_1 @ sk_B)),
% 0.75/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.93  thf('121', plain, ((v2_funct_1 @ sk_B)),
% 0.75/0.93      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.75/0.93  thf('122', plain,
% 0.75/0.93      ((r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.75/0.93        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 0.75/0.93      inference('demod', [status(thm)], ['117', '118', '119', '120', '121'])).
% 0.75/0.93  thf('123', plain,
% 0.75/0.93      (((k6_relat_1 @ sk_A) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 0.75/0.93      inference('demod', [status(thm)], ['112', '122'])).
% 0.75/0.93  thf('124', plain,
% 0.75/0.93      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.75/0.93         = (k6_relat_1 @ sk_A))),
% 0.75/0.93      inference('demod', [status(thm)], ['85', '86', '123'])).
% 0.75/0.93  thf('125', plain,
% 0.75/0.93      (![X0 : $i]:
% 0.75/0.93         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.75/0.93      inference('sup-', [status(thm)], ['56', '58'])).
% 0.75/0.93  thf('126', plain, ($false),
% 0.75/0.93      inference('demod', [status(thm)], ['75', '124', '125'])).
% 0.75/0.93  
% 0.75/0.93  % SZS output end Refutation
% 0.75/0.93  
% 0.75/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
