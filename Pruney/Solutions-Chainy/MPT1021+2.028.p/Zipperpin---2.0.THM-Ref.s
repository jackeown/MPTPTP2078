%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rV7Rn73sdq

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:14 EST 2020

% Result     : Theorem 0.64s
% Output     : Refutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :  259 (5781 expanded)
%              Number of leaves         :   38 (1786 expanded)
%              Depth                    :   22
%              Number of atoms          : 2550 (154232 expanded)
%              Number of equality atoms :   73 ( 829 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

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
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
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
    ! [X29: $i,X30: $i] :
      ( ( ( k2_funct_2 @ X30 @ X29 )
        = ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( v3_funct_2 @ X29 @ X30 @ X30 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
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

thf('12',plain,(
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

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('19',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 )
        = ( k5_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0 )
        = ( k5_relat_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('28',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['28','29','30','31'])).

thf('33',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('34',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('35',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X3 ) )
        = X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('36',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X3 ) )
        = X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('37',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('38',plain,(
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('39',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_funct_2 @ ( k2_funct_2 @ X19 @ X20 ) @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('43',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('48',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X19 @ X20 ) @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('51',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('56',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('57',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','48','56'])).

thf('58',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('59',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k2_funct_2 @ X30 @ X29 )
        = ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( v3_funct_2 @ X29 @ X30 @ X30 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('60',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('62',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('63',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('64',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('65',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','64'])).

thf('66',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k2_funct_2 @ X30 @ X29 )
        = ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X30 ) ) )
      | ~ ( v3_funct_2 @ X29 @ X30 @ X30 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('67',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('69',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('70',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('72',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('73',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('74',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('76',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('78',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v1_funct_2 @ ( k2_funct_2 @ X19 @ X20 ) @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('79',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( v1_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('81',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('82',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('83',plain,(
    v1_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['79','80','81','82'])).

thf('84',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('85',plain,(
    v1_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('87',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v3_funct_2 @ ( k2_funct_2 @ X19 @ X20 ) @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_2])).

thf('88',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ( v3_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('90',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('91',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('92',plain,(
    v3_funct_2 @ ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61','62','63'])).

thf('94',plain,(
    v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k2_funct_2 @ sk_A @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['67','76','85','94'])).

thf('96',plain,
    ( ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['36','95'])).

thf('97',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('98',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('99',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('100',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
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

thf('103',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v3_funct_2 @ X14 @ X15 @ X16 )
      | ( v2_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('104',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['96','97','100','101','107'])).

thf(t62_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('109',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t62_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('112',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X3 ) )
        = X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('113',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ X1 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['110','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['109','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_B ) )
      = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['108','120'])).

thf('122',plain,
    ( ( k2_funct_1 @ sk_B )
    = ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['96','97','100','101','107'])).

thf('123',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('124',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v3_funct_2 @ X14 @ X15 @ X16 )
      | ( v2_funct_2 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('125',plain,
    ( ( v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('127',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('128',plain,(
    v2_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['125','126','127'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('129',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_funct_2 @ X18 @ X17 )
      | ( ( k2_relat_1 @ X18 )
        = X17 )
      | ~ ( v5_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('130',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('132',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('133',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('135',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v5_relat_1 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('136',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['130','133','136'])).

thf('138',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','64'])).

thf('139',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('140',plain,(
    v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('142',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','64'])).

thf('143',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v3_funct_2 @ X14 @ X15 @ X16 )
      | ( v2_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('144',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['92','93'])).

thf('146',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('147',plain,(
    v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['121','122','137','140','141','147'])).

thf('149',plain,
    ( ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['35','148'])).

thf('150',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['98','99'])).

thf('151',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('153',plain,
    ( ( k5_relat_1 @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['149','150','151','152'])).

thf('154',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','34','153'])).

thf('155',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('156',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('157',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('158',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_1 @ sk_B ) ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['155','158'])).

thf('160',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
   <= ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['154','159'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('161',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('162',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('163',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('164',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_relset_1 @ X10 @ X11 @ X12 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('165',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['163','165'])).

thf('167',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['160','166'])).

thf('168',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('169',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['167','168'])).

thf('170',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['11','169'])).

thf('171',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('173',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 )
        = ( k5_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('174',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('176',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['171','176'])).

thf('178',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('180',plain,(
    ! [X3: $i] :
      ( ~ ( v2_funct_1 @ X3 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X3 ) )
        = X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('181',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['180','181'])).

thf('183',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['179','182'])).

thf('184',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15','16','17','18'])).

thf('185',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v3_funct_2 @ X14 @ X15 @ X16 )
      | ( v2_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('186',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    v3_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('188',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('189',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('190',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('191',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('192',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['98','99'])).

thf('194',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','64'])).

thf('195',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v3_funct_2 @ X14 @ X15 @ X16 )
      | ( v2_funct_2 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('196',plain,
    ( ( v2_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A )
    | ~ ( v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    v3_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['92','93'])).

thf('198',plain,(
    v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('199',plain,(
    v2_funct_2 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A ),
    inference(demod,[status(thm)],['196','197','198'])).

thf('200',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_funct_2 @ X18 @ X17 )
      | ( ( k2_relat_1 @ X18 )
        = X17 )
      | ~ ( v5_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('201',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    | ~ ( v5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('203',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','64'])).

thf('204',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v5_relat_1 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('205',plain,(
    v5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) @ sk_A ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_B ) ) )
    = sk_A ),
    inference(demod,[status(thm)],['201','202','205'])).

thf('207',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k2_funct_1 @ X1 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,
    ( ( ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['206','210'])).

thf('212',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('213',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('214',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('215',plain,
    ( ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_B ) ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['211','212','213','214'])).

thf('216',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['183','189','190','191','192','193','215'])).

thf('217',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['177','178','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['163','165'])).

thf('219',plain,(
    $false ),
    inference(demod,[status(thm)],['170','217','218'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rV7Rn73sdq
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:06:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.64/0.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.64/0.81  % Solved by: fo/fo7.sh
% 0.64/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.64/0.81  % done 637 iterations in 0.351s
% 0.64/0.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.64/0.81  % SZS output start Refutation
% 0.64/0.81  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.64/0.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.64/0.81  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.64/0.81  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.64/0.81  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.64/0.81  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.64/0.81  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.64/0.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.64/0.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.64/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.64/0.81  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.64/0.81  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.64/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.64/0.81  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.64/0.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.64/0.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.64/0.81  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.64/0.81  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.64/0.81  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.64/0.81  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.64/0.81  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.64/0.81  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.64/0.81  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.64/0.81  thf(t88_funct_2, conjecture,
% 0.64/0.81    (![A:$i,B:$i]:
% 0.64/0.81     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.64/0.81         ( v3_funct_2 @ B @ A @ A ) & 
% 0.64/0.81         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.64/0.81       ( ( r2_relset_1 @
% 0.64/0.81           A @ A @ 
% 0.64/0.81           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.64/0.81           ( k6_partfun1 @ A ) ) & 
% 0.64/0.81         ( r2_relset_1 @
% 0.64/0.81           A @ A @ 
% 0.64/0.81           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.64/0.81           ( k6_partfun1 @ A ) ) ) ))).
% 0.64/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.64/0.81    (~( ![A:$i,B:$i]:
% 0.64/0.81        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.64/0.81            ( v3_funct_2 @ B @ A @ A ) & 
% 0.64/0.81            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.64/0.81          ( ( r2_relset_1 @
% 0.64/0.81              A @ A @ 
% 0.64/0.81              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.64/0.81              ( k6_partfun1 @ A ) ) & 
% 0.64/0.81            ( r2_relset_1 @
% 0.64/0.81              A @ A @ 
% 0.64/0.81              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.64/0.81              ( k6_partfun1 @ A ) ) ) ) )),
% 0.64/0.81    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.64/0.81  thf('0', plain,
% 0.64/0.81      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.81           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.64/0.81            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.64/0.81           (k6_partfun1 @ sk_A))
% 0.64/0.81        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.81             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.64/0.81              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.64/0.81             (k6_partfun1 @ sk_A)))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('1', plain,
% 0.64/0.81      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.81           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.64/0.81            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.64/0.81           (k6_partfun1 @ sk_A)))
% 0.64/0.81         <= (~
% 0.64/0.81             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.81               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.64/0.81                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.64/0.81               (k6_partfun1 @ sk_A))))),
% 0.64/0.81      inference('split', [status(esa)], ['0'])).
% 0.64/0.81  thf(redefinition_k6_partfun1, axiom,
% 0.64/0.81    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.64/0.81  thf('2', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.64/0.81      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.64/0.81  thf('3', plain,
% 0.64/0.81      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.81           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.64/0.81            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.64/0.81           (k6_relat_1 @ sk_A)))
% 0.64/0.81         <= (~
% 0.64/0.81             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.81               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.64/0.81                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.64/0.81               (k6_partfun1 @ sk_A))))),
% 0.64/0.81      inference('demod', [status(thm)], ['1', '2'])).
% 0.64/0.81  thf('4', plain,
% 0.64/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf(redefinition_k2_funct_2, axiom,
% 0.64/0.81    (![A:$i,B:$i]:
% 0.64/0.81     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.64/0.81         ( v3_funct_2 @ B @ A @ A ) & 
% 0.64/0.81         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.64/0.81       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.64/0.81  thf('5', plain,
% 0.64/0.81      (![X29 : $i, X30 : $i]:
% 0.64/0.81         (((k2_funct_2 @ X30 @ X29) = (k2_funct_1 @ X29))
% 0.64/0.81          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 0.64/0.81          | ~ (v3_funct_2 @ X29 @ X30 @ X30)
% 0.64/0.81          | ~ (v1_funct_2 @ X29 @ X30 @ X30)
% 0.64/0.81          | ~ (v1_funct_1 @ X29))),
% 0.64/0.81      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.64/0.81  thf('6', plain,
% 0.64/0.81      ((~ (v1_funct_1 @ sk_B)
% 0.64/0.81        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.64/0.81        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.64/0.81        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.64/0.81      inference('sup-', [status(thm)], ['4', '5'])).
% 0.64/0.81  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('8', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('9', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('10', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.64/0.81      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.64/0.81  thf('11', plain,
% 0.64/0.81      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.81           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.64/0.81            sk_B) @ 
% 0.64/0.81           (k6_relat_1 @ sk_A)))
% 0.64/0.81         <= (~
% 0.64/0.81             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.81               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.64/0.81                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.64/0.81               (k6_partfun1 @ sk_A))))),
% 0.64/0.81      inference('demod', [status(thm)], ['3', '10'])).
% 0.64/0.81  thf('12', plain,
% 0.64/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf(dt_k2_funct_2, axiom,
% 0.64/0.81    (![A:$i,B:$i]:
% 0.64/0.81     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.64/0.81         ( v3_funct_2 @ B @ A @ A ) & 
% 0.64/0.81         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.64/0.81       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.64/0.81         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.64/0.81         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.64/0.81         ( m1_subset_1 @
% 0.64/0.81           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.64/0.81  thf('13', plain,
% 0.64/0.81      (![X19 : $i, X20 : $i]:
% 0.64/0.81         ((m1_subset_1 @ (k2_funct_2 @ X19 @ X20) @ 
% 0.64/0.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.64/0.81          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.64/0.81          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 0.64/0.81          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 0.64/0.81          | ~ (v1_funct_1 @ X20))),
% 0.64/0.81      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.64/0.81  thf('14', plain,
% 0.64/0.81      ((~ (v1_funct_1 @ sk_B)
% 0.64/0.81        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.64/0.81        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.64/0.81        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.64/0.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.64/0.81      inference('sup-', [status(thm)], ['12', '13'])).
% 0.64/0.81  thf('15', plain, ((v1_funct_1 @ sk_B)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('16', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('17', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('18', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.64/0.81      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.64/0.81  thf('19', plain,
% 0.64/0.81      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.64/0.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.81      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.64/0.81  thf('20', plain,
% 0.64/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf(redefinition_k1_partfun1, axiom,
% 0.64/0.81    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.64/0.81     ( ( ( v1_funct_1 @ E ) & 
% 0.64/0.81         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.64/0.81         ( v1_funct_1 @ F ) & 
% 0.64/0.81         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.64/0.81       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.64/0.81  thf('21', plain,
% 0.64/0.81      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.64/0.81         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.64/0.81          | ~ (v1_funct_1 @ X23)
% 0.64/0.81          | ~ (v1_funct_1 @ X26)
% 0.64/0.81          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.64/0.81          | ((k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26)
% 0.64/0.81              = (k5_relat_1 @ X23 @ X26)))),
% 0.64/0.81      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.64/0.81  thf('22', plain,
% 0.64/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.81         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.64/0.81            = (k5_relat_1 @ sk_B @ X0))
% 0.64/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.64/0.81          | ~ (v1_funct_1 @ X0)
% 0.64/0.81          | ~ (v1_funct_1 @ sk_B))),
% 0.64/0.81      inference('sup-', [status(thm)], ['20', '21'])).
% 0.64/0.81  thf('23', plain, ((v1_funct_1 @ sk_B)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('24', plain,
% 0.64/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.81         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.64/0.81            = (k5_relat_1 @ sk_B @ X0))
% 0.64/0.81          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.64/0.81          | ~ (v1_funct_1 @ X0))),
% 0.64/0.81      inference('demod', [status(thm)], ['22', '23'])).
% 0.64/0.81  thf('25', plain,
% 0.64/0.81      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.64/0.81        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.64/0.81            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 0.64/0.81      inference('sup-', [status(thm)], ['19', '24'])).
% 0.64/0.81  thf('26', plain,
% 0.64/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('27', plain,
% 0.64/0.81      (![X19 : $i, X20 : $i]:
% 0.64/0.81         ((v1_funct_1 @ (k2_funct_2 @ X19 @ X20))
% 0.64/0.81          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.64/0.81          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 0.64/0.81          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 0.64/0.81          | ~ (v1_funct_1 @ X20))),
% 0.64/0.81      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.64/0.81  thf('28', plain,
% 0.64/0.81      ((~ (v1_funct_1 @ sk_B)
% 0.64/0.81        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.64/0.81        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.64/0.81        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.64/0.81      inference('sup-', [status(thm)], ['26', '27'])).
% 0.64/0.81  thf('29', plain, ((v1_funct_1 @ sk_B)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('30', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('31', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('32', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.64/0.81      inference('demod', [status(thm)], ['28', '29', '30', '31'])).
% 0.64/0.81  thf('33', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.64/0.81      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.64/0.81  thf('34', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.64/0.81      inference('demod', [status(thm)], ['32', '33'])).
% 0.64/0.81  thf(t65_funct_1, axiom,
% 0.64/0.81    (![A:$i]:
% 0.64/0.81     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.64/0.81       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.64/0.81  thf('35', plain,
% 0.64/0.81      (![X3 : $i]:
% 0.64/0.81         (~ (v2_funct_1 @ X3)
% 0.64/0.81          | ((k2_funct_1 @ (k2_funct_1 @ X3)) = (X3))
% 0.64/0.81          | ~ (v1_funct_1 @ X3)
% 0.64/0.81          | ~ (v1_relat_1 @ X3))),
% 0.64/0.81      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.64/0.81  thf('36', plain,
% 0.64/0.81      (![X3 : $i]:
% 0.64/0.81         (~ (v2_funct_1 @ X3)
% 0.64/0.81          | ((k2_funct_1 @ (k2_funct_1 @ X3)) = (X3))
% 0.64/0.81          | ~ (v1_funct_1 @ X3)
% 0.64/0.81          | ~ (v1_relat_1 @ X3))),
% 0.64/0.81      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.64/0.81  thf('37', plain,
% 0.64/0.81      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.64/0.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.81      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.64/0.81  thf('38', plain,
% 0.64/0.81      (![X19 : $i, X20 : $i]:
% 0.64/0.81         ((m1_subset_1 @ (k2_funct_2 @ X19 @ X20) @ 
% 0.64/0.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.64/0.81          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.64/0.81          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 0.64/0.81          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 0.64/0.81          | ~ (v1_funct_1 @ X20))),
% 0.64/0.81      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.64/0.81  thf('39', plain,
% 0.64/0.81      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.64/0.81        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.64/0.81        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.64/0.81        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ 
% 0.64/0.81           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.64/0.81      inference('sup-', [status(thm)], ['37', '38'])).
% 0.64/0.81  thf('40', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.64/0.81      inference('demod', [status(thm)], ['32', '33'])).
% 0.64/0.81  thf('41', plain,
% 0.64/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('42', plain,
% 0.64/0.81      (![X19 : $i, X20 : $i]:
% 0.64/0.81         ((v1_funct_2 @ (k2_funct_2 @ X19 @ X20) @ X19 @ X19)
% 0.64/0.81          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.64/0.81          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 0.64/0.81          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 0.64/0.81          | ~ (v1_funct_1 @ X20))),
% 0.64/0.81      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.64/0.81  thf('43', plain,
% 0.64/0.81      ((~ (v1_funct_1 @ sk_B)
% 0.64/0.81        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.64/0.81        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.64/0.81        | (v1_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.64/0.81      inference('sup-', [status(thm)], ['41', '42'])).
% 0.64/0.81  thf('44', plain, ((v1_funct_1 @ sk_B)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('45', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('46', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('47', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.64/0.81      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.64/0.81  thf('48', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.64/0.81      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.64/0.81  thf('49', plain,
% 0.64/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('50', plain,
% 0.64/0.81      (![X19 : $i, X20 : $i]:
% 0.64/0.81         ((v3_funct_2 @ (k2_funct_2 @ X19 @ X20) @ X19 @ X19)
% 0.64/0.81          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.64/0.81          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 0.64/0.81          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 0.64/0.81          | ~ (v1_funct_1 @ X20))),
% 0.64/0.81      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.64/0.81  thf('51', plain,
% 0.64/0.81      ((~ (v1_funct_1 @ sk_B)
% 0.64/0.81        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.64/0.81        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.64/0.81        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ sk_B) @ sk_A @ sk_A))),
% 0.64/0.81      inference('sup-', [status(thm)], ['49', '50'])).
% 0.64/0.81  thf('52', plain, ((v1_funct_1 @ sk_B)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('53', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('54', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.64/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.81  thf('55', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.64/0.81      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.64/0.81  thf('56', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.64/0.81      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 0.64/0.81  thf('57', plain,
% 0.64/0.81      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ 
% 0.64/0.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.81      inference('demod', [status(thm)], ['39', '40', '48', '56'])).
% 0.64/0.81  thf('58', plain,
% 0.64/0.81      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.64/0.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.81      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.64/0.81  thf('59', plain,
% 0.64/0.81      (![X29 : $i, X30 : $i]:
% 0.64/0.81         (((k2_funct_2 @ X30 @ X29) = (k2_funct_1 @ X29))
% 0.64/0.81          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 0.64/0.81          | ~ (v3_funct_2 @ X29 @ X30 @ X30)
% 0.64/0.81          | ~ (v1_funct_2 @ X29 @ X30 @ X30)
% 0.64/0.81          | ~ (v1_funct_1 @ X29))),
% 0.64/0.81      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.64/0.81  thf('60', plain,
% 0.64/0.81      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.64/0.81        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.64/0.81        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.64/0.81        | ((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 0.64/0.81            = (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.64/0.81      inference('sup-', [status(thm)], ['58', '59'])).
% 0.64/0.81  thf('61', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.64/0.81      inference('demod', [status(thm)], ['32', '33'])).
% 0.64/0.81  thf('62', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.64/0.81      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.64/0.81  thf('63', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.64/0.81      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 0.64/0.81  thf('64', plain,
% 0.64/0.81      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 0.64/0.81         = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.64/0.81      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.64/0.81  thf('65', plain,
% 0.64/0.81      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 0.64/0.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.81      inference('demod', [status(thm)], ['57', '64'])).
% 0.64/0.81  thf('66', plain,
% 0.64/0.81      (![X29 : $i, X30 : $i]:
% 0.64/0.81         (((k2_funct_2 @ X30 @ X29) = (k2_funct_1 @ X29))
% 0.64/0.81          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X30)))
% 0.64/0.81          | ~ (v3_funct_2 @ X29 @ X30 @ X30)
% 0.64/0.81          | ~ (v1_funct_2 @ X29 @ X30 @ X30)
% 0.64/0.81          | ~ (v1_funct_1 @ X29))),
% 0.64/0.81      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.64/0.81  thf('67', plain,
% 0.64/0.81      ((~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.64/0.81        | ~ (v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)
% 0.64/0.81        | ~ (v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)
% 0.64/0.81        | ((k2_funct_2 @ sk_A @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.64/0.81            = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))))),
% 0.64/0.81      inference('sup-', [status(thm)], ['65', '66'])).
% 0.64/0.81  thf('68', plain,
% 0.64/0.81      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.64/0.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.81      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.64/0.81  thf('69', plain,
% 0.64/0.81      (![X19 : $i, X20 : $i]:
% 0.64/0.81         ((v1_funct_1 @ (k2_funct_2 @ X19 @ X20))
% 0.64/0.81          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.64/0.81          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 0.64/0.81          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 0.64/0.81          | ~ (v1_funct_1 @ X20))),
% 0.64/0.81      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.64/0.81  thf('70', plain,
% 0.64/0.81      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.64/0.81        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.64/0.81        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.64/0.81        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))))),
% 0.64/0.81      inference('sup-', [status(thm)], ['68', '69'])).
% 0.64/0.81  thf('71', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.64/0.81      inference('demod', [status(thm)], ['32', '33'])).
% 0.64/0.81  thf('72', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.64/0.81      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.64/0.81  thf('73', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.64/0.81      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 0.64/0.81  thf('74', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)))),
% 0.64/0.81      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.64/0.81  thf('75', plain,
% 0.64/0.81      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 0.64/0.81         = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.64/0.81      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.64/0.81  thf('76', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.64/0.81      inference('demod', [status(thm)], ['74', '75'])).
% 0.64/0.81  thf('77', plain,
% 0.64/0.81      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.64/0.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.81      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.64/0.81  thf('78', plain,
% 0.64/0.81      (![X19 : $i, X20 : $i]:
% 0.64/0.81         ((v1_funct_2 @ (k2_funct_2 @ X19 @ X20) @ X19 @ X19)
% 0.64/0.81          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.64/0.81          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 0.64/0.81          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 0.64/0.81          | ~ (v1_funct_1 @ X20))),
% 0.64/0.81      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.64/0.81  thf('79', plain,
% 0.64/0.81      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.64/0.81        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.64/0.81        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.64/0.81        | (v1_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A))),
% 0.64/0.81      inference('sup-', [status(thm)], ['77', '78'])).
% 0.64/0.81  thf('80', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.64/0.81      inference('demod', [status(thm)], ['32', '33'])).
% 0.64/0.81  thf('81', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.64/0.81      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.64/0.81  thf('82', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.64/0.81      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 0.64/0.81  thf('83', plain,
% 0.64/0.81      ((v1_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 0.64/0.81      inference('demod', [status(thm)], ['79', '80', '81', '82'])).
% 0.64/0.81  thf('84', plain,
% 0.64/0.81      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 0.64/0.81         = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.64/0.81      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.64/0.81  thf('85', plain,
% 0.64/0.81      ((v1_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 0.64/0.81      inference('demod', [status(thm)], ['83', '84'])).
% 0.64/0.81  thf('86', plain,
% 0.64/0.81      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.64/0.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.81      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.64/0.81  thf('87', plain,
% 0.64/0.81      (![X19 : $i, X20 : $i]:
% 0.64/0.81         ((v3_funct_2 @ (k2_funct_2 @ X19 @ X20) @ X19 @ X19)
% 0.64/0.81          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.64/0.81          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 0.64/0.81          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 0.64/0.81          | ~ (v1_funct_1 @ X20))),
% 0.64/0.81      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.64/0.81  thf('88', plain,
% 0.64/0.81      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.64/0.81        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.64/0.81        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.64/0.81        | (v3_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A))),
% 0.64/0.81      inference('sup-', [status(thm)], ['86', '87'])).
% 0.64/0.81  thf('89', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.64/0.81      inference('demod', [status(thm)], ['32', '33'])).
% 0.64/0.81  thf('90', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.64/0.81      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.64/0.81  thf('91', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.64/0.81      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 0.64/0.81  thf('92', plain,
% 0.64/0.81      ((v3_funct_2 @ (k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 0.64/0.81      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 0.64/0.81  thf('93', plain,
% 0.64/0.81      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ sk_B))
% 0.64/0.81         = (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.64/0.81      inference('demod', [status(thm)], ['60', '61', '62', '63'])).
% 0.64/0.81  thf('94', plain,
% 0.64/0.81      ((v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 0.64/0.81      inference('demod', [status(thm)], ['92', '93'])).
% 0.64/0.81  thf('95', plain,
% 0.64/0.81      (((k2_funct_2 @ sk_A @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.64/0.81         = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.64/0.82      inference('demod', [status(thm)], ['67', '76', '85', '94'])).
% 0.64/0.82  thf('96', plain,
% 0.64/0.82      ((((k2_funct_2 @ sk_A @ sk_B)
% 0.64/0.82          = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))
% 0.64/0.82        | ~ (v1_relat_1 @ sk_B)
% 0.64/0.82        | ~ (v1_funct_1 @ sk_B)
% 0.64/0.82        | ~ (v2_funct_1 @ sk_B))),
% 0.64/0.82      inference('sup+', [status(thm)], ['36', '95'])).
% 0.64/0.82  thf('97', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.64/0.82      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.64/0.82  thf('98', plain,
% 0.64/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.82  thf(cc1_relset_1, axiom,
% 0.64/0.82    (![A:$i,B:$i,C:$i]:
% 0.64/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.64/0.82       ( v1_relat_1 @ C ) ))).
% 0.64/0.82  thf('99', plain,
% 0.64/0.82      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.64/0.82         ((v1_relat_1 @ X4)
% 0.64/0.82          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.64/0.82      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.64/0.82  thf('100', plain, ((v1_relat_1 @ sk_B)),
% 0.64/0.82      inference('sup-', [status(thm)], ['98', '99'])).
% 0.64/0.82  thf('101', plain, ((v1_funct_1 @ sk_B)),
% 0.64/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.82  thf('102', plain,
% 0.64/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.82  thf(cc2_funct_2, axiom,
% 0.64/0.82    (![A:$i,B:$i,C:$i]:
% 0.64/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.64/0.82       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.64/0.82         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.64/0.82  thf('103', plain,
% 0.64/0.82      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.64/0.82         (~ (v1_funct_1 @ X14)
% 0.64/0.82          | ~ (v3_funct_2 @ X14 @ X15 @ X16)
% 0.64/0.82          | (v2_funct_1 @ X14)
% 0.64/0.82          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.64/0.82      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.64/0.82  thf('104', plain,
% 0.64/0.82      (((v2_funct_1 @ sk_B)
% 0.64/0.82        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.64/0.82        | ~ (v1_funct_1 @ sk_B))),
% 0.64/0.82      inference('sup-', [status(thm)], ['102', '103'])).
% 0.64/0.82  thf('105', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.64/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.82  thf('106', plain, ((v1_funct_1 @ sk_B)),
% 0.64/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.82  thf('107', plain, ((v2_funct_1 @ sk_B)),
% 0.64/0.82      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.64/0.82  thf('108', plain,
% 0.64/0.82      (((k2_funct_1 @ sk_B) = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.64/0.82      inference('demod', [status(thm)], ['96', '97', '100', '101', '107'])).
% 0.64/0.82  thf(t62_funct_1, axiom,
% 0.64/0.82    (![A:$i]:
% 0.64/0.82     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.64/0.82       ( ( v2_funct_1 @ A ) => ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.64/0.82  thf('109', plain,
% 0.64/0.82      (![X2 : $i]:
% 0.64/0.82         (~ (v2_funct_1 @ X2)
% 0.64/0.82          | (v2_funct_1 @ (k2_funct_1 @ X2))
% 0.64/0.82          | ~ (v1_funct_1 @ X2)
% 0.64/0.82          | ~ (v1_relat_1 @ X2))),
% 0.64/0.82      inference('cnf', [status(esa)], [t62_funct_1])).
% 0.64/0.82  thf(dt_k2_funct_1, axiom,
% 0.64/0.82    (![A:$i]:
% 0.64/0.82     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.64/0.82       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.64/0.82         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.64/0.82  thf('110', plain,
% 0.64/0.82      (![X0 : $i]:
% 0.64/0.82         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.64/0.82          | ~ (v1_funct_1 @ X0)
% 0.64/0.82          | ~ (v1_relat_1 @ X0))),
% 0.64/0.82      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.64/0.82  thf('111', plain,
% 0.64/0.82      (![X0 : $i]:
% 0.64/0.82         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.64/0.82          | ~ (v1_funct_1 @ X0)
% 0.64/0.82          | ~ (v1_relat_1 @ X0))),
% 0.64/0.82      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.64/0.82  thf('112', plain,
% 0.64/0.82      (![X3 : $i]:
% 0.64/0.82         (~ (v2_funct_1 @ X3)
% 0.64/0.82          | ((k2_funct_1 @ (k2_funct_1 @ X3)) = (X3))
% 0.64/0.82          | ~ (v1_funct_1 @ X3)
% 0.64/0.82          | ~ (v1_relat_1 @ X3))),
% 0.64/0.82      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.64/0.82  thf(t61_funct_1, axiom,
% 0.64/0.82    (![A:$i]:
% 0.64/0.82     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.64/0.82       ( ( v2_funct_1 @ A ) =>
% 0.64/0.82         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.64/0.82             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.64/0.82           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.64/0.82             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.64/0.82  thf('113', plain,
% 0.64/0.82      (![X1 : $i]:
% 0.64/0.82         (~ (v2_funct_1 @ X1)
% 0.64/0.82          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ X1)
% 0.64/0.82              = (k6_relat_1 @ (k2_relat_1 @ X1)))
% 0.64/0.82          | ~ (v1_funct_1 @ X1)
% 0.64/0.82          | ~ (v1_relat_1 @ X1))),
% 0.64/0.82      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.64/0.82  thf('114', plain,
% 0.64/0.82      (![X0 : $i]:
% 0.64/0.82         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.64/0.82            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.64/0.82          | ~ (v1_relat_1 @ X0)
% 0.64/0.82          | ~ (v1_funct_1 @ X0)
% 0.64/0.82          | ~ (v2_funct_1 @ X0)
% 0.64/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.64/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.64/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.64/0.82      inference('sup+', [status(thm)], ['112', '113'])).
% 0.64/0.82  thf('115', plain,
% 0.64/0.82      (![X0 : $i]:
% 0.64/0.82         (~ (v1_relat_1 @ X0)
% 0.64/0.82          | ~ (v1_funct_1 @ X0)
% 0.64/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.64/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.64/0.82          | ~ (v2_funct_1 @ X0)
% 0.64/0.82          | ~ (v1_funct_1 @ X0)
% 0.64/0.82          | ~ (v1_relat_1 @ X0)
% 0.64/0.82          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.64/0.82              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.64/0.82      inference('sup-', [status(thm)], ['111', '114'])).
% 0.64/0.82  thf('116', plain,
% 0.64/0.82      (![X0 : $i]:
% 0.64/0.82         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.64/0.82            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.64/0.82          | ~ (v2_funct_1 @ X0)
% 0.64/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.64/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.64/0.82          | ~ (v1_funct_1 @ X0)
% 0.64/0.82          | ~ (v1_relat_1 @ X0))),
% 0.64/0.82      inference('simplify', [status(thm)], ['115'])).
% 0.64/0.82  thf('117', plain,
% 0.64/0.82      (![X0 : $i]:
% 0.64/0.82         (~ (v1_relat_1 @ X0)
% 0.64/0.82          | ~ (v1_funct_1 @ X0)
% 0.64/0.82          | ~ (v1_relat_1 @ X0)
% 0.64/0.82          | ~ (v1_funct_1 @ X0)
% 0.64/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.64/0.82          | ~ (v2_funct_1 @ X0)
% 0.64/0.82          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.64/0.82              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.64/0.82      inference('sup-', [status(thm)], ['110', '116'])).
% 0.64/0.82  thf('118', plain,
% 0.64/0.82      (![X0 : $i]:
% 0.64/0.82         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.64/0.82            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.64/0.82          | ~ (v2_funct_1 @ X0)
% 0.64/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.64/0.82          | ~ (v1_funct_1 @ X0)
% 0.64/0.82          | ~ (v1_relat_1 @ X0))),
% 0.64/0.82      inference('simplify', [status(thm)], ['117'])).
% 0.64/0.82  thf('119', plain,
% 0.64/0.82      (![X0 : $i]:
% 0.64/0.82         (~ (v1_relat_1 @ X0)
% 0.64/0.82          | ~ (v1_funct_1 @ X0)
% 0.64/0.82          | ~ (v2_funct_1 @ X0)
% 0.64/0.82          | ~ (v1_relat_1 @ X0)
% 0.64/0.82          | ~ (v1_funct_1 @ X0)
% 0.64/0.82          | ~ (v2_funct_1 @ X0)
% 0.64/0.82          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.64/0.82              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.64/0.82      inference('sup-', [status(thm)], ['109', '118'])).
% 0.64/0.82  thf('120', plain,
% 0.64/0.82      (![X0 : $i]:
% 0.64/0.82         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.64/0.82            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.64/0.82          | ~ (v2_funct_1 @ X0)
% 0.64/0.82          | ~ (v1_funct_1 @ X0)
% 0.64/0.82          | ~ (v1_relat_1 @ X0))),
% 0.64/0.82      inference('simplify', [status(thm)], ['119'])).
% 0.64/0.82  thf('121', plain,
% 0.64/0.82      ((((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ (k2_funct_1 @ sk_B))
% 0.64/0.82          = (k6_relat_1 @ 
% 0.64/0.82             (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))))
% 0.64/0.82        | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.64/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.64/0.82        | ~ (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.64/0.82      inference('sup+', [status(thm)], ['108', '120'])).
% 0.64/0.82  thf('122', plain,
% 0.64/0.82      (((k2_funct_1 @ sk_B) = (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.64/0.82      inference('demod', [status(thm)], ['96', '97', '100', '101', '107'])).
% 0.64/0.82  thf('123', plain,
% 0.64/0.82      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.64/0.82        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.82      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.64/0.82  thf('124', plain,
% 0.64/0.82      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.64/0.82         (~ (v1_funct_1 @ X14)
% 0.64/0.82          | ~ (v3_funct_2 @ X14 @ X15 @ X16)
% 0.64/0.82          | (v2_funct_2 @ X14 @ X16)
% 0.64/0.82          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.64/0.82      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.64/0.82  thf('125', plain,
% 0.64/0.82      (((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)
% 0.64/0.82        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.64/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.64/0.82      inference('sup-', [status(thm)], ['123', '124'])).
% 0.64/0.82  thf('126', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.64/0.82      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 0.64/0.82  thf('127', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.64/0.82      inference('demod', [status(thm)], ['32', '33'])).
% 0.64/0.82  thf('128', plain, ((v2_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 0.64/0.82      inference('demod', [status(thm)], ['125', '126', '127'])).
% 0.64/0.82  thf(d3_funct_2, axiom,
% 0.64/0.82    (![A:$i,B:$i]:
% 0.64/0.82     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.64/0.82       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.64/0.82  thf('129', plain,
% 0.64/0.82      (![X17 : $i, X18 : $i]:
% 0.64/0.82         (~ (v2_funct_2 @ X18 @ X17)
% 0.64/0.82          | ((k2_relat_1 @ X18) = (X17))
% 0.64/0.82          | ~ (v5_relat_1 @ X18 @ X17)
% 0.64/0.82          | ~ (v1_relat_1 @ X18))),
% 0.64/0.82      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.64/0.82  thf('130', plain,
% 0.64/0.82      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.64/0.82        | ~ (v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)
% 0.64/0.82        | ((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A)))),
% 0.64/0.82      inference('sup-', [status(thm)], ['128', '129'])).
% 0.64/0.82  thf('131', plain,
% 0.64/0.82      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.64/0.82        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.82      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.64/0.82  thf('132', plain,
% 0.64/0.82      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.64/0.82         ((v1_relat_1 @ X4)
% 0.64/0.82          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.64/0.82      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.64/0.82  thf('133', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.64/0.82      inference('sup-', [status(thm)], ['131', '132'])).
% 0.64/0.82  thf('134', plain,
% 0.64/0.82      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.64/0.82        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.82      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.64/0.82  thf(cc2_relset_1, axiom,
% 0.64/0.82    (![A:$i,B:$i,C:$i]:
% 0.64/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.64/0.82       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.64/0.82  thf('135', plain,
% 0.64/0.82      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.64/0.82         ((v5_relat_1 @ X7 @ X9)
% 0.64/0.82          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.64/0.82      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.64/0.82  thf('136', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)),
% 0.64/0.82      inference('sup-', [status(thm)], ['134', '135'])).
% 0.64/0.82  thf('137', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_B)) = (sk_A))),
% 0.64/0.82      inference('demod', [status(thm)], ['130', '133', '136'])).
% 0.64/0.82  thf('138', plain,
% 0.64/0.82      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 0.64/0.82        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.82      inference('demod', [status(thm)], ['57', '64'])).
% 0.64/0.82  thf('139', plain,
% 0.64/0.82      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.64/0.82         ((v1_relat_1 @ X4)
% 0.64/0.82          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.64/0.82      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.64/0.82  thf('140', plain, ((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.64/0.82      inference('sup-', [status(thm)], ['138', '139'])).
% 0.64/0.82  thf('141', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.64/0.82      inference('demod', [status(thm)], ['74', '75'])).
% 0.64/0.82  thf('142', plain,
% 0.64/0.82      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 0.64/0.82        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.82      inference('demod', [status(thm)], ['57', '64'])).
% 0.64/0.82  thf('143', plain,
% 0.64/0.82      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.64/0.82         (~ (v1_funct_1 @ X14)
% 0.64/0.82          | ~ (v3_funct_2 @ X14 @ X15 @ X16)
% 0.64/0.82          | (v2_funct_1 @ X14)
% 0.64/0.82          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.64/0.82      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.64/0.82  thf('144', plain,
% 0.64/0.82      (((v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.64/0.82        | ~ (v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)
% 0.64/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.64/0.82      inference('sup-', [status(thm)], ['142', '143'])).
% 0.64/0.82  thf('145', plain,
% 0.64/0.82      ((v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 0.64/0.82      inference('demod', [status(thm)], ['92', '93'])).
% 0.64/0.82  thf('146', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.64/0.82      inference('demod', [status(thm)], ['74', '75'])).
% 0.64/0.82  thf('147', plain, ((v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.64/0.82      inference('demod', [status(thm)], ['144', '145', '146'])).
% 0.64/0.82  thf('148', plain,
% 0.64/0.82      (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ (k2_funct_1 @ sk_B))
% 0.64/0.82         = (k6_relat_1 @ sk_A))),
% 0.64/0.82      inference('demod', [status(thm)],
% 0.64/0.82                ['121', '122', '137', '140', '141', '147'])).
% 0.64/0.82  thf('149', plain,
% 0.64/0.82      ((((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) = (k6_relat_1 @ sk_A))
% 0.64/0.82        | ~ (v1_relat_1 @ sk_B)
% 0.64/0.82        | ~ (v1_funct_1 @ sk_B)
% 0.64/0.82        | ~ (v2_funct_1 @ sk_B))),
% 0.64/0.82      inference('sup+', [status(thm)], ['35', '148'])).
% 0.64/0.82  thf('150', plain, ((v1_relat_1 @ sk_B)),
% 0.64/0.82      inference('sup-', [status(thm)], ['98', '99'])).
% 0.64/0.82  thf('151', plain, ((v1_funct_1 @ sk_B)),
% 0.64/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.82  thf('152', plain, ((v2_funct_1 @ sk_B)),
% 0.64/0.82      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.64/0.82  thf('153', plain,
% 0.64/0.82      (((k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) = (k6_relat_1 @ sk_A))),
% 0.64/0.82      inference('demod', [status(thm)], ['149', '150', '151', '152'])).
% 0.64/0.82  thf('154', plain,
% 0.64/0.82      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 0.64/0.82         = (k6_relat_1 @ sk_A))),
% 0.64/0.82      inference('demod', [status(thm)], ['25', '34', '153'])).
% 0.64/0.82  thf('155', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.64/0.82      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.64/0.82  thf('156', plain,
% 0.64/0.82      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.82           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.64/0.82            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.64/0.82           (k6_partfun1 @ sk_A)))
% 0.64/0.82         <= (~
% 0.64/0.82             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.82               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.64/0.82                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.64/0.82               (k6_partfun1 @ sk_A))))),
% 0.64/0.82      inference('split', [status(esa)], ['0'])).
% 0.64/0.82  thf('157', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.64/0.82      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.64/0.82  thf('158', plain,
% 0.64/0.82      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.82           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.64/0.82            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.64/0.82           (k6_relat_1 @ sk_A)))
% 0.64/0.82         <= (~
% 0.64/0.82             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.82               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.64/0.82                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.64/0.82               (k6_partfun1 @ sk_A))))),
% 0.64/0.82      inference('demod', [status(thm)], ['156', '157'])).
% 0.64/0.82  thf('159', plain,
% 0.64/0.82      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.82           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.64/0.82            (k2_funct_1 @ sk_B)) @ 
% 0.64/0.82           (k6_relat_1 @ sk_A)))
% 0.64/0.82         <= (~
% 0.64/0.82             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.82               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.64/0.82                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.64/0.82               (k6_partfun1 @ sk_A))))),
% 0.64/0.82      inference('sup-', [status(thm)], ['155', '158'])).
% 0.64/0.82  thf('160', plain,
% 0.64/0.82      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 0.64/0.82           (k6_relat_1 @ sk_A)))
% 0.64/0.82         <= (~
% 0.64/0.82             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.82               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.64/0.82                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.64/0.82               (k6_partfun1 @ sk_A))))),
% 0.64/0.82      inference('sup-', [status(thm)], ['154', '159'])).
% 0.64/0.82  thf(dt_k6_partfun1, axiom,
% 0.64/0.82    (![A:$i]:
% 0.64/0.82     ( ( m1_subset_1 @
% 0.64/0.82         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.64/0.82       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.64/0.82  thf('161', plain,
% 0.64/0.82      (![X22 : $i]:
% 0.64/0.82         (m1_subset_1 @ (k6_partfun1 @ X22) @ 
% 0.64/0.82          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 0.64/0.82      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.64/0.82  thf('162', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.64/0.82      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.64/0.82  thf('163', plain,
% 0.64/0.82      (![X22 : $i]:
% 0.64/0.82         (m1_subset_1 @ (k6_relat_1 @ X22) @ 
% 0.64/0.82          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 0.64/0.82      inference('demod', [status(thm)], ['161', '162'])).
% 0.64/0.82  thf(reflexivity_r2_relset_1, axiom,
% 0.64/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.64/0.82     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.64/0.82         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.64/0.82       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.64/0.82  thf('164', plain,
% 0.64/0.82      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.64/0.82         ((r2_relset_1 @ X10 @ X11 @ X12 @ X12)
% 0.64/0.82          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.64/0.82          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.64/0.82      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.64/0.82  thf('165', plain,
% 0.64/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.82         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.64/0.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.64/0.82      inference('condensation', [status(thm)], ['164'])).
% 0.64/0.82  thf('166', plain,
% 0.64/0.82      (![X0 : $i]:
% 0.64/0.82         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.64/0.82      inference('sup-', [status(thm)], ['163', '165'])).
% 0.64/0.82  thf('167', plain,
% 0.64/0.82      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.82         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.64/0.82          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.64/0.82         (k6_partfun1 @ sk_A)))),
% 0.64/0.82      inference('demod', [status(thm)], ['160', '166'])).
% 0.64/0.82  thf('168', plain,
% 0.64/0.82      (~
% 0.64/0.82       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.82         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.64/0.82          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.64/0.82         (k6_partfun1 @ sk_A))) | 
% 0.64/0.82       ~
% 0.64/0.82       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.82         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.64/0.82          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.64/0.82         (k6_partfun1 @ sk_A)))),
% 0.64/0.82      inference('split', [status(esa)], ['0'])).
% 0.64/0.82  thf('169', plain,
% 0.64/0.82      (~
% 0.64/0.82       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.82         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.64/0.82          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.64/0.82         (k6_partfun1 @ sk_A)))),
% 0.64/0.82      inference('sat_resolution*', [status(thm)], ['167', '168'])).
% 0.64/0.82  thf('170', plain,
% 0.64/0.82      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.64/0.82          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.64/0.82          (k6_relat_1 @ sk_A))),
% 0.64/0.82      inference('simpl_trail', [status(thm)], ['11', '169'])).
% 0.64/0.82  thf('171', plain,
% 0.64/0.82      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.82  thf('172', plain,
% 0.64/0.82      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.64/0.82        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.82      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.64/0.82  thf('173', plain,
% 0.64/0.82      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.64/0.82         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.64/0.82          | ~ (v1_funct_1 @ X23)
% 0.64/0.82          | ~ (v1_funct_1 @ X26)
% 0.64/0.82          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.64/0.82          | ((k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26)
% 0.64/0.82              = (k5_relat_1 @ X23 @ X26)))),
% 0.64/0.82      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.64/0.82  thf('174', plain,
% 0.64/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.82         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.64/0.82            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.64/0.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.64/0.82          | ~ (v1_funct_1 @ X0)
% 0.64/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.64/0.82      inference('sup-', [status(thm)], ['172', '173'])).
% 0.64/0.82  thf('175', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.64/0.82      inference('demod', [status(thm)], ['32', '33'])).
% 0.64/0.82  thf('176', plain,
% 0.64/0.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.82         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.64/0.82            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.64/0.82          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.64/0.82          | ~ (v1_funct_1 @ X0))),
% 0.64/0.82      inference('demod', [status(thm)], ['174', '175'])).
% 0.64/0.82  thf('177', plain,
% 0.64/0.82      ((~ (v1_funct_1 @ sk_B)
% 0.64/0.82        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.64/0.82            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 0.64/0.82      inference('sup-', [status(thm)], ['171', '176'])).
% 0.64/0.82  thf('178', plain, ((v1_funct_1 @ sk_B)),
% 0.64/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.82  thf('179', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.64/0.82      inference('sup-', [status(thm)], ['131', '132'])).
% 0.64/0.82  thf('180', plain,
% 0.64/0.82      (![X3 : $i]:
% 0.64/0.82         (~ (v2_funct_1 @ X3)
% 0.64/0.82          | ((k2_funct_1 @ (k2_funct_1 @ X3)) = (X3))
% 0.64/0.82          | ~ (v1_funct_1 @ X3)
% 0.64/0.82          | ~ (v1_relat_1 @ X3))),
% 0.64/0.82      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.64/0.82  thf('181', plain,
% 0.64/0.82      (![X1 : $i]:
% 0.64/0.82         (~ (v2_funct_1 @ X1)
% 0.64/0.82          | ((k5_relat_1 @ X1 @ (k2_funct_1 @ X1))
% 0.64/0.82              = (k6_relat_1 @ (k1_relat_1 @ X1)))
% 0.64/0.82          | ~ (v1_funct_1 @ X1)
% 0.64/0.82          | ~ (v1_relat_1 @ X1))),
% 0.64/0.82      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.64/0.82  thf('182', plain,
% 0.64/0.82      (![X0 : $i]:
% 0.64/0.82         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.64/0.82            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.64/0.82          | ~ (v1_relat_1 @ X0)
% 0.64/0.82          | ~ (v1_funct_1 @ X0)
% 0.64/0.82          | ~ (v2_funct_1 @ X0)
% 0.64/0.82          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.64/0.82          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.64/0.82          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.64/0.82      inference('sup+', [status(thm)], ['180', '181'])).
% 0.64/0.82  thf('183', plain,
% 0.64/0.82      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_B))
% 0.64/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.64/0.82        | ~ (v2_funct_1 @ sk_B)
% 0.64/0.82        | ~ (v1_funct_1 @ sk_B)
% 0.64/0.82        | ~ (v1_relat_1 @ sk_B)
% 0.64/0.82        | ((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.64/0.82            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_B)))))),
% 0.64/0.82      inference('sup-', [status(thm)], ['179', '182'])).
% 0.64/0.82  thf('184', plain,
% 0.64/0.82      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.64/0.82        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.82      inference('demod', [status(thm)], ['14', '15', '16', '17', '18'])).
% 0.64/0.82  thf('185', plain,
% 0.64/0.82      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.64/0.82         (~ (v1_funct_1 @ X14)
% 0.64/0.82          | ~ (v3_funct_2 @ X14 @ X15 @ X16)
% 0.64/0.82          | (v2_funct_1 @ X14)
% 0.64/0.82          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.64/0.82      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.64/0.82  thf('186', plain,
% 0.64/0.82      (((v2_funct_1 @ (k2_funct_1 @ sk_B))
% 0.64/0.82        | ~ (v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)
% 0.64/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.64/0.82      inference('sup-', [status(thm)], ['184', '185'])).
% 0.64/0.82  thf('187', plain, ((v3_funct_2 @ (k2_funct_1 @ sk_B) @ sk_A @ sk_A)),
% 0.64/0.82      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 0.64/0.82  thf('188', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.64/0.82      inference('demod', [status(thm)], ['32', '33'])).
% 0.64/0.82  thf('189', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.64/0.82      inference('demod', [status(thm)], ['186', '187', '188'])).
% 0.64/0.82  thf('190', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.64/0.82      inference('demod', [status(thm)], ['32', '33'])).
% 0.64/0.82  thf('191', plain, ((v2_funct_1 @ sk_B)),
% 0.64/0.82      inference('demod', [status(thm)], ['104', '105', '106'])).
% 0.64/0.82  thf('192', plain, ((v1_funct_1 @ sk_B)),
% 0.64/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.82  thf('193', plain, ((v1_relat_1 @ sk_B)),
% 0.64/0.82      inference('sup-', [status(thm)], ['98', '99'])).
% 0.64/0.82  thf('194', plain,
% 0.64/0.82      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 0.64/0.82        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.82      inference('demod', [status(thm)], ['57', '64'])).
% 0.64/0.82  thf('195', plain,
% 0.64/0.82      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.64/0.82         (~ (v1_funct_1 @ X14)
% 0.64/0.82          | ~ (v3_funct_2 @ X14 @ X15 @ X16)
% 0.64/0.82          | (v2_funct_2 @ X14 @ X16)
% 0.64/0.82          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.64/0.82      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.64/0.82  thf('196', plain,
% 0.64/0.82      (((v2_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A)
% 0.64/0.82        | ~ (v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)
% 0.64/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))))),
% 0.64/0.82      inference('sup-', [status(thm)], ['194', '195'])).
% 0.64/0.82  thf('197', plain,
% 0.64/0.82      ((v3_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A @ sk_A)),
% 0.64/0.82      inference('demod', [status(thm)], ['92', '93'])).
% 0.64/0.82  thf('198', plain, ((v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.64/0.82      inference('demod', [status(thm)], ['74', '75'])).
% 0.64/0.82  thf('199', plain, ((v2_funct_2 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A)),
% 0.64/0.82      inference('demod', [status(thm)], ['196', '197', '198'])).
% 0.64/0.82  thf('200', plain,
% 0.64/0.82      (![X17 : $i, X18 : $i]:
% 0.64/0.82         (~ (v2_funct_2 @ X18 @ X17)
% 0.64/0.82          | ((k2_relat_1 @ X18) = (X17))
% 0.64/0.82          | ~ (v5_relat_1 @ X18 @ X17)
% 0.64/0.82          | ~ (v1_relat_1 @ X18))),
% 0.64/0.82      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.64/0.82  thf('201', plain,
% 0.64/0.82      ((~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))
% 0.64/0.82        | ~ (v5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A)
% 0.64/0.82        | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))) = (sk_A)))),
% 0.64/0.82      inference('sup-', [status(thm)], ['199', '200'])).
% 0.64/0.82  thf('202', plain, ((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.64/0.82      inference('sup-', [status(thm)], ['138', '139'])).
% 0.64/0.82  thf('203', plain,
% 0.64/0.82      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ 
% 0.64/0.82        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.64/0.82      inference('demod', [status(thm)], ['57', '64'])).
% 0.64/0.82  thf('204', plain,
% 0.64/0.82      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.64/0.82         ((v5_relat_1 @ X7 @ X9)
% 0.64/0.82          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.64/0.82      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.64/0.82  thf('205', plain, ((v5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B)) @ sk_A)),
% 0.64/0.82      inference('sup-', [status(thm)], ['203', '204'])).
% 0.64/0.82  thf('206', plain,
% 0.64/0.82      (((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_B))) = (sk_A))),
% 0.64/0.82      inference('demod', [status(thm)], ['201', '202', '205'])).
% 0.64/0.82  thf('207', plain,
% 0.64/0.82      (![X1 : $i]:
% 0.64/0.82         (~ (v2_funct_1 @ X1)
% 0.64/0.82          | ((k5_relat_1 @ X1 @ (k2_funct_1 @ X1))
% 0.64/0.82              = (k6_relat_1 @ (k1_relat_1 @ X1)))
% 0.64/0.82          | ~ (v1_funct_1 @ X1)
% 0.64/0.82          | ~ (v1_relat_1 @ X1))),
% 0.64/0.82      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.64/0.82  thf('208', plain,
% 0.64/0.82      (![X0 : $i]:
% 0.64/0.82         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.64/0.82            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.64/0.82          | ~ (v2_funct_1 @ X0)
% 0.64/0.82          | ~ (v1_funct_1 @ X0)
% 0.64/0.82          | ~ (v1_relat_1 @ X0))),
% 0.64/0.82      inference('simplify', [status(thm)], ['119'])).
% 0.64/0.82  thf('209', plain,
% 0.64/0.82      (![X0 : $i]:
% 0.64/0.82         (((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.64/0.82            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.64/0.82          | ~ (v1_relat_1 @ X0)
% 0.64/0.82          | ~ (v1_funct_1 @ X0)
% 0.64/0.82          | ~ (v2_funct_1 @ X0)
% 0.64/0.82          | ~ (v1_relat_1 @ X0)
% 0.64/0.82          | ~ (v1_funct_1 @ X0)
% 0.64/0.82          | ~ (v2_funct_1 @ X0))),
% 0.64/0.82      inference('sup+', [status(thm)], ['207', '208'])).
% 0.64/0.82  thf('210', plain,
% 0.64/0.82      (![X0 : $i]:
% 0.64/0.82         (~ (v2_funct_1 @ X0)
% 0.64/0.82          | ~ (v1_funct_1 @ X0)
% 0.64/0.82          | ~ (v1_relat_1 @ X0)
% 0.64/0.82          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.64/0.82              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.64/0.82      inference('simplify', [status(thm)], ['209'])).
% 0.64/0.82  thf('211', plain,
% 0.64/0.82      ((((k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_B)))
% 0.64/0.82          = (k6_relat_1 @ sk_A))
% 0.64/0.82        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.64/0.82        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.64/0.82        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.64/0.82      inference('sup+', [status(thm)], ['206', '210'])).
% 0.64/0.82  thf('212', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 0.64/0.82      inference('sup-', [status(thm)], ['131', '132'])).
% 0.64/0.82  thf('213', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.64/0.82      inference('demod', [status(thm)], ['32', '33'])).
% 0.64/0.82  thf('214', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.64/0.82      inference('demod', [status(thm)], ['186', '187', '188'])).
% 0.64/0.82  thf('215', plain,
% 0.64/0.82      (((k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_B))) = (k6_relat_1 @ sk_A))),
% 0.64/0.82      inference('demod', [status(thm)], ['211', '212', '213', '214'])).
% 0.64/0.82  thf('216', plain,
% 0.64/0.82      (((k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) = (k6_relat_1 @ sk_A))),
% 0.64/0.82      inference('demod', [status(thm)],
% 0.64/0.82                ['183', '189', '190', '191', '192', '193', '215'])).
% 0.64/0.82  thf('217', plain,
% 0.64/0.82      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.64/0.82         = (k6_relat_1 @ sk_A))),
% 0.64/0.82      inference('demod', [status(thm)], ['177', '178', '216'])).
% 0.64/0.82  thf('218', plain,
% 0.64/0.82      (![X0 : $i]:
% 0.64/0.82         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.64/0.82      inference('sup-', [status(thm)], ['163', '165'])).
% 0.64/0.82  thf('219', plain, ($false),
% 0.64/0.82      inference('demod', [status(thm)], ['170', '217', '218'])).
% 0.64/0.82  
% 0.64/0.82  % SZS output end Refutation
% 0.64/0.82  
% 0.64/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
