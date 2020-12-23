%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XlTiVCy1Ry

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:15 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 438 expanded)
%              Number of leaves         :   38 ( 148 expanded)
%              Depth                    :   13
%              Number of atoms          : 1531 (9859 expanded)
%              Number of equality atoms :   43 (  73 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

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
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
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
    ! [X31: $i,X32: $i] :
      ( ( ( k2_funct_2 @ X32 @ X31 )
        = ( k2_funct_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) )
      | ~ ( v3_funct_2 @ X31 @ X32 @ X32 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X32 )
      | ~ ( v1_funct_1 @ X31 ) ) ),
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
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k2_funct_2 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 )
        = ( k5_relat_1 @ X25 @ X28 ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( v1_funct_1 @ ( k2_funct_2 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v3_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_2 @ X20 @ X19 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
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
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
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
    ! [X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X34 @ X35 )
        = X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X34 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( ( k1_relset_1 @ X8 @ X9 @ X7 )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
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
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('55',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('56',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('57',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_relset_1 @ X10 @ X11 @ X12 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('61',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
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

thf('65',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v3_funct_2 @ X14 @ X15 @ X16 )
      | ( v2_funct_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('66',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['44','53','59','62','63','69'])).

thf('71',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ ( k2_funct_2 @ sk_A @ sk_B ) ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('72',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_2 @ sk_A @ sk_B ) @ sk_B ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['11','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16','17','18'])).

thf('76',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 )
        = ( k5_relat_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ ( k2_funct_2 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['30','31','32','33'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_2 @ sk_A @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('81',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ ( k2_funct_1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['74','82'])).

thf('84',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k2_funct_1 @ sk_B ) @ sk_B )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v3_funct_2 @ X14 @ X15 @ X16 )
      | ( v2_funct_2 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( v2_funct_2 @ X18 @ X17 )
      | ( ( k2_relat_1 @ X18 )
        = X17 )
      | ~ ( v5_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('94',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['60','61'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('97',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v5_relat_1 @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('98',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['94','95','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('101',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
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
    inference(demod,[status(thm)],['66','67','68'])).

thf('106',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['60','61'])).

thf('108',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['57'])).

thf('110',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ ( k2_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['86','110'])).

thf('112',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['94','95','98'])).

thf('113',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['60','61'])).

thf('114',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('116',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_B ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['111','112','113','114','115'])).

thf('117',plain,(
    $false ),
    inference(demod,[status(thm)],['73','85','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XlTiVCy1Ry
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:41:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.74/0.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.74/0.93  % Solved by: fo/fo7.sh
% 0.74/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.93  % done 639 iterations in 0.474s
% 0.74/0.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.74/0.93  % SZS output start Refutation
% 0.74/0.93  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.74/0.93  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.74/0.93  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.74/0.93  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.74/0.93  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.74/0.93  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.74/0.93  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.74/0.93  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.74/0.93  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.74/0.93  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.74/0.93  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.74/0.93  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.74/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.93  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.74/0.93  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.74/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.74/0.93  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 0.74/0.93  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.74/0.93  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 0.74/0.93  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.74/0.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.74/0.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.74/0.93  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.74/0.93  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.74/0.93  thf(t88_funct_2, conjecture,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.74/0.93         ( v3_funct_2 @ B @ A @ A ) & 
% 0.74/0.93         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.74/0.93       ( ( r2_relset_1 @
% 0.74/0.93           A @ A @ 
% 0.74/0.93           ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.74/0.93           ( k6_partfun1 @ A ) ) & 
% 0.74/0.93         ( r2_relset_1 @
% 0.74/0.93           A @ A @ 
% 0.74/0.93           ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.74/0.93           ( k6_partfun1 @ A ) ) ) ))).
% 0.74/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.93    (~( ![A:$i,B:$i]:
% 0.74/0.93        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.74/0.93            ( v3_funct_2 @ B @ A @ A ) & 
% 0.74/0.93            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.74/0.93          ( ( r2_relset_1 @
% 0.74/0.93              A @ A @ 
% 0.74/0.93              ( k1_partfun1 @ A @ A @ A @ A @ B @ ( k2_funct_2 @ A @ B ) ) @ 
% 0.74/0.93              ( k6_partfun1 @ A ) ) & 
% 0.74/0.93            ( r2_relset_1 @
% 0.74/0.93              A @ A @ 
% 0.74/0.93              ( k1_partfun1 @ A @ A @ A @ A @ ( k2_funct_2 @ A @ B ) @ B ) @ 
% 0.74/0.93              ( k6_partfun1 @ A ) ) ) ) )),
% 0.74/0.93    inference('cnf.neg', [status(esa)], [t88_funct_2])).
% 0.74/0.93  thf('0', plain,
% 0.74/0.93      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.93           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.74/0.93            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.74/0.93           (k6_partfun1 @ sk_A))
% 0.74/0.93        | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.93             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.74/0.93              (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.74/0.93             (k6_partfun1 @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('1', plain,
% 0.74/0.93      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.93           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.74/0.93            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.74/0.93           (k6_partfun1 @ sk_A)))
% 0.74/0.93         <= (~
% 0.74/0.93             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.93               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.74/0.93                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.74/0.93               (k6_partfun1 @ sk_A))))),
% 0.74/0.93      inference('split', [status(esa)], ['0'])).
% 0.74/0.93  thf(redefinition_k6_partfun1, axiom,
% 0.74/0.93    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.74/0.93  thf('2', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.74/0.93      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.74/0.93  thf('3', plain,
% 0.74/0.93      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.93           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.74/0.93            (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.74/0.93           (k6_relat_1 @ sk_A)))
% 0.74/0.93         <= (~
% 0.74/0.93             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.93               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.74/0.93                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.74/0.93               (k6_partfun1 @ sk_A))))),
% 0.74/0.93      inference('demod', [status(thm)], ['1', '2'])).
% 0.74/0.93  thf('4', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(redefinition_k2_funct_2, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.74/0.93         ( v3_funct_2 @ B @ A @ A ) & 
% 0.74/0.93         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.74/0.93       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 0.74/0.93  thf('5', plain,
% 0.74/0.93      (![X31 : $i, X32 : $i]:
% 0.74/0.93         (((k2_funct_2 @ X32 @ X31) = (k2_funct_1 @ X31))
% 0.74/0.93          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X32)))
% 0.74/0.93          | ~ (v3_funct_2 @ X31 @ X32 @ X32)
% 0.74/0.93          | ~ (v1_funct_2 @ X31 @ X32 @ X32)
% 0.74/0.93          | ~ (v1_funct_1 @ X31))),
% 0.74/0.93      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 0.74/0.93  thf('6', plain,
% 0.74/0.93      ((~ (v1_funct_1 @ sk_B)
% 0.74/0.93        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.74/0.93        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.74/0.93        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['4', '5'])).
% 0.74/0.93  thf('7', plain, ((v1_funct_1 @ sk_B)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('8', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('9', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('10', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.74/0.93      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.74/0.93  thf('11', plain,
% 0.74/0.93      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.93           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.74/0.93            sk_B) @ 
% 0.74/0.93           (k6_relat_1 @ sk_A)))
% 0.74/0.93         <= (~
% 0.74/0.93             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.93               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.74/0.93                (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.74/0.93               (k6_partfun1 @ sk_A))))),
% 0.74/0.93      inference('demod', [status(thm)], ['3', '10'])).
% 0.74/0.93  thf(t61_funct_1, axiom,
% 0.74/0.93    (![A:$i]:
% 0.74/0.93     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.74/0.93       ( ( v2_funct_1 @ A ) =>
% 0.74/0.93         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.74/0.93             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.74/0.93           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.74/0.93             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.74/0.93  thf('12', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         (~ (v2_funct_1 @ X0)
% 0.74/0.93          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.74/0.93              = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.74/0.93          | ~ (v1_funct_1 @ X0)
% 0.74/0.93          | ~ (v1_relat_1 @ X0))),
% 0.74/0.93      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.74/0.93  thf('13', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(dt_k2_funct_2, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.74/0.93         ( v3_funct_2 @ B @ A @ A ) & 
% 0.74/0.93         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.74/0.93       ( ( v1_funct_1 @ ( k2_funct_2 @ A @ B ) ) & 
% 0.74/0.93         ( v1_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.74/0.93         ( v3_funct_2 @ ( k2_funct_2 @ A @ B ) @ A @ A ) & 
% 0.74/0.93         ( m1_subset_1 @
% 0.74/0.93           ( k2_funct_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) ))).
% 0.74/0.93  thf('14', plain,
% 0.74/0.93      (![X19 : $i, X20 : $i]:
% 0.74/0.93         ((m1_subset_1 @ (k2_funct_2 @ X19 @ X20) @ 
% 0.74/0.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.74/0.93          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.74/0.93          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 0.74/0.93          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 0.74/0.93          | ~ (v1_funct_1 @ X20))),
% 0.74/0.93      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.74/0.93  thf('15', plain,
% 0.74/0.93      ((~ (v1_funct_1 @ sk_B)
% 0.74/0.93        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.74/0.93        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.74/0.93        | (m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.74/0.93           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['13', '14'])).
% 0.74/0.93  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('17', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('18', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('19', plain,
% 0.74/0.93      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.74/0.93        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.74/0.93      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.74/0.93  thf('20', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.74/0.93      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.74/0.93  thf('21', plain,
% 0.74/0.93      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 0.74/0.93        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.74/0.93      inference('demod', [status(thm)], ['19', '20'])).
% 0.74/0.93  thf('22', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(redefinition_k1_partfun1, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.74/0.93     ( ( ( v1_funct_1 @ E ) & 
% 0.74/0.93         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.74/0.93         ( v1_funct_1 @ F ) & 
% 0.74/0.93         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.74/0.93       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.74/0.93  thf('23', plain,
% 0.74/0.93      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.74/0.93         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.74/0.93          | ~ (v1_funct_1 @ X25)
% 0.74/0.93          | ~ (v1_funct_1 @ X28)
% 0.74/0.93          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.74/0.93          | ((k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28)
% 0.74/0.93              = (k5_relat_1 @ X25 @ X28)))),
% 0.74/0.93      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.74/0.93  thf('24', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.93         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.74/0.93            = (k5_relat_1 @ sk_B @ X0))
% 0.74/0.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.74/0.93          | ~ (v1_funct_1 @ X0)
% 0.74/0.93          | ~ (v1_funct_1 @ sk_B))),
% 0.74/0.93      inference('sup-', [status(thm)], ['22', '23'])).
% 0.74/0.93  thf('25', plain, ((v1_funct_1 @ sk_B)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('26', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.93         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_B @ X0)
% 0.74/0.93            = (k5_relat_1 @ sk_B @ X0))
% 0.74/0.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.74/0.93          | ~ (v1_funct_1 @ X0))),
% 0.74/0.93      inference('demod', [status(thm)], ['24', '25'])).
% 0.74/0.93  thf('27', plain,
% 0.74/0.93      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.74/0.93        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.74/0.93            (k2_funct_1 @ sk_B)) = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['21', '26'])).
% 0.74/0.93  thf('28', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('29', plain,
% 0.74/0.93      (![X19 : $i, X20 : $i]:
% 0.74/0.93         ((v1_funct_1 @ (k2_funct_2 @ X19 @ X20))
% 0.74/0.93          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X19)))
% 0.74/0.93          | ~ (v3_funct_2 @ X20 @ X19 @ X19)
% 0.74/0.93          | ~ (v1_funct_2 @ X20 @ X19 @ X19)
% 0.74/0.93          | ~ (v1_funct_1 @ X20))),
% 0.74/0.93      inference('cnf', [status(esa)], [dt_k2_funct_2])).
% 0.74/0.93  thf('30', plain,
% 0.74/0.93      ((~ (v1_funct_1 @ sk_B)
% 0.74/0.93        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.74/0.93        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.74/0.93        | (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['28', '29'])).
% 0.74/0.93  thf('31', plain, ((v1_funct_1 @ sk_B)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('32', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('33', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('34', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.74/0.93      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.74/0.93  thf('35', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.74/0.93      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.74/0.93  thf('36', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 0.74/0.93      inference('demod', [status(thm)], ['34', '35'])).
% 0.74/0.93  thf('37', plain,
% 0.74/0.93      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ (k2_funct_1 @ sk_B))
% 0.74/0.93         = (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)))),
% 0.74/0.93      inference('demod', [status(thm)], ['27', '36'])).
% 0.74/0.93  thf('38', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.74/0.93      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.74/0.93  thf('39', plain,
% 0.74/0.93      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.93           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.74/0.93            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.74/0.93           (k6_partfun1 @ sk_A)))
% 0.74/0.93         <= (~
% 0.74/0.93             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.93               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.74/0.93                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.74/0.93               (k6_partfun1 @ sk_A))))),
% 0.74/0.93      inference('split', [status(esa)], ['0'])).
% 0.74/0.93  thf('40', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.74/0.93      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.74/0.93  thf('41', plain,
% 0.74/0.93      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.93           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.74/0.93            (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.74/0.93           (k6_relat_1 @ sk_A)))
% 0.74/0.93         <= (~
% 0.74/0.93             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.93               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.74/0.93                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.74/0.93               (k6_partfun1 @ sk_A))))),
% 0.74/0.93      inference('demod', [status(thm)], ['39', '40'])).
% 0.74/0.93  thf('42', plain,
% 0.74/0.93      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.93           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.74/0.93            (k2_funct_1 @ sk_B)) @ 
% 0.74/0.93           (k6_relat_1 @ sk_A)))
% 0.74/0.93         <= (~
% 0.74/0.93             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.93               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.74/0.93                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.74/0.93               (k6_partfun1 @ sk_A))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['38', '41'])).
% 0.74/0.93  thf('43', plain,
% 0.74/0.93      ((~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.93           (k5_relat_1 @ sk_B @ (k2_funct_1 @ sk_B)) @ (k6_relat_1 @ sk_A)))
% 0.74/0.93         <= (~
% 0.74/0.93             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.93               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.74/0.93                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.74/0.93               (k6_partfun1 @ sk_A))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['37', '42'])).
% 0.74/0.93  thf('44', plain,
% 0.74/0.93      (((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ (k1_relat_1 @ sk_B)) @ 
% 0.74/0.93            (k6_relat_1 @ sk_A))
% 0.74/0.93         | ~ (v1_relat_1 @ sk_B)
% 0.74/0.93         | ~ (v1_funct_1 @ sk_B)
% 0.74/0.93         | ~ (v2_funct_1 @ sk_B)))
% 0.74/0.93         <= (~
% 0.74/0.93             ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.93               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.74/0.93                (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.74/0.93               (k6_partfun1 @ sk_A))))),
% 0.74/0.93      inference('sup-', [status(thm)], ['12', '43'])).
% 0.74/0.93  thf('45', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(t67_funct_2, axiom,
% 0.74/0.93    (![A:$i,B:$i]:
% 0.74/0.93     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.74/0.93         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.74/0.93       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.74/0.93  thf('46', plain,
% 0.74/0.93      (![X34 : $i, X35 : $i]:
% 0.74/0.93         (((k1_relset_1 @ X34 @ X34 @ X35) = (X34))
% 0.74/0.93          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X34)))
% 0.74/0.93          | ~ (v1_funct_2 @ X35 @ X34 @ X34)
% 0.74/0.93          | ~ (v1_funct_1 @ X35))),
% 0.74/0.93      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.74/0.93  thf('47', plain,
% 0.74/0.93      ((~ (v1_funct_1 @ sk_B)
% 0.74/0.93        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.74/0.93        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 0.74/0.93      inference('sup-', [status(thm)], ['45', '46'])).
% 0.74/0.93  thf('48', plain, ((v1_funct_1 @ sk_B)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('49', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('50', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(redefinition_k1_relset_1, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i]:
% 0.74/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.93       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.74/0.93  thf('51', plain,
% 0.74/0.93      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.74/0.93         (((k1_relset_1 @ X8 @ X9 @ X7) = (k1_relat_1 @ X7))
% 0.74/0.93          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.74/0.93      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.74/0.93  thf('52', plain,
% 0.74/0.93      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.74/0.93      inference('sup-', [status(thm)], ['50', '51'])).
% 0.74/0.93  thf('53', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.74/0.93      inference('demod', [status(thm)], ['47', '48', '49', '52'])).
% 0.74/0.93  thf(dt_k6_partfun1, axiom,
% 0.74/0.93    (![A:$i]:
% 0.74/0.93     ( ( m1_subset_1 @
% 0.74/0.93         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.74/0.93       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.74/0.93  thf('54', plain,
% 0.74/0.93      (![X22 : $i]:
% 0.74/0.93         (m1_subset_1 @ (k6_partfun1 @ X22) @ 
% 0.74/0.93          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 0.74/0.93      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.74/0.93  thf('55', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.74/0.93      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.74/0.93  thf('56', plain,
% 0.74/0.93      (![X22 : $i]:
% 0.74/0.93         (m1_subset_1 @ (k6_relat_1 @ X22) @ 
% 0.74/0.93          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 0.74/0.93      inference('demod', [status(thm)], ['54', '55'])).
% 0.74/0.93  thf(reflexivity_r2_relset_1, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/0.93     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.74/0.93         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.74/0.93       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.74/0.93  thf('57', plain,
% 0.74/0.93      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.74/0.93         ((r2_relset_1 @ X10 @ X11 @ X12 @ X12)
% 0.74/0.93          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11)))
% 0.74/0.93          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.74/0.93      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.74/0.93  thf('58', plain,
% 0.74/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.93         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.74/0.93          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.74/0.93      inference('condensation', [status(thm)], ['57'])).
% 0.74/0.93  thf('59', plain,
% 0.74/0.93      (![X0 : $i]:
% 0.74/0.93         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.74/0.93      inference('sup-', [status(thm)], ['56', '58'])).
% 0.74/0.93  thf('60', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(cc1_relset_1, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i]:
% 0.74/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.93       ( v1_relat_1 @ C ) ))).
% 0.74/0.93  thf('61', plain,
% 0.74/0.93      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.74/0.93         ((v1_relat_1 @ X1)
% 0.74/0.93          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X3))))),
% 0.74/0.93      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.74/0.93  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 0.74/0.93      inference('sup-', [status(thm)], ['60', '61'])).
% 0.74/0.93  thf('63', plain, ((v1_funct_1 @ sk_B)),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf('64', plain,
% 0.74/0.93      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.74/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.93  thf(cc2_funct_2, axiom,
% 0.74/0.93    (![A:$i,B:$i,C:$i]:
% 0.74/0.93     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.93       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 0.74/0.94         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 0.74/0.94  thf('65', plain,
% 0.74/0.94      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.74/0.94         (~ (v1_funct_1 @ X14)
% 0.74/0.94          | ~ (v3_funct_2 @ X14 @ X15 @ X16)
% 0.74/0.94          | (v2_funct_1 @ X14)
% 0.74/0.94          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.74/0.94      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.74/0.94  thf('66', plain,
% 0.74/0.94      (((v2_funct_1 @ sk_B)
% 0.74/0.94        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.74/0.94        | ~ (v1_funct_1 @ sk_B))),
% 0.74/0.94      inference('sup-', [status(thm)], ['64', '65'])).
% 0.74/0.94  thf('67', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('68', plain, ((v1_funct_1 @ sk_B)),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('69', plain, ((v2_funct_1 @ sk_B)),
% 0.74/0.94      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.74/0.94  thf('70', plain,
% 0.74/0.94      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.94         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.74/0.94          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.74/0.94         (k6_partfun1 @ sk_A)))),
% 0.74/0.94      inference('demod', [status(thm)], ['44', '53', '59', '62', '63', '69'])).
% 0.74/0.94  thf('71', plain,
% 0.74/0.94      (~
% 0.74/0.94       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.94         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.74/0.94          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.74/0.94         (k6_partfun1 @ sk_A))) | 
% 0.74/0.94       ~
% 0.74/0.94       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.94         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.74/0.94          (k2_funct_2 @ sk_A @ sk_B)) @ 
% 0.74/0.94         (k6_partfun1 @ sk_A)))),
% 0.74/0.94      inference('split', [status(esa)], ['0'])).
% 0.74/0.94  thf('72', plain,
% 0.74/0.94      (~
% 0.74/0.94       ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.94         (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ 
% 0.74/0.94          (k2_funct_2 @ sk_A @ sk_B) @ sk_B) @ 
% 0.74/0.94         (k6_partfun1 @ sk_A)))),
% 0.74/0.94      inference('sat_resolution*', [status(thm)], ['70', '71'])).
% 0.74/0.94  thf('73', plain,
% 0.74/0.94      (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.94          (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.74/0.94          (k6_relat_1 @ sk_A))),
% 0.74/0.94      inference('simpl_trail', [status(thm)], ['11', '72'])).
% 0.74/0.94  thf('74', plain,
% 0.74/0.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('75', plain,
% 0.74/0.94      ((m1_subset_1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.74/0.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.74/0.94      inference('demod', [status(thm)], ['15', '16', '17', '18'])).
% 0.74/0.94  thf('76', plain,
% 0.74/0.94      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.74/0.94         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.74/0.94          | ~ (v1_funct_1 @ X25)
% 0.74/0.94          | ~ (v1_funct_1 @ X28)
% 0.74/0.94          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.74/0.94          | ((k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28)
% 0.74/0.94              = (k5_relat_1 @ X25 @ X28)))),
% 0.74/0.94      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.74/0.94  thf('77', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.94         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.74/0.94            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 0.74/0.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.74/0.94          | ~ (v1_funct_1 @ X0)
% 0.74/0.94          | ~ (v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B)))),
% 0.74/0.94      inference('sup-', [status(thm)], ['75', '76'])).
% 0.74/0.94  thf('78', plain, ((v1_funct_1 @ (k2_funct_2 @ sk_A @ sk_B))),
% 0.74/0.94      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 0.74/0.94  thf('79', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.94         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_2 @ sk_A @ sk_B) @ 
% 0.74/0.94            X0) = (k5_relat_1 @ (k2_funct_2 @ sk_A @ sk_B) @ X0))
% 0.74/0.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.74/0.94          | ~ (v1_funct_1 @ X0))),
% 0.74/0.94      inference('demod', [status(thm)], ['77', '78'])).
% 0.74/0.94  thf('80', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.74/0.94      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.74/0.94  thf('81', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 0.74/0.94      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.74/0.94  thf('82', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.94         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ (k2_funct_1 @ sk_B) @ X0)
% 0.74/0.94            = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ X0))
% 0.74/0.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.74/0.94          | ~ (v1_funct_1 @ X0))),
% 0.74/0.94      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.74/0.94  thf('83', plain,
% 0.74/0.94      ((~ (v1_funct_1 @ sk_B)
% 0.74/0.94        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ 
% 0.74/0.94            sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B)))),
% 0.74/0.94      inference('sup-', [status(thm)], ['74', '82'])).
% 0.74/0.94  thf('84', plain, ((v1_funct_1 @ sk_B)),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('85', plain,
% 0.74/0.94      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k2_funct_1 @ sk_B) @ sk_B)
% 0.74/0.94         = (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 0.74/0.94      inference('demod', [status(thm)], ['83', '84'])).
% 0.74/0.94  thf('86', plain,
% 0.74/0.94      (![X0 : $i]:
% 0.74/0.94         (~ (v2_funct_1 @ X0)
% 0.74/0.94          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.74/0.94              = (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.74/0.94          | ~ (v1_funct_1 @ X0)
% 0.74/0.94          | ~ (v1_relat_1 @ X0))),
% 0.74/0.94      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.74/0.94  thf('87', plain,
% 0.74/0.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('88', plain,
% 0.74/0.94      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.74/0.94         (~ (v1_funct_1 @ X14)
% 0.74/0.94          | ~ (v3_funct_2 @ X14 @ X15 @ X16)
% 0.74/0.94          | (v2_funct_2 @ X14 @ X16)
% 0.74/0.94          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.74/0.94      inference('cnf', [status(esa)], [cc2_funct_2])).
% 0.74/0.94  thf('89', plain,
% 0.74/0.94      (((v2_funct_2 @ sk_B @ sk_A)
% 0.74/0.94        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.74/0.94        | ~ (v1_funct_1 @ sk_B))),
% 0.74/0.94      inference('sup-', [status(thm)], ['87', '88'])).
% 0.74/0.94  thf('90', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('91', plain, ((v1_funct_1 @ sk_B)),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('92', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 0.74/0.94      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.74/0.94  thf(d3_funct_2, axiom,
% 0.74/0.94    (![A:$i,B:$i]:
% 0.74/0.94     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.74/0.94       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.74/0.94  thf('93', plain,
% 0.74/0.94      (![X17 : $i, X18 : $i]:
% 0.74/0.94         (~ (v2_funct_2 @ X18 @ X17)
% 0.74/0.94          | ((k2_relat_1 @ X18) = (X17))
% 0.74/0.94          | ~ (v5_relat_1 @ X18 @ X17)
% 0.74/0.94          | ~ (v1_relat_1 @ X18))),
% 0.74/0.94      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.74/0.94  thf('94', plain,
% 0.74/0.94      ((~ (v1_relat_1 @ sk_B)
% 0.74/0.94        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 0.74/0.94        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 0.74/0.94      inference('sup-', [status(thm)], ['92', '93'])).
% 0.74/0.94  thf('95', plain, ((v1_relat_1 @ sk_B)),
% 0.74/0.94      inference('sup-', [status(thm)], ['60', '61'])).
% 0.74/0.94  thf('96', plain,
% 0.74/0.94      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf(cc2_relset_1, axiom,
% 0.74/0.94    (![A:$i,B:$i,C:$i]:
% 0.74/0.94     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/0.94       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.74/0.94  thf('97', plain,
% 0.74/0.94      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.74/0.94         ((v5_relat_1 @ X4 @ X6)
% 0.74/0.94          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.74/0.94      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.74/0.94  thf('98', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 0.74/0.94      inference('sup-', [status(thm)], ['96', '97'])).
% 0.74/0.94  thf('99', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.74/0.94      inference('demod', [status(thm)], ['94', '95', '98'])).
% 0.74/0.94  thf('100', plain,
% 0.74/0.94      (![X0 : $i]:
% 0.74/0.94         (~ (v2_funct_1 @ X0)
% 0.74/0.94          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.74/0.94              = (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.74/0.94          | ~ (v1_funct_1 @ X0)
% 0.74/0.94          | ~ (v1_relat_1 @ X0))),
% 0.74/0.94      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.74/0.94  thf('101', plain,
% 0.74/0.94      (![X22 : $i]:
% 0.74/0.94         (m1_subset_1 @ (k6_relat_1 @ X22) @ 
% 0.74/0.94          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 0.74/0.94      inference('demod', [status(thm)], ['54', '55'])).
% 0.74/0.94  thf('102', plain,
% 0.74/0.94      (![X0 : $i]:
% 0.74/0.94         ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0) @ 
% 0.74/0.94           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.74/0.94          | ~ (v1_relat_1 @ X0)
% 0.74/0.94          | ~ (v1_funct_1 @ X0)
% 0.74/0.94          | ~ (v2_funct_1 @ X0))),
% 0.74/0.94      inference('sup+', [status(thm)], ['100', '101'])).
% 0.74/0.94  thf('103', plain,
% 0.74/0.94      (((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.74/0.94         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))
% 0.74/0.94        | ~ (v2_funct_1 @ sk_B)
% 0.74/0.94        | ~ (v1_funct_1 @ sk_B)
% 0.74/0.94        | ~ (v1_relat_1 @ sk_B))),
% 0.74/0.94      inference('sup+', [status(thm)], ['99', '102'])).
% 0.74/0.94  thf('104', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.74/0.94      inference('demod', [status(thm)], ['94', '95', '98'])).
% 0.74/0.94  thf('105', plain, ((v2_funct_1 @ sk_B)),
% 0.74/0.94      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.74/0.94  thf('106', plain, ((v1_funct_1 @ sk_B)),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('107', plain, ((v1_relat_1 @ sk_B)),
% 0.74/0.94      inference('sup-', [status(thm)], ['60', '61'])).
% 0.74/0.94  thf('108', plain,
% 0.74/0.94      ((m1_subset_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.74/0.94        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.74/0.94      inference('demod', [status(thm)], ['103', '104', '105', '106', '107'])).
% 0.74/0.94  thf('109', plain,
% 0.74/0.94      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.94         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.74/0.94          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.74/0.94      inference('condensation', [status(thm)], ['57'])).
% 0.74/0.94  thf('110', plain,
% 0.74/0.94      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.94        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.74/0.94        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B))),
% 0.74/0.94      inference('sup-', [status(thm)], ['108', '109'])).
% 0.74/0.94  thf('111', plain,
% 0.74/0.94      (((r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.94         (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ 
% 0.74/0.94         (k6_relat_1 @ (k2_relat_1 @ sk_B)))
% 0.74/0.94        | ~ (v1_relat_1 @ sk_B)
% 0.74/0.94        | ~ (v1_funct_1 @ sk_B)
% 0.74/0.94        | ~ (v2_funct_1 @ sk_B))),
% 0.74/0.94      inference('sup+', [status(thm)], ['86', '110'])).
% 0.74/0.94  thf('112', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 0.74/0.94      inference('demod', [status(thm)], ['94', '95', '98'])).
% 0.74/0.94  thf('113', plain, ((v1_relat_1 @ sk_B)),
% 0.74/0.94      inference('sup-', [status(thm)], ['60', '61'])).
% 0.74/0.94  thf('114', plain, ((v1_funct_1 @ sk_B)),
% 0.74/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.94  thf('115', plain, ((v2_funct_1 @ sk_B)),
% 0.74/0.94      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.74/0.94  thf('116', plain,
% 0.74/0.94      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.74/0.94        (k5_relat_1 @ (k2_funct_1 @ sk_B) @ sk_B) @ (k6_relat_1 @ sk_A))),
% 0.74/0.94      inference('demod', [status(thm)], ['111', '112', '113', '114', '115'])).
% 0.74/0.94  thf('117', plain, ($false),
% 0.74/0.94      inference('demod', [status(thm)], ['73', '85', '116'])).
% 0.74/0.94  
% 0.74/0.94  % SZS output end Refutation
% 0.74/0.94  
% 0.74/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
