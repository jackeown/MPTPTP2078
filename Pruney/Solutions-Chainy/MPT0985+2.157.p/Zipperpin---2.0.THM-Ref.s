%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CeEXA5K9Us

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:49 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 463 expanded)
%              Number of leaves         :   28 ( 155 expanded)
%              Depth                    :   25
%              Number of atoms          :  872 (6940 expanded)
%              Number of equality atoms :   16 ( 164 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('6',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('15',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('16',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('17',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('18',plain,(
    ! [X9: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X11 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('21',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('24',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['21','24'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ( v5_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('35',plain,
    ( ( v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['18','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['17','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('45',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('48',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X20 ) @ X21 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['14','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('62',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('63',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','65','66','67','68'])).

thf('70',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('71',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('73',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['13','71','72'])).

thf('74',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','73'])).

thf('75',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('76',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('77',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('78',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ( v1_funct_2 @ X20 @ ( k1_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('79',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('81',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('84',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['79','84'])).

thf('86',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['76','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['75','90'])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['63','64'])).

thf('93',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('94',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['91','92','93','94','95'])).

thf('97',plain,(
    $false ),
    inference(demod,[status(thm)],['74','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CeEXA5K9Us
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:15:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.36/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.52  % Solved by: fo/fo7.sh
% 0.36/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.52  % done 117 iterations in 0.066s
% 0.36/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.52  % SZS output start Refutation
% 0.36/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.52  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.36/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.52  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.52  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.36/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.36/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.36/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.52  thf(t31_funct_2, conjecture,
% 0.36/0.52    (![A:$i,B:$i,C:$i]:
% 0.36/0.52     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.52       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.36/0.52         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.36/0.52           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.36/0.52           ( m1_subset_1 @
% 0.36/0.52             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.36/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.52        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.36/0.52            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.36/0.52          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.36/0.52            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.36/0.52              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.36/0.52              ( m1_subset_1 @
% 0.36/0.52                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.36/0.52    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.36/0.52  thf('0', plain,
% 0.36/0.52      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.52        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.36/0.52        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('1', plain,
% 0.36/0.52      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.36/0.52         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.36/0.52      inference('split', [status(esa)], ['0'])).
% 0.36/0.52  thf('2', plain,
% 0.36/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf(cc2_relat_1, axiom,
% 0.36/0.52    (![A:$i]:
% 0.36/0.52     ( ( v1_relat_1 @ A ) =>
% 0.36/0.52       ( ![B:$i]:
% 0.36/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.36/0.52  thf('3', plain,
% 0.36/0.52      (![X3 : $i, X4 : $i]:
% 0.36/0.52         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.36/0.52          | (v1_relat_1 @ X3)
% 0.36/0.52          | ~ (v1_relat_1 @ X4))),
% 0.36/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.36/0.52  thf('4', plain,
% 0.36/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.36/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.52  thf(fc6_relat_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.36/0.52  thf('5', plain,
% 0.36/0.52      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.36/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.36/0.52  thf('6', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.36/0.52  thf(fc6_funct_1, axiom,
% 0.36/0.52    (![A:$i]:
% 0.36/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.36/0.52       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.36/0.52         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.36/0.52         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.36/0.52  thf('7', plain,
% 0.36/0.52      (![X9 : $i]:
% 0.36/0.52         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 0.36/0.52          | ~ (v2_funct_1 @ X9)
% 0.36/0.52          | ~ (v1_funct_1 @ X9)
% 0.36/0.52          | ~ (v1_relat_1 @ X9))),
% 0.36/0.52      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.36/0.52  thf('8', plain,
% 0.36/0.52      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.36/0.52         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.36/0.52      inference('split', [status(esa)], ['0'])).
% 0.36/0.52  thf('9', plain,
% 0.36/0.52      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C) | ~ (v2_funct_1 @ sk_C)))
% 0.36/0.52         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.36/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.52  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('11', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('12', plain,
% 0.36/0.52      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.36/0.52      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.36/0.52  thf('13', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.36/0.52      inference('sup-', [status(thm)], ['6', '12'])).
% 0.36/0.52  thf(t55_funct_1, axiom,
% 0.36/0.52    (![A:$i]:
% 0.36/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.52       ( ( v2_funct_1 @ A ) =>
% 0.36/0.52         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.36/0.52           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.36/0.52  thf('14', plain,
% 0.36/0.52      (![X10 : $i]:
% 0.36/0.52         (~ (v2_funct_1 @ X10)
% 0.36/0.52          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 0.36/0.52          | ~ (v1_funct_1 @ X10)
% 0.36/0.52          | ~ (v1_relat_1 @ X10))),
% 0.36/0.52      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.36/0.52  thf('15', plain,
% 0.36/0.52      (![X9 : $i]:
% 0.36/0.52         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 0.36/0.52          | ~ (v2_funct_1 @ X9)
% 0.36/0.52          | ~ (v1_funct_1 @ X9)
% 0.36/0.52          | ~ (v1_relat_1 @ X9))),
% 0.36/0.52      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.36/0.52  thf('16', plain,
% 0.36/0.52      (![X9 : $i]:
% 0.36/0.52         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.36/0.52          | ~ (v2_funct_1 @ X9)
% 0.36/0.52          | ~ (v1_funct_1 @ X9)
% 0.36/0.52          | ~ (v1_relat_1 @ X9))),
% 0.36/0.52      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.36/0.52  thf('17', plain,
% 0.36/0.52      (![X9 : $i]:
% 0.36/0.52         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.36/0.52          | ~ (v2_funct_1 @ X9)
% 0.36/0.52          | ~ (v1_funct_1 @ X9)
% 0.36/0.52          | ~ (v1_relat_1 @ X9))),
% 0.36/0.52      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.36/0.52  thf('18', plain,
% 0.36/0.52      (![X9 : $i]:
% 0.36/0.52         ((v1_relat_1 @ (k2_funct_1 @ X9))
% 0.36/0.52          | ~ (v2_funct_1 @ X9)
% 0.36/0.52          | ~ (v1_funct_1 @ X9)
% 0.36/0.52          | ~ (v1_relat_1 @ X9))),
% 0.36/0.52      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.36/0.52  thf('19', plain,
% 0.36/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf(dt_k1_relset_1, axiom,
% 0.36/0.52    (![A:$i,B:$i,C:$i]:
% 0.36/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.52       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.36/0.52  thf('20', plain,
% 0.36/0.52      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.36/0.52         ((m1_subset_1 @ (k1_relset_1 @ X11 @ X12 @ X13) @ (k1_zfmisc_1 @ X11))
% 0.36/0.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.36/0.52      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.36/0.52  thf('21', plain,
% 0.36/0.52      ((m1_subset_1 @ (k1_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.52  thf('22', plain,
% 0.36/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf(redefinition_k1_relset_1, axiom,
% 0.36/0.52    (![A:$i,B:$i,C:$i]:
% 0.36/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.52       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.36/0.52  thf('23', plain,
% 0.36/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.36/0.52         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.36/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.36/0.52      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.52  thf('24', plain,
% 0.36/0.52      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.36/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.52  thf('25', plain,
% 0.36/0.52      ((m1_subset_1 @ (k1_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.52      inference('demod', [status(thm)], ['21', '24'])).
% 0.36/0.52  thf(t3_subset, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.52  thf('26', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i]:
% 0.36/0.52         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.36/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.52  thf('27', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.36/0.52      inference('sup-', [status(thm)], ['25', '26'])).
% 0.36/0.52  thf('28', plain,
% 0.36/0.52      (![X10 : $i]:
% 0.36/0.52         (~ (v2_funct_1 @ X10)
% 0.36/0.52          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 0.36/0.52          | ~ (v1_funct_1 @ X10)
% 0.36/0.52          | ~ (v1_relat_1 @ X10))),
% 0.36/0.52      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.36/0.52  thf(d19_relat_1, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( v1_relat_1 @ B ) =>
% 0.36/0.52       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.36/0.52  thf('29', plain,
% 0.36/0.52      (![X5 : $i, X6 : $i]:
% 0.36/0.52         (~ (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.36/0.52          | (v5_relat_1 @ X5 @ X6)
% 0.36/0.52          | ~ (v1_relat_1 @ X5))),
% 0.36/0.52      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.36/0.52  thf('30', plain,
% 0.36/0.52      (![X0 : $i, X1 : $i]:
% 0.36/0.52         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.36/0.52          | ~ (v1_relat_1 @ X0)
% 0.36/0.52          | ~ (v1_funct_1 @ X0)
% 0.36/0.52          | ~ (v2_funct_1 @ X0)
% 0.36/0.52          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.36/0.52          | (v5_relat_1 @ (k2_funct_1 @ X0) @ X1))),
% 0.36/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.36/0.52  thf('31', plain,
% 0.36/0.52      (((v5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)
% 0.36/0.52        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.52        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.52        | ~ (v1_relat_1 @ sk_C))),
% 0.36/0.52      inference('sup-', [status(thm)], ['27', '30'])).
% 0.36/0.52  thf('32', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.36/0.52  thf('35', plain,
% 0.36/0.52      (((v5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)
% 0.36/0.52        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.36/0.52      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 0.36/0.52  thf('36', plain,
% 0.36/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.36/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.52        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.52        | (v5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A))),
% 0.36/0.52      inference('sup-', [status(thm)], ['18', '35'])).
% 0.36/0.52  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.36/0.52  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('39', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('40', plain, ((v5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_A)),
% 0.36/0.52      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.36/0.52  thf('41', plain,
% 0.36/0.52      (![X5 : $i, X6 : $i]:
% 0.36/0.52         (~ (v5_relat_1 @ X5 @ X6)
% 0.36/0.52          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.36/0.52          | ~ (v1_relat_1 @ X5))),
% 0.36/0.52      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.36/0.52  thf('42', plain,
% 0.36/0.52      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.52        | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 0.36/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.36/0.52  thf('43', plain,
% 0.36/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.36/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.52        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.52        | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 0.36/0.52      inference('sup-', [status(thm)], ['17', '42'])).
% 0.36/0.52  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.36/0.52  thf('45', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('46', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('47', plain, ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)),
% 0.36/0.52      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 0.36/0.52  thf(t4_funct_2, axiom,
% 0.36/0.52    (![A:$i,B:$i]:
% 0.36/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.52       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.36/0.52         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.36/0.52           ( m1_subset_1 @
% 0.36/0.52             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.36/0.52  thf('48', plain,
% 0.36/0.52      (![X20 : $i, X21 : $i]:
% 0.36/0.52         (~ (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 0.36/0.52          | (m1_subset_1 @ X20 @ 
% 0.36/0.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X20) @ X21)))
% 0.36/0.52          | ~ (v1_funct_1 @ X20)
% 0.36/0.52          | ~ (v1_relat_1 @ X20))),
% 0.36/0.52      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.36/0.52  thf('49', plain,
% 0.36/0.52      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.52        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.52        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.52           (k1_zfmisc_1 @ 
% 0.36/0.52            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))))),
% 0.36/0.52      inference('sup-', [status(thm)], ['47', '48'])).
% 0.36/0.52  thf('50', plain,
% 0.36/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.36/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.52        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.52        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.52           (k1_zfmisc_1 @ 
% 0.36/0.52            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))
% 0.36/0.52        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.36/0.52      inference('sup-', [status(thm)], ['16', '49'])).
% 0.36/0.52  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.36/0.52  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('53', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('54', plain,
% 0.36/0.52      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.52         (k1_zfmisc_1 @ 
% 0.36/0.52          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))
% 0.36/0.52        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.36/0.52      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.36/0.52  thf('55', plain,
% 0.36/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.36/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.52        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.52        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.52           (k1_zfmisc_1 @ 
% 0.36/0.52            (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))))),
% 0.36/0.52      inference('sup-', [status(thm)], ['15', '54'])).
% 0.36/0.52  thf('56', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.36/0.52  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('58', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('59', plain,
% 0.36/0.52      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.52        (k1_zfmisc_1 @ 
% 0.36/0.52         (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))),
% 0.36/0.52      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.36/0.52  thf('60', plain,
% 0.36/0.52      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 0.36/0.52        | ~ (v1_relat_1 @ sk_C)
% 0.36/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.52        | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.52      inference('sup+', [status(thm)], ['14', '59'])).
% 0.36/0.52  thf('61', plain,
% 0.36/0.52      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf(redefinition_k2_relset_1, axiom,
% 0.36/0.52    (![A:$i,B:$i,C:$i]:
% 0.36/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.52       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.36/0.52  thf('62', plain,
% 0.36/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.52         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.36/0.52          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.36/0.52      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.52  thf('63', plain,
% 0.36/0.52      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.36/0.52      inference('sup-', [status(thm)], ['61', '62'])).
% 0.36/0.52  thf('64', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('65', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.36/0.52      inference('sup+', [status(thm)], ['63', '64'])).
% 0.36/0.52  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.36/0.52  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('68', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('69', plain,
% 0.36/0.52      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.36/0.52      inference('demod', [status(thm)], ['60', '65', '66', '67', '68'])).
% 0.36/0.52  thf('70', plain,
% 0.36/0.52      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.52           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.36/0.52         <= (~
% 0.36/0.52             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.36/0.52      inference('split', [status(esa)], ['0'])).
% 0.36/0.52  thf('71', plain,
% 0.36/0.52      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.36/0.52      inference('sup-', [status(thm)], ['69', '70'])).
% 0.36/0.52  thf('72', plain,
% 0.36/0.52      (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.36/0.52       ~
% 0.36/0.52       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.36/0.52       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.36/0.52      inference('split', [status(esa)], ['0'])).
% 0.36/0.52  thf('73', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.36/0.52      inference('sat_resolution*', [status(thm)], ['13', '71', '72'])).
% 0.36/0.52  thf('74', plain, (~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.36/0.52      inference('simpl_trail', [status(thm)], ['1', '73'])).
% 0.36/0.52  thf('75', plain,
% 0.36/0.52      (![X10 : $i]:
% 0.36/0.52         (~ (v2_funct_1 @ X10)
% 0.36/0.52          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 0.36/0.52          | ~ (v1_funct_1 @ X10)
% 0.36/0.52          | ~ (v1_relat_1 @ X10))),
% 0.36/0.52      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.36/0.52  thf('76', plain,
% 0.36/0.52      (![X9 : $i]:
% 0.36/0.52         ((v1_funct_1 @ (k2_funct_1 @ X9))
% 0.36/0.52          | ~ (v2_funct_1 @ X9)
% 0.36/0.52          | ~ (v1_funct_1 @ X9)
% 0.36/0.52          | ~ (v1_relat_1 @ X9))),
% 0.36/0.52      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.36/0.52  thf('77', plain, ((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)),
% 0.36/0.52      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 0.36/0.52  thf('78', plain,
% 0.36/0.52      (![X20 : $i, X21 : $i]:
% 0.36/0.52         (~ (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 0.36/0.52          | (v1_funct_2 @ X20 @ (k1_relat_1 @ X20) @ X21)
% 0.36/0.52          | ~ (v1_funct_1 @ X20)
% 0.36/0.52          | ~ (v1_relat_1 @ X20))),
% 0.36/0.52      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.36/0.52  thf('79', plain,
% 0.36/0.52      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.52        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.52        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.52           (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 0.36/0.52      inference('sup-', [status(thm)], ['77', '78'])).
% 0.36/0.52  thf('80', plain,
% 0.36/0.52      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.52        (k1_zfmisc_1 @ 
% 0.36/0.52         (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)))),
% 0.36/0.52      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.36/0.52  thf('81', plain,
% 0.36/0.52      (![X3 : $i, X4 : $i]:
% 0.36/0.52         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.36/0.52          | (v1_relat_1 @ X3)
% 0.36/0.52          | ~ (v1_relat_1 @ X4))),
% 0.36/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.36/0.52  thf('82', plain,
% 0.36/0.52      ((~ (v1_relat_1 @ 
% 0.36/0.52           (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))
% 0.36/0.52        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.36/0.52      inference('sup-', [status(thm)], ['80', '81'])).
% 0.36/0.52  thf('83', plain,
% 0.36/0.52      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.36/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.36/0.52  thf('84', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.36/0.52      inference('demod', [status(thm)], ['82', '83'])).
% 0.36/0.52  thf('85', plain,
% 0.36/0.52      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.36/0.52        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.52           (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 0.36/0.52      inference('demod', [status(thm)], ['79', '84'])).
% 0.36/0.52  thf('86', plain,
% 0.36/0.52      ((~ (v1_relat_1 @ sk_C)
% 0.36/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.52        | ~ (v2_funct_1 @ sk_C)
% 0.36/0.52        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.52           (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))),
% 0.36/0.52      inference('sup-', [status(thm)], ['76', '85'])).
% 0.36/0.52  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.36/0.52  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('89', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('90', plain,
% 0.36/0.52      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.36/0.52        (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)),
% 0.36/0.52      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 0.36/0.52  thf('91', plain,
% 0.36/0.52      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 0.36/0.52        | ~ (v1_relat_1 @ sk_C)
% 0.36/0.52        | ~ (v1_funct_1 @ sk_C)
% 0.36/0.52        | ~ (v2_funct_1 @ sk_C))),
% 0.36/0.52      inference('sup+', [status(thm)], ['75', '90'])).
% 0.36/0.52  thf('92', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.36/0.52      inference('sup+', [status(thm)], ['63', '64'])).
% 0.36/0.52  thf('93', plain, ((v1_relat_1 @ sk_C)),
% 0.36/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.36/0.52  thf('94', plain, ((v1_funct_1 @ sk_C)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('95', plain, ((v2_funct_1 @ sk_C)),
% 0.36/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.52  thf('96', plain, ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)),
% 0.36/0.52      inference('demod', [status(thm)], ['91', '92', '93', '94', '95'])).
% 0.36/0.52  thf('97', plain, ($false), inference('demod', [status(thm)], ['74', '96'])).
% 0.36/0.52  
% 0.36/0.52  % SZS output end Refutation
% 0.36/0.52  
% 0.36/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
