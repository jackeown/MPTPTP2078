%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fo8hBY6ZBB

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:47 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 396 expanded)
%              Number of leaves         :   31 ( 134 expanded)
%              Depth                    :   12
%              Number of atoms          :  827 (5767 expanded)
%              Number of equality atoms :   34 ( 177 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('6',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('7',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ X6 )
        = ( k4_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['1','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('14',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X12 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('22',plain,(
    m1_subset_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k3_relset_1 @ X19 @ X20 @ X18 )
        = ( k4_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('25',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('28',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['19','30','31'])).

thf('33',plain,(
    ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['12','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v5_relat_1 @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('36',plain,(
    v5_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['34','35'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('43',plain,(
    v1_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k3_relset_1 @ sk_A @ sk_B @ sk_C ) ) @ sk_A ),
    inference(demod,[status(thm)],['38','43'])).

thf('45',plain,
    ( ( k3_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('46',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('47',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('48',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('50',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['44','45','52'])).

thf('54',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k1_relat_1 @ X8 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('55',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X21 ) @ X22 )
      | ( v1_funct_2 @ X21 @ ( k1_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('59',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('60',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('61',plain,(
    ! [X8: $i] :
      ( ~ ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X8 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('62',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('68',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('69',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['66','71'])).

thf('73',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('74',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('75',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('76',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('81',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('82',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('83',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['4','5'])).

thf('90',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['57','58','59','72','73','79','80','86','87','88','89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['33','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fo8hBY6ZBB
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 14:13:56 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.35/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.55  % Solved by: fo/fo7.sh
% 0.35/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.55  % done 115 iterations in 0.070s
% 0.35/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.55  % SZS output start Refutation
% 0.35/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.35/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.55  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.35/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.35/0.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.35/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.35/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.35/0.55  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.35/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.35/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.55  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.35/0.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.35/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.35/0.55  thf(t31_funct_2, conjecture,
% 0.35/0.55    (![A:$i,B:$i,C:$i]:
% 0.35/0.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.55       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.35/0.55         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.35/0.55           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.35/0.55           ( m1_subset_1 @
% 0.35/0.55             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.35/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.35/0.55        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.35/0.55            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.35/0.55          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.35/0.55            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.35/0.55              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.35/0.55              ( m1_subset_1 @
% 0.35/0.55                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.35/0.55    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.35/0.55  thf('0', plain,
% 0.35/0.55      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.55        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.35/0.55        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.35/0.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('1', plain,
% 0.35/0.55      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.35/0.55         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('2', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(cc2_relat_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( v1_relat_1 @ A ) =>
% 0.35/0.55       ( ![B:$i]:
% 0.35/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.35/0.55  thf('3', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.35/0.55          | (v1_relat_1 @ X0)
% 0.35/0.55          | ~ (v1_relat_1 @ X1))),
% 0.35/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.35/0.55  thf('4', plain,
% 0.35/0.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.35/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.55  thf(fc6_relat_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.35/0.55  thf('5', plain,
% 0.35/0.55      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.35/0.55  thf('6', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.35/0.55  thf(d9_funct_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.55       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.35/0.55  thf('7', plain,
% 0.35/0.55      (![X6 : $i]:
% 0.35/0.55         (~ (v2_funct_1 @ X6)
% 0.35/0.55          | ((k2_funct_1 @ X6) = (k4_relat_1 @ X6))
% 0.35/0.55          | ~ (v1_funct_1 @ X6)
% 0.35/0.55          | ~ (v1_relat_1 @ X6))),
% 0.35/0.55      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.35/0.55  thf('8', plain,
% 0.35/0.55      ((~ (v1_funct_1 @ sk_C)
% 0.35/0.55        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.35/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.35/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.35/0.55  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('10', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('11', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.35/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.35/0.55  thf('12', plain,
% 0.35/0.55      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))
% 0.35/0.55         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.35/0.55      inference('demod', [status(thm)], ['1', '11'])).
% 0.35/0.55  thf('13', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.35/0.55  thf(dt_k2_funct_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.55       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.35/0.55         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.35/0.55  thf('14', plain,
% 0.35/0.55      (![X7 : $i]:
% 0.35/0.55         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 0.35/0.55          | ~ (v1_funct_1 @ X7)
% 0.35/0.55          | ~ (v1_relat_1 @ X7))),
% 0.35/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.35/0.55  thf('15', plain,
% 0.35/0.55      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.35/0.55         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('16', plain,
% 0.35/0.55      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 0.35/0.55         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.35/0.55  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('18', plain,
% 0.35/0.55      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.35/0.55      inference('demod', [status(thm)], ['16', '17'])).
% 0.35/0.55  thf('19', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['13', '18'])).
% 0.35/0.55  thf('20', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(dt_k3_relset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.55       ( m1_subset_1 @
% 0.35/0.55         ( k3_relset_1 @ A @ B @ C ) @ 
% 0.35/0.55         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 0.35/0.55  thf('21', plain,
% 0.35/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.35/0.55         ((m1_subset_1 @ (k3_relset_1 @ X12 @ X13 @ X14) @ 
% 0.35/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X12)))
% 0.35/0.55          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.35/0.55      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 0.35/0.55  thf('22', plain,
% 0.35/0.55      ((m1_subset_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.35/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.55  thf('23', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(redefinition_k3_relset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.55       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.35/0.55  thf('24', plain,
% 0.35/0.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.35/0.55         (((k3_relset_1 @ X19 @ X20 @ X18) = (k4_relat_1 @ X18))
% 0.35/0.55          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.35/0.55      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.35/0.55  thf('25', plain,
% 0.35/0.55      (((k3_relset_1 @ sk_A @ sk_B @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.35/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.35/0.55  thf('26', plain,
% 0.35/0.55      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.35/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.55      inference('demod', [status(thm)], ['22', '25'])).
% 0.35/0.55  thf('27', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.35/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.35/0.55  thf('28', plain,
% 0.35/0.55      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.35/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.35/0.55         <= (~
% 0.35/0.55             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.35/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('29', plain,
% 0.35/0.55      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.35/0.55           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.35/0.55         <= (~
% 0.35/0.55             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.35/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.55  thf('30', plain,
% 0.35/0.55      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.35/0.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.35/0.55      inference('sup-', [status(thm)], ['26', '29'])).
% 0.35/0.55  thf('31', plain,
% 0.35/0.55      (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.35/0.55       ~
% 0.35/0.55       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.35/0.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.35/0.55       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.35/0.55      inference('split', [status(esa)], ['0'])).
% 0.35/0.55  thf('32', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.35/0.55      inference('sat_resolution*', [status(thm)], ['19', '30', '31'])).
% 0.35/0.55  thf('33', plain, (~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)),
% 0.35/0.55      inference('simpl_trail', [status(thm)], ['12', '32'])).
% 0.35/0.55  thf('34', plain,
% 0.35/0.55      ((m1_subset_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.35/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.55  thf(cc2_relset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.35/0.55  thf('35', plain,
% 0.35/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.35/0.55         ((v5_relat_1 @ X9 @ X11)
% 0.35/0.55          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.35/0.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.35/0.55  thf('36', plain, ((v5_relat_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C) @ sk_A)),
% 0.35/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.35/0.55  thf(d19_relat_1, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( v1_relat_1 @ B ) =>
% 0.35/0.55       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.35/0.55  thf('37', plain,
% 0.35/0.55      (![X2 : $i, X3 : $i]:
% 0.35/0.55         (~ (v5_relat_1 @ X2 @ X3)
% 0.35/0.55          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 0.35/0.55          | ~ (v1_relat_1 @ X2))),
% 0.35/0.55      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.35/0.55  thf('38', plain,
% 0.35/0.55      ((~ (v1_relat_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))
% 0.35/0.55        | (r1_tarski @ (k2_relat_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C)) @ sk_A))),
% 0.35/0.55      inference('sup-', [status(thm)], ['36', '37'])).
% 0.35/0.55  thf('39', plain,
% 0.35/0.55      ((m1_subset_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.35/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.55  thf('40', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.35/0.55          | (v1_relat_1 @ X0)
% 0.35/0.55          | ~ (v1_relat_1 @ X1))),
% 0.35/0.55      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.35/0.55  thf('41', plain,
% 0.35/0.55      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))
% 0.35/0.55        | (v1_relat_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.35/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.35/0.55  thf('42', plain,
% 0.35/0.55      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.35/0.55      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.35/0.55  thf('43', plain, ((v1_relat_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C))),
% 0.35/0.55      inference('demod', [status(thm)], ['41', '42'])).
% 0.35/0.55  thf('44', plain,
% 0.35/0.55      ((r1_tarski @ (k2_relat_1 @ (k3_relset_1 @ sk_A @ sk_B @ sk_C)) @ sk_A)),
% 0.35/0.55      inference('demod', [status(thm)], ['38', '43'])).
% 0.35/0.55  thf('45', plain,
% 0.35/0.55      (((k3_relset_1 @ sk_A @ sk_B @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.35/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.35/0.55  thf('46', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.35/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.35/0.55  thf(t55_funct_1, axiom,
% 0.35/0.55    (![A:$i]:
% 0.35/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.35/0.55       ( ( v2_funct_1 @ A ) =>
% 0.35/0.55         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.35/0.55           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.35/0.55  thf('47', plain,
% 0.35/0.55      (![X8 : $i]:
% 0.35/0.55         (~ (v2_funct_1 @ X8)
% 0.35/0.55          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 0.35/0.55          | ~ (v1_funct_1 @ X8)
% 0.35/0.55          | ~ (v1_relat_1 @ X8))),
% 0.35/0.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.35/0.55  thf('48', plain,
% 0.35/0.55      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.35/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.35/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.35/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.35/0.55      inference('sup+', [status(thm)], ['46', '47'])).
% 0.35/0.55  thf('49', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.35/0.55  thf('50', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('51', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('52', plain,
% 0.35/0.55      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.35/0.55      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.35/0.55  thf('53', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.35/0.55      inference('demod', [status(thm)], ['44', '45', '52'])).
% 0.35/0.55  thf('54', plain,
% 0.35/0.55      (![X8 : $i]:
% 0.35/0.55         (~ (v2_funct_1 @ X8)
% 0.35/0.55          | ((k1_relat_1 @ X8) = (k2_relat_1 @ (k2_funct_1 @ X8)))
% 0.35/0.55          | ~ (v1_funct_1 @ X8)
% 0.35/0.55          | ~ (v1_relat_1 @ X8))),
% 0.35/0.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.35/0.55  thf(t4_funct_2, axiom,
% 0.35/0.55    (![A:$i,B:$i]:
% 0.35/0.55     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.35/0.55       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.35/0.55         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.35/0.55           ( m1_subset_1 @
% 0.35/0.55             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.35/0.55  thf('55', plain,
% 0.35/0.55      (![X21 : $i, X22 : $i]:
% 0.35/0.55         (~ (r1_tarski @ (k2_relat_1 @ X21) @ X22)
% 0.35/0.55          | (v1_funct_2 @ X21 @ (k1_relat_1 @ X21) @ X22)
% 0.35/0.55          | ~ (v1_funct_1 @ X21)
% 0.35/0.55          | ~ (v1_relat_1 @ X21))),
% 0.35/0.55      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.35/0.55  thf('56', plain,
% 0.35/0.55      (![X0 : $i, X1 : $i]:
% 0.35/0.55         (~ (r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 0.35/0.55          | ~ (v1_relat_1 @ X0)
% 0.35/0.55          | ~ (v1_funct_1 @ X0)
% 0.35/0.55          | ~ (v2_funct_1 @ X0)
% 0.35/0.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.35/0.55          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.35/0.55          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 0.35/0.55             (k1_relat_1 @ (k2_funct_1 @ X0)) @ X1))),
% 0.35/0.55      inference('sup-', [status(thm)], ['54', '55'])).
% 0.35/0.55  thf('57', plain,
% 0.35/0.55      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ 
% 0.35/0.55         (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 0.35/0.55        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.55        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.35/0.55        | ~ (v2_funct_1 @ sk_C)
% 0.35/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.35/0.55        | ~ (v1_relat_1 @ sk_C))),
% 0.35/0.55      inference('sup-', [status(thm)], ['53', '56'])).
% 0.35/0.55  thf('58', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.35/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.35/0.55  thf('59', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.35/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.35/0.55  thf('60', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.35/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.35/0.55  thf('61', plain,
% 0.35/0.55      (![X8 : $i]:
% 0.35/0.55         (~ (v2_funct_1 @ X8)
% 0.35/0.55          | ((k2_relat_1 @ X8) = (k1_relat_1 @ (k2_funct_1 @ X8)))
% 0.35/0.55          | ~ (v1_funct_1 @ X8)
% 0.35/0.55          | ~ (v1_relat_1 @ X8))),
% 0.35/0.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.35/0.55  thf('62', plain,
% 0.35/0.55      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.35/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.35/0.55        | ~ (v1_funct_1 @ sk_C)
% 0.35/0.55        | ~ (v2_funct_1 @ sk_C))),
% 0.35/0.55      inference('sup+', [status(thm)], ['60', '61'])).
% 0.35/0.55  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.35/0.55  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('65', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('66', plain,
% 0.35/0.55      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.35/0.55      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.35/0.55  thf('67', plain,
% 0.35/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf(redefinition_k2_relset_1, axiom,
% 0.35/0.55    (![A:$i,B:$i,C:$i]:
% 0.35/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.55       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.35/0.55  thf('68', plain,
% 0.35/0.55      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.55         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.35/0.55          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.35/0.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.35/0.55  thf('69', plain,
% 0.35/0.55      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.35/0.55      inference('sup-', [status(thm)], ['67', '68'])).
% 0.35/0.55  thf('70', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('71', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.35/0.55      inference('sup+', [status(thm)], ['69', '70'])).
% 0.35/0.55  thf('72', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.35/0.55      inference('demod', [status(thm)], ['66', '71'])).
% 0.35/0.55  thf('73', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.35/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.35/0.55  thf('74', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.35/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.35/0.55  thf('75', plain,
% 0.35/0.55      (![X7 : $i]:
% 0.35/0.55         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 0.35/0.55          | ~ (v1_funct_1 @ X7)
% 0.35/0.55          | ~ (v1_relat_1 @ X7))),
% 0.35/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.35/0.55  thf('76', plain,
% 0.35/0.55      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.35/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.35/0.55        | ~ (v1_funct_1 @ sk_C))),
% 0.35/0.55      inference('sup+', [status(thm)], ['74', '75'])).
% 0.35/0.55  thf('77', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.35/0.55  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('79', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.35/0.55      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.35/0.55  thf('80', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.35/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.35/0.55  thf('81', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.35/0.55      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.35/0.55  thf('82', plain,
% 0.35/0.55      (![X7 : $i]:
% 0.35/0.55         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.35/0.55          | ~ (v1_funct_1 @ X7)
% 0.35/0.55          | ~ (v1_relat_1 @ X7))),
% 0.35/0.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.35/0.55  thf('83', plain,
% 0.35/0.55      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.35/0.55        | ~ (v1_relat_1 @ sk_C)
% 0.35/0.55        | ~ (v1_funct_1 @ sk_C))),
% 0.35/0.55      inference('sup+', [status(thm)], ['81', '82'])).
% 0.35/0.55  thf('84', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.35/0.55  thf('85', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('86', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.35/0.55      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.35/0.55  thf('87', plain, ((v2_funct_1 @ sk_C)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 0.35/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.55  thf('89', plain, ((v1_relat_1 @ sk_C)),
% 0.35/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.35/0.55  thf('90', plain, ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)),
% 0.35/0.55      inference('demod', [status(thm)],
% 0.35/0.55                ['57', '58', '59', '72', '73', '79', '80', '86', '87', '88', 
% 0.35/0.55                 '89'])).
% 0.35/0.55  thf('91', plain, ($false), inference('demod', [status(thm)], ['33', '90'])).
% 0.35/0.55  
% 0.35/0.55  % SZS output end Refutation
% 0.35/0.55  
% 0.35/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
