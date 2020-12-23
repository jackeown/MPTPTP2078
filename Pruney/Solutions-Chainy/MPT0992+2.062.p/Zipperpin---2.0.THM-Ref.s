%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zudR0IO5uD

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:43 EST 2020

% Result     : Theorem 43.48s
% Output     : Refutation 43.48s
% Verified   : 
% Statistics : Number of formulae       :  278 (1166 expanded)
%              Number of leaves         :   51 ( 363 expanded)
%              Depth                    :   28
%              Number of atoms          : 2226 (16293 expanded)
%              Number of equality atoms :  132 ( 713 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t38_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ C @ A )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
            & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
            & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ C @ A )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) )
              & ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B )
              & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ D @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X67: $i,X68: $i,X69: $i,X70: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X68 @ X69 ) ) )
      | ~ ( v1_funct_1 @ X67 )
      | ( ( k2_partfun1 @ X68 @ X69 @ X67 @ X70 )
        = ( k7_relat_1 @ X67 @ X70 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['1','6'])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('10',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D ) )
   <= ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X25: $i,X26: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['12','17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( v4_relat_1 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc23_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v4_relat_1 @ C @ B ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ) )).

thf('23',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) @ X23 )
      | ~ ( v4_relat_1 @ X22 @ X24 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('26',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('29',plain,(
    ! [X40: $i] :
      ( ( ( k7_relat_1 @ X40 @ ( k1_relat_1 @ X40 ) )
        = X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('31',plain,
    ( ( v4_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('33',plain,(
    v4_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['31','32'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X30
        = ( k7_relat_1 @ X30 @ X31 ) )
      | ~ ( v4_relat_1 @ X30 @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('37',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('38',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X34 @ X35 ) @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('39',plain,
    ( ( r1_tarski @ sk_D @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('41',plain,(
    r1_tarski @ sk_D @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X34 @ X35 ) @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_D ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('48',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('53',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['28','53'])).

thf('55',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X34 @ X35 ) @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ( ( r1_tarski @ A @ D )
       => ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('57',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) )
      | ~ ( r1_tarski @ X55 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t4_relset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_D )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('61',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('62',plain,(
    ! [X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X51 ) @ X52 )
      | ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X53 ) ) )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X53 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('66',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('70',plain,(
    ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['19','68','69'])).

thf('71',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['7','70'])).

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

thf('72',plain,(
    ! [X59: $i,X60: $i] :
      ( ( zip_tseitin_0 @ X59 @ X60 )
      | ( X59 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('73',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('74',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ~ ( zip_tseitin_0 @ X64 @ X65 )
      | ( zip_tseitin_1 @ X66 @ X64 @ X65 )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X64 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('75',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ~ ( v1_funct_2 @ X63 @ X61 @ X62 )
      | ( X61
        = ( k1_relset_1 @ X61 @ X62 @ X63 ) )
      | ~ ( zip_tseitin_1 @ X63 @ X62 @ X61 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('79',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('81',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( ( k1_relset_1 @ X49 @ X50 @ X48 )
        = ( k1_relat_1 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('82',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['79','82'])).

thf('84',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['76','83'])).

thf('85',plain,(
    v4_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('86',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('87',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('89',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_D ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','89'])).

thf('91',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('95',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( r1_tarski @ X38 @ ( k1_relat_1 @ X39 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X39 @ X38 ) )
        = X38 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('96',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('98',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
      = sk_C ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['99'])).

thf('101',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['99'])).

thf('102',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('104',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('105',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['103','105'])).

thf('107',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('108',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('109',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('110',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('113',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('114',plain,(
    ! [X67: $i,X68: $i,X69: $i,X70: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X68 @ X69 ) ) )
      | ~ ( v1_funct_1 @ X67 )
      | ( ( k2_partfun1 @ X68 @ X69 @ X67 @ X70 )
        = ( k7_relat_1 @ X67 @ X70 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = ( k7_relat_1 @ k1_xboole_0 @ X2 ) )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('117',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( v4_relat_1 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('118',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X30
        = ( k7_relat_1 @ X30 @ X31 ) )
      | ~ ( v4_relat_1 @ X30 @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['104'])).

thf('122',plain,(
    ! [X25: $i,X26: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('123',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['120','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['115','124'])).

thf('126',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['112','125'])).

thf('127',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['99'])).

thf('128',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('129',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
   <= ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('131',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['99'])).

thf('132',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('135',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('137',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['104'])).

thf('138',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['129','130','135','136','137'])).

thf('139',plain,
    ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['126','138'])).

thf('140',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('141',plain,
    ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
    | ( sk_A != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['112','125'])).

thf('143',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('144',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['99'])).

thf('145',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('146',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
   <= ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('148',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('149',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ k1_xboole_0 ) @ k1_xboole_0 @ sk_B )
   <= ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_B )
   <= ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['143','149'])).

thf('151',plain,
    ( ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B )
   <= ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['142','150'])).

thf('152',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('153',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ( ( k1_relset_1 @ X49 @ X50 @ X48 )
        = ( k1_relat_1 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X49 @ X50 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('156',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['121','122'])).

thf('159',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('161',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['154','161'])).

thf('163',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( X61
       != ( k1_relset_1 @ X61 @ X62 @ X63 ) )
      | ( v1_funct_2 @ X63 @ X61 @ X62 )
      | ~ ( zip_tseitin_1 @ X63 @ X62 @ X61 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ k1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
    ! [X59: $i,X60: $i] :
      ( ( zip_tseitin_0 @ X59 @ X60 )
      | ( X60 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('167',plain,(
    ! [X59: $i] :
      ( zip_tseitin_0 @ X59 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('169',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ~ ( zip_tseitin_0 @ X64 @ X65 )
      | ( zip_tseitin_1 @ X66 @ X64 @ X65 )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X64 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['167','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['165','171'])).

thf('173',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['151','172'])).

thf('174',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['99'])).

thf('175',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['19','141','173','69','174'])).

thf('176',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['100','175'])).

thf('177',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ sk_C ) )
    = sk_C ),
    inference('simplify_reflect-',[status(thm)],['98','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('179',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( v5_relat_1 @ X45 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('180',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('181',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v5_relat_1 @ X18 @ X19 )
      | ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('184',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['182','183'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('185',plain,(
    ! [X71: $i,X72: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X71 ) @ X72 )
      | ( v1_funct_2 @ X71 @ ( k1_relat_1 @ X71 ) @ X72 )
      | ~ ( v1_funct_1 @ X71 )
      | ~ ( v1_relat_1 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('189',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X32 @ X33 ) ) @ X33 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf(t103_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('190',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ X27 @ X28 )
      | ~ ( v1_relat_1 @ X29 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X29 @ X28 ) @ X27 )
        = ( k7_relat_1 @ X29 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t103_relat_1])).

thf('191',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
        = ( k7_relat_1 @ X2 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('193',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X30
        = ( k7_relat_1 @ X30 @ X31 ) )
      | ~ ( v4_relat_1 @ X30 @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('194',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( ( k7_relat_1 @ sk_D @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_D @ X0 )
      = ( k7_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,(
    ! [X40: $i] :
      ( ( ( k7_relat_1 @ X40 @ ( k1_relat_1 @ X40 ) )
        = X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('198',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X32 @ X33 ) ) @ X33 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('202',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['202'])).

thf('204',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ X22 @ X23 ) @ X24 )
      | ~ ( v4_relat_1 @ X22 @ X24 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('205',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['196','206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('209',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference(demod,[status(thm)],['207','208'])).

thf('210',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X30
        = ( k7_relat_1 @ X30 @ X31 ) )
      | ~ ( v4_relat_1 @ X30 @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( ( k7_relat_1 @ sk_D @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_D @ X0 )
      = ( k7_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_D @ X0 )
        = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['191','213'])).

thf('215',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('216',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['214','215','216'])).

thf('218',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['217','218'])).

thf('220',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['15','16'])).

thf('221',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['219','220','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['188','222'])).

thf('224',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_C @ sk_B ),
    inference('sup+',[status(thm)],['177','223'])).

thf('225',plain,(
    $false ),
    inference(demod,[status(thm)],['71','224'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zudR0IO5uD
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:23:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 43.48/43.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 43.48/43.68  % Solved by: fo/fo7.sh
% 43.48/43.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 43.48/43.68  % done 31485 iterations in 43.212s
% 43.48/43.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 43.48/43.68  % SZS output start Refutation
% 43.48/43.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 43.48/43.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 43.48/43.68  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 43.48/43.68  thf(sk_A_type, type, sk_A: $i).
% 43.48/43.68  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 43.48/43.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 43.48/43.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 43.48/43.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 43.48/43.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 43.48/43.68  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 43.48/43.68  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 43.48/43.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 43.48/43.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 43.48/43.68  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 43.48/43.68  thf(sk_D_type, type, sk_D: $i).
% 43.48/43.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 43.48/43.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 43.48/43.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 43.48/43.68  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 43.48/43.68  thf(sk_B_type, type, sk_B: $i).
% 43.48/43.68  thf(sk_C_type, type, sk_C: $i).
% 43.48/43.68  thf(t38_funct_2, conjecture,
% 43.48/43.68    (![A:$i,B:$i,C:$i,D:$i]:
% 43.48/43.68     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 43.48/43.68         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 43.48/43.68       ( ( r1_tarski @ C @ A ) =>
% 43.48/43.68         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 43.48/43.68           ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 43.48/43.68             ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 43.48/43.68             ( m1_subset_1 @
% 43.48/43.68               ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 43.48/43.68               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ))).
% 43.48/43.68  thf(zf_stmt_0, negated_conjecture,
% 43.48/43.68    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 43.48/43.68        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 43.48/43.68            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 43.48/43.68          ( ( r1_tarski @ C @ A ) =>
% 43.48/43.68            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 43.48/43.68              ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ D @ C ) ) & 
% 43.48/43.68                ( v1_funct_2 @ ( k2_partfun1 @ A @ B @ D @ C ) @ C @ B ) & 
% 43.48/43.68                ( m1_subset_1 @
% 43.48/43.68                  ( k2_partfun1 @ A @ B @ D @ C ) @ 
% 43.48/43.68                  ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) ) ) )),
% 43.48/43.68    inference('cnf.neg', [status(esa)], [t38_funct_2])).
% 43.48/43.68  thf('0', plain,
% 43.48/43.68      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))
% 43.48/43.68        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 43.48/43.68             sk_B)
% 43.48/43.68        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 43.48/43.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 43.48/43.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.48/43.68  thf('1', plain,
% 43.48/43.68      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B))
% 43.48/43.68         <= (~
% 43.48/43.68             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 43.48/43.68               sk_B)))),
% 43.48/43.68      inference('split', [status(esa)], ['0'])).
% 43.48/43.68  thf('2', plain,
% 43.48/43.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 43.48/43.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.48/43.68  thf(redefinition_k2_partfun1, axiom,
% 43.48/43.68    (![A:$i,B:$i,C:$i,D:$i]:
% 43.48/43.68     ( ( ( v1_funct_1 @ C ) & 
% 43.48/43.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 43.48/43.68       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 43.48/43.68  thf('3', plain,
% 43.48/43.68      (![X67 : $i, X68 : $i, X69 : $i, X70 : $i]:
% 43.48/43.68         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X68 @ X69)))
% 43.48/43.68          | ~ (v1_funct_1 @ X67)
% 43.48/43.68          | ((k2_partfun1 @ X68 @ X69 @ X67 @ X70) = (k7_relat_1 @ X67 @ X70)))),
% 43.48/43.68      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 43.48/43.68  thf('4', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         (((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))
% 43.48/43.68          | ~ (v1_funct_1 @ sk_D))),
% 43.48/43.68      inference('sup-', [status(thm)], ['2', '3'])).
% 43.48/43.68  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 43.48/43.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.48/43.68  thf('6', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 43.48/43.68      inference('demod', [status(thm)], ['4', '5'])).
% 43.48/43.68  thf('7', plain,
% 43.48/43.68      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B))
% 43.48/43.68         <= (~
% 43.48/43.68             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 43.48/43.68               sk_B)))),
% 43.48/43.68      inference('demod', [status(thm)], ['1', '6'])).
% 43.48/43.68  thf(fc8_funct_1, axiom,
% 43.48/43.68    (![A:$i,B:$i]:
% 43.48/43.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 43.48/43.68       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 43.48/43.68         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 43.48/43.68  thf('8', plain,
% 43.48/43.68      (![X43 : $i, X44 : $i]:
% 43.48/43.68         (~ (v1_funct_1 @ X43)
% 43.48/43.68          | ~ (v1_relat_1 @ X43)
% 43.48/43.68          | (v1_funct_1 @ (k7_relat_1 @ X43 @ X44)))),
% 43.48/43.68      inference('cnf', [status(esa)], [fc8_funct_1])).
% 43.48/43.68  thf('9', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 43.48/43.68      inference('demod', [status(thm)], ['4', '5'])).
% 43.48/43.68  thf('10', plain,
% 43.48/43.68      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))
% 43.48/43.68         <= (~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))))),
% 43.48/43.68      inference('split', [status(esa)], ['0'])).
% 43.48/43.68  thf('11', plain,
% 43.48/43.68      ((~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ sk_C)))
% 43.48/43.68         <= (~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))))),
% 43.48/43.68      inference('sup-', [status(thm)], ['9', '10'])).
% 43.48/43.68  thf('12', plain,
% 43.48/43.68      (((~ (v1_relat_1 @ sk_D) | ~ (v1_funct_1 @ sk_D)))
% 43.48/43.68         <= (~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C))))),
% 43.48/43.68      inference('sup-', [status(thm)], ['8', '11'])).
% 43.48/43.68  thf('13', plain,
% 43.48/43.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 43.48/43.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.48/43.68  thf(cc2_relat_1, axiom,
% 43.48/43.68    (![A:$i]:
% 43.48/43.68     ( ( v1_relat_1 @ A ) =>
% 43.48/43.68       ( ![B:$i]:
% 43.48/43.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 43.48/43.68  thf('14', plain,
% 43.48/43.68      (![X14 : $i, X15 : $i]:
% 43.48/43.68         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 43.48/43.68          | (v1_relat_1 @ X14)
% 43.48/43.68          | ~ (v1_relat_1 @ X15))),
% 43.48/43.68      inference('cnf', [status(esa)], [cc2_relat_1])).
% 43.48/43.68  thf('15', plain,
% 43.48/43.68      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 43.48/43.68      inference('sup-', [status(thm)], ['13', '14'])).
% 43.48/43.68  thf(fc6_relat_1, axiom,
% 43.48/43.68    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 43.48/43.68  thf('16', plain,
% 43.48/43.68      (![X25 : $i, X26 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X25 @ X26))),
% 43.48/43.68      inference('cnf', [status(esa)], [fc6_relat_1])).
% 43.48/43.68  thf('17', plain, ((v1_relat_1 @ sk_D)),
% 43.48/43.68      inference('demod', [status(thm)], ['15', '16'])).
% 43.48/43.68  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 43.48/43.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.48/43.68  thf('19', plain,
% 43.48/43.68      (((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 43.48/43.68      inference('demod', [status(thm)], ['12', '17', '18'])).
% 43.48/43.68  thf('20', plain,
% 43.48/43.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 43.48/43.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.48/43.68  thf(cc2_relset_1, axiom,
% 43.48/43.68    (![A:$i,B:$i,C:$i]:
% 43.48/43.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 43.48/43.68       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 43.48/43.68  thf('21', plain,
% 43.48/43.68      (![X45 : $i, X46 : $i, X47 : $i]:
% 43.48/43.68         ((v4_relat_1 @ X45 @ X46)
% 43.48/43.68          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47))))),
% 43.48/43.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 43.48/43.68  thf('22', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 43.48/43.68      inference('sup-', [status(thm)], ['20', '21'])).
% 43.48/43.68  thf(fc23_relat_1, axiom,
% 43.48/43.68    (![A:$i,B:$i,C:$i]:
% 43.48/43.68     ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ B ) ) =>
% 43.48/43.68       ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) ) & 
% 43.48/43.68         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A ) & 
% 43.48/43.68         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ))).
% 43.48/43.68  thf('23', plain,
% 43.48/43.68      (![X22 : $i, X23 : $i, X24 : $i]:
% 43.48/43.68         ((v4_relat_1 @ (k7_relat_1 @ X22 @ X23) @ X23)
% 43.48/43.68          | ~ (v4_relat_1 @ X22 @ X24)
% 43.48/43.68          | ~ (v1_relat_1 @ X22))),
% 43.48/43.68      inference('cnf', [status(esa)], [fc23_relat_1])).
% 43.48/43.68  thf('24', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         (~ (v1_relat_1 @ sk_D) | (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0))),
% 43.48/43.68      inference('sup-', [status(thm)], ['22', '23'])).
% 43.48/43.68  thf('25', plain, ((v1_relat_1 @ sk_D)),
% 43.48/43.68      inference('demod', [status(thm)], ['15', '16'])).
% 43.48/43.68  thf('26', plain, (![X0 : $i]: (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0)),
% 43.48/43.68      inference('demod', [status(thm)], ['24', '25'])).
% 43.48/43.68  thf(d18_relat_1, axiom,
% 43.48/43.68    (![A:$i,B:$i]:
% 43.48/43.68     ( ( v1_relat_1 @ B ) =>
% 43.48/43.68       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 43.48/43.68  thf('27', plain,
% 43.48/43.68      (![X16 : $i, X17 : $i]:
% 43.48/43.68         (~ (v4_relat_1 @ X16 @ X17)
% 43.48/43.68          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 43.48/43.68          | ~ (v1_relat_1 @ X16))),
% 43.48/43.68      inference('cnf', [status(esa)], [d18_relat_1])).
% 43.48/43.68  thf('28', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 43.48/43.68          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0))),
% 43.48/43.68      inference('sup-', [status(thm)], ['26', '27'])).
% 43.48/43.68  thf(t98_relat_1, axiom,
% 43.48/43.68    (![A:$i]:
% 43.48/43.68     ( ( v1_relat_1 @ A ) =>
% 43.48/43.68       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 43.48/43.68  thf('29', plain,
% 43.48/43.68      (![X40 : $i]:
% 43.48/43.68         (((k7_relat_1 @ X40 @ (k1_relat_1 @ X40)) = (X40))
% 43.48/43.68          | ~ (v1_relat_1 @ X40))),
% 43.48/43.68      inference('cnf', [status(esa)], [t98_relat_1])).
% 43.48/43.68  thf('30', plain, (![X0 : $i]: (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0)),
% 43.48/43.68      inference('demod', [status(thm)], ['24', '25'])).
% 43.48/43.68  thf('31', plain,
% 43.48/43.68      (((v4_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)) | ~ (v1_relat_1 @ sk_D))),
% 43.48/43.68      inference('sup+', [status(thm)], ['29', '30'])).
% 43.48/43.68  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 43.48/43.68      inference('demod', [status(thm)], ['15', '16'])).
% 43.48/43.68  thf('33', plain, ((v4_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))),
% 43.48/43.68      inference('demod', [status(thm)], ['31', '32'])).
% 43.48/43.68  thf(t209_relat_1, axiom,
% 43.48/43.68    (![A:$i,B:$i]:
% 43.48/43.68     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 43.48/43.68       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 43.48/43.68  thf('34', plain,
% 43.48/43.68      (![X30 : $i, X31 : $i]:
% 43.48/43.68         (((X30) = (k7_relat_1 @ X30 @ X31))
% 43.48/43.68          | ~ (v4_relat_1 @ X30 @ X31)
% 43.48/43.68          | ~ (v1_relat_1 @ X30))),
% 43.48/43.68      inference('cnf', [status(esa)], [t209_relat_1])).
% 43.48/43.68  thf('35', plain,
% 43.48/43.68      ((~ (v1_relat_1 @ sk_D)
% 43.48/43.68        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))))),
% 43.48/43.68      inference('sup-', [status(thm)], ['33', '34'])).
% 43.48/43.68  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 43.48/43.68      inference('demod', [status(thm)], ['15', '16'])).
% 43.48/43.68  thf('37', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 43.48/43.68      inference('demod', [status(thm)], ['35', '36'])).
% 43.48/43.68  thf(t88_relat_1, axiom,
% 43.48/43.68    (![A:$i,B:$i]:
% 43.48/43.68     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 43.48/43.68  thf('38', plain,
% 43.48/43.68      (![X34 : $i, X35 : $i]:
% 43.48/43.68         ((r1_tarski @ (k7_relat_1 @ X34 @ X35) @ X34) | ~ (v1_relat_1 @ X34))),
% 43.48/43.68      inference('cnf', [status(esa)], [t88_relat_1])).
% 43.48/43.68  thf('39', plain, (((r1_tarski @ sk_D @ sk_D) | ~ (v1_relat_1 @ sk_D))),
% 43.48/43.68      inference('sup+', [status(thm)], ['37', '38'])).
% 43.48/43.68  thf('40', plain, ((v1_relat_1 @ sk_D)),
% 43.48/43.68      inference('demod', [status(thm)], ['15', '16'])).
% 43.48/43.68  thf('41', plain, ((r1_tarski @ sk_D @ sk_D)),
% 43.48/43.68      inference('demod', [status(thm)], ['39', '40'])).
% 43.48/43.68  thf('42', plain,
% 43.48/43.68      (![X34 : $i, X35 : $i]:
% 43.48/43.68         ((r1_tarski @ (k7_relat_1 @ X34 @ X35) @ X34) | ~ (v1_relat_1 @ X34))),
% 43.48/43.68      inference('cnf', [status(esa)], [t88_relat_1])).
% 43.48/43.68  thf(t1_xboole_1, axiom,
% 43.48/43.68    (![A:$i,B:$i,C:$i]:
% 43.48/43.68     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 43.48/43.68       ( r1_tarski @ A @ C ) ))).
% 43.48/43.68  thf('43', plain,
% 43.48/43.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.48/43.68         (~ (r1_tarski @ X0 @ X1)
% 43.48/43.68          | ~ (r1_tarski @ X1 @ X2)
% 43.48/43.68          | (r1_tarski @ X0 @ X2))),
% 43.48/43.68      inference('cnf', [status(esa)], [t1_xboole_1])).
% 43.48/43.68  thf('44', plain,
% 43.48/43.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.48/43.68         (~ (v1_relat_1 @ X0)
% 43.48/43.68          | (r1_tarski @ (k7_relat_1 @ X0 @ X1) @ X2)
% 43.48/43.68          | ~ (r1_tarski @ X0 @ X2))),
% 43.48/43.68      inference('sup-', [status(thm)], ['42', '43'])).
% 43.48/43.68  thf('45', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         ((r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ sk_D) | ~ (v1_relat_1 @ sk_D))),
% 43.48/43.68      inference('sup-', [status(thm)], ['41', '44'])).
% 43.48/43.68  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 43.48/43.68      inference('demod', [status(thm)], ['15', '16'])).
% 43.48/43.68  thf('47', plain, (![X0 : $i]: (r1_tarski @ (k7_relat_1 @ sk_D @ X0) @ sk_D)),
% 43.48/43.68      inference('demod', [status(thm)], ['45', '46'])).
% 43.48/43.68  thf(t3_subset, axiom,
% 43.48/43.68    (![A:$i,B:$i]:
% 43.48/43.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 43.48/43.68  thf('48', plain,
% 43.48/43.68      (![X8 : $i, X10 : $i]:
% 43.48/43.68         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 43.48/43.68      inference('cnf', [status(esa)], [t3_subset])).
% 43.48/43.68  thf('49', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ (k1_zfmisc_1 @ sk_D))),
% 43.48/43.68      inference('sup-', [status(thm)], ['47', '48'])).
% 43.48/43.68  thf('50', plain,
% 43.48/43.68      (![X14 : $i, X15 : $i]:
% 43.48/43.68         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 43.48/43.68          | (v1_relat_1 @ X14)
% 43.48/43.68          | ~ (v1_relat_1 @ X15))),
% 43.48/43.68      inference('cnf', [status(esa)], [cc2_relat_1])).
% 43.48/43.68  thf('51', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         (~ (v1_relat_1 @ sk_D) | (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 43.48/43.68      inference('sup-', [status(thm)], ['49', '50'])).
% 43.48/43.68  thf('52', plain, ((v1_relat_1 @ sk_D)),
% 43.48/43.68      inference('demod', [status(thm)], ['15', '16'])).
% 43.48/43.68  thf('53', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 43.48/43.68      inference('demod', [status(thm)], ['51', '52'])).
% 43.48/43.68  thf('54', plain,
% 43.48/43.68      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0)),
% 43.48/43.68      inference('demod', [status(thm)], ['28', '53'])).
% 43.48/43.68  thf('55', plain,
% 43.48/43.68      (![X34 : $i, X35 : $i]:
% 43.48/43.68         ((r1_tarski @ (k7_relat_1 @ X34 @ X35) @ X34) | ~ (v1_relat_1 @ X34))),
% 43.48/43.68      inference('cnf', [status(esa)], [t88_relat_1])).
% 43.48/43.68  thf('56', plain,
% 43.48/43.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 43.48/43.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.48/43.68  thf(t4_relset_1, axiom,
% 43.48/43.68    (![A:$i,B:$i,C:$i,D:$i]:
% 43.48/43.68     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 43.48/43.68       ( ( r1_tarski @ A @ D ) =>
% 43.48/43.68         ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 43.48/43.68  thf('57', plain,
% 43.48/43.68      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 43.48/43.68         ((m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57)))
% 43.48/43.68          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57)))
% 43.48/43.68          | ~ (r1_tarski @ X55 @ X58))),
% 43.48/43.68      inference('cnf', [status(esa)], [t4_relset_1])).
% 43.48/43.68  thf('58', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         (~ (r1_tarski @ X0 @ sk_D)
% 43.48/43.68          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 43.48/43.68      inference('sup-', [status(thm)], ['56', '57'])).
% 43.48/43.68  thf('59', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         (~ (v1_relat_1 @ sk_D)
% 43.48/43.68          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 43.48/43.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))))),
% 43.48/43.68      inference('sup-', [status(thm)], ['55', '58'])).
% 43.48/43.68  thf('60', plain, ((v1_relat_1 @ sk_D)),
% 43.48/43.68      inference('demod', [status(thm)], ['15', '16'])).
% 43.48/43.68  thf('61', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 43.48/43.68          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 43.48/43.68      inference('demod', [status(thm)], ['59', '60'])).
% 43.48/43.68  thf(t13_relset_1, axiom,
% 43.48/43.68    (![A:$i,B:$i,C:$i,D:$i]:
% 43.48/43.68     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 43.48/43.68       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 43.48/43.68         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 43.48/43.68  thf('62', plain,
% 43.48/43.68      (![X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 43.48/43.68         (~ (r1_tarski @ (k1_relat_1 @ X51) @ X52)
% 43.48/43.68          | (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X53)))
% 43.48/43.68          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X53))))),
% 43.48/43.68      inference('cnf', [status(esa)], [t13_relset_1])).
% 43.48/43.68  thf('63', plain,
% 43.48/43.68      (![X0 : $i, X1 : $i]:
% 43.48/43.68         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 43.48/43.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 43.48/43.68          | ~ (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X1))),
% 43.48/43.68      inference('sup-', [status(thm)], ['61', '62'])).
% 43.48/43.68  thf('64', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 43.48/43.68          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 43.48/43.68      inference('sup-', [status(thm)], ['54', '63'])).
% 43.48/43.68  thf('65', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         ((k2_partfun1 @ sk_A @ sk_B @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 43.48/43.68      inference('demod', [status(thm)], ['4', '5'])).
% 43.48/43.68  thf('66', plain,
% 43.48/43.68      ((~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 43.48/43.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 43.48/43.68         <= (~
% 43.48/43.68             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 43.48/43.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 43.48/43.68      inference('split', [status(esa)], ['0'])).
% 43.48/43.68  thf('67', plain,
% 43.48/43.68      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_C) @ 
% 43.48/43.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 43.48/43.68         <= (~
% 43.48/43.68             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 43.48/43.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 43.48/43.68      inference('sup-', [status(thm)], ['65', '66'])).
% 43.48/43.68  thf('68', plain,
% 43.48/43.68      (((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 43.48/43.68         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))),
% 43.48/43.68      inference('sup-', [status(thm)], ['64', '67'])).
% 43.48/43.68  thf('69', plain,
% 43.48/43.68      (~
% 43.48/43.68       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B)) | 
% 43.48/43.68       ~
% 43.48/43.68       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 43.48/43.68         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) | 
% 43.48/43.68       ~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C)))),
% 43.48/43.68      inference('split', [status(esa)], ['0'])).
% 43.48/43.68  thf('70', plain,
% 43.48/43.68      (~
% 43.48/43.68       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 43.48/43.68      inference('sat_resolution*', [status(thm)], ['19', '68', '69'])).
% 43.48/43.68  thf('71', plain, (~ (v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 43.48/43.68      inference('simpl_trail', [status(thm)], ['7', '70'])).
% 43.48/43.68  thf(d1_funct_2, axiom,
% 43.48/43.68    (![A:$i,B:$i,C:$i]:
% 43.48/43.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 43.48/43.68       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 43.48/43.68           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 43.48/43.68             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 43.48/43.68         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 43.48/43.68           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 43.48/43.68             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 43.48/43.68  thf(zf_stmt_1, axiom,
% 43.48/43.68    (![B:$i,A:$i]:
% 43.48/43.68     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 43.48/43.68       ( zip_tseitin_0 @ B @ A ) ))).
% 43.48/43.68  thf('72', plain,
% 43.48/43.68      (![X59 : $i, X60 : $i]:
% 43.48/43.68         ((zip_tseitin_0 @ X59 @ X60) | ((X59) = (k1_xboole_0)))),
% 43.48/43.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 43.48/43.68  thf('73', plain,
% 43.48/43.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 43.48/43.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.48/43.68  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 43.48/43.68  thf(zf_stmt_3, axiom,
% 43.48/43.68    (![C:$i,B:$i,A:$i]:
% 43.48/43.68     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 43.48/43.68       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 43.48/43.68  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 43.48/43.68  thf(zf_stmt_5, axiom,
% 43.48/43.68    (![A:$i,B:$i,C:$i]:
% 43.48/43.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 43.48/43.68       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 43.48/43.68         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 43.48/43.68           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 43.48/43.68             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 43.48/43.68  thf('74', plain,
% 43.48/43.68      (![X64 : $i, X65 : $i, X66 : $i]:
% 43.48/43.68         (~ (zip_tseitin_0 @ X64 @ X65)
% 43.48/43.68          | (zip_tseitin_1 @ X66 @ X64 @ X65)
% 43.48/43.68          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X64))))),
% 43.48/43.68      inference('cnf', [status(esa)], [zf_stmt_5])).
% 43.48/43.68  thf('75', plain,
% 43.48/43.68      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 43.48/43.68      inference('sup-', [status(thm)], ['73', '74'])).
% 43.48/43.68  thf('76', plain,
% 43.48/43.68      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 43.48/43.68      inference('sup-', [status(thm)], ['72', '75'])).
% 43.48/43.68  thf('77', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 43.48/43.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.48/43.68  thf('78', plain,
% 43.48/43.68      (![X61 : $i, X62 : $i, X63 : $i]:
% 43.48/43.68         (~ (v1_funct_2 @ X63 @ X61 @ X62)
% 43.48/43.68          | ((X61) = (k1_relset_1 @ X61 @ X62 @ X63))
% 43.48/43.68          | ~ (zip_tseitin_1 @ X63 @ X62 @ X61))),
% 43.48/43.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 43.48/43.68  thf('79', plain,
% 43.48/43.68      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 43.48/43.68        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 43.48/43.68      inference('sup-', [status(thm)], ['77', '78'])).
% 43.48/43.68  thf('80', plain,
% 43.48/43.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 43.48/43.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.48/43.68  thf(redefinition_k1_relset_1, axiom,
% 43.48/43.68    (![A:$i,B:$i,C:$i]:
% 43.48/43.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 43.48/43.68       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 43.48/43.68  thf('81', plain,
% 43.48/43.68      (![X48 : $i, X49 : $i, X50 : $i]:
% 43.48/43.68         (((k1_relset_1 @ X49 @ X50 @ X48) = (k1_relat_1 @ X48))
% 43.48/43.68          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50))))),
% 43.48/43.68      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 43.48/43.68  thf('82', plain,
% 43.48/43.68      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 43.48/43.68      inference('sup-', [status(thm)], ['80', '81'])).
% 43.48/43.68  thf('83', plain,
% 43.48/43.68      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 43.48/43.68      inference('demod', [status(thm)], ['79', '82'])).
% 43.48/43.68  thf('84', plain,
% 43.48/43.68      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 43.48/43.68      inference('sup-', [status(thm)], ['76', '83'])).
% 43.48/43.68  thf('85', plain, ((v4_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))),
% 43.48/43.68      inference('demod', [status(thm)], ['31', '32'])).
% 43.48/43.68  thf('86', plain,
% 43.48/43.68      (![X16 : $i, X17 : $i]:
% 43.48/43.68         (~ (v4_relat_1 @ X16 @ X17)
% 43.48/43.68          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 43.48/43.68          | ~ (v1_relat_1 @ X16))),
% 43.48/43.68      inference('cnf', [status(esa)], [d18_relat_1])).
% 43.48/43.68  thf('87', plain,
% 43.48/43.68      ((~ (v1_relat_1 @ sk_D)
% 43.48/43.68        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_relat_1 @ sk_D)))),
% 43.48/43.68      inference('sup-', [status(thm)], ['85', '86'])).
% 43.48/43.68  thf('88', plain, ((v1_relat_1 @ sk_D)),
% 43.48/43.68      inference('demod', [status(thm)], ['15', '16'])).
% 43.48/43.68  thf('89', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_relat_1 @ sk_D))),
% 43.48/43.68      inference('demod', [status(thm)], ['87', '88'])).
% 43.48/43.68  thf('90', plain,
% 43.48/43.68      (((r1_tarski @ sk_A @ (k1_relat_1 @ sk_D)) | ((sk_B) = (k1_xboole_0)))),
% 43.48/43.68      inference('sup+', [status(thm)], ['84', '89'])).
% 43.48/43.68  thf('91', plain, ((r1_tarski @ sk_C @ sk_A)),
% 43.48/43.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.48/43.68  thf('92', plain,
% 43.48/43.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.48/43.68         (~ (r1_tarski @ X0 @ X1)
% 43.48/43.68          | ~ (r1_tarski @ X1 @ X2)
% 43.48/43.68          | (r1_tarski @ X0 @ X2))),
% 43.48/43.68      inference('cnf', [status(esa)], [t1_xboole_1])).
% 43.48/43.68  thf('93', plain,
% 43.48/43.68      (![X0 : $i]: ((r1_tarski @ sk_C @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 43.48/43.68      inference('sup-', [status(thm)], ['91', '92'])).
% 43.48/43.68  thf('94', plain,
% 43.48/43.68      ((((sk_B) = (k1_xboole_0)) | (r1_tarski @ sk_C @ (k1_relat_1 @ sk_D)))),
% 43.48/43.68      inference('sup-', [status(thm)], ['90', '93'])).
% 43.48/43.68  thf(t91_relat_1, axiom,
% 43.48/43.68    (![A:$i,B:$i]:
% 43.48/43.68     ( ( v1_relat_1 @ B ) =>
% 43.48/43.68       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 43.48/43.68         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 43.48/43.68  thf('95', plain,
% 43.48/43.68      (![X38 : $i, X39 : $i]:
% 43.48/43.68         (~ (r1_tarski @ X38 @ (k1_relat_1 @ X39))
% 43.48/43.68          | ((k1_relat_1 @ (k7_relat_1 @ X39 @ X38)) = (X38))
% 43.48/43.68          | ~ (v1_relat_1 @ X39))),
% 43.48/43.68      inference('cnf', [status(esa)], [t91_relat_1])).
% 43.48/43.68  thf('96', plain,
% 43.48/43.68      ((((sk_B) = (k1_xboole_0))
% 43.48/43.68        | ~ (v1_relat_1 @ sk_D)
% 43.48/43.68        | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C)))),
% 43.48/43.68      inference('sup-', [status(thm)], ['94', '95'])).
% 43.48/43.68  thf('97', plain, ((v1_relat_1 @ sk_D)),
% 43.48/43.68      inference('demod', [status(thm)], ['15', '16'])).
% 43.48/43.68  thf('98', plain,
% 43.48/43.68      ((((sk_B) = (k1_xboole_0))
% 43.48/43.68        | ((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C)))),
% 43.48/43.68      inference('demod', [status(thm)], ['96', '97'])).
% 43.48/43.68  thf('99', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 43.48/43.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.48/43.68  thf('100', plain,
% 43.48/43.68      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 43.48/43.68      inference('split', [status(esa)], ['99'])).
% 43.48/43.68  thf('101', plain,
% 43.48/43.68      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('split', [status(esa)], ['99'])).
% 43.48/43.68  thf('102', plain,
% 43.48/43.68      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 43.48/43.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.48/43.68  thf('103', plain,
% 43.48/43.68      (((m1_subset_1 @ sk_D @ 
% 43.48/43.68         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 43.48/43.68         <= ((((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('sup+', [status(thm)], ['101', '102'])).
% 43.48/43.68  thf(t113_zfmisc_1, axiom,
% 43.48/43.68    (![A:$i,B:$i]:
% 43.48/43.68     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 43.48/43.68       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 43.48/43.68  thf('104', plain,
% 43.48/43.68      (![X5 : $i, X6 : $i]:
% 43.48/43.68         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 43.48/43.68      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 43.48/43.68  thf('105', plain,
% 43.48/43.68      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 43.48/43.68      inference('simplify', [status(thm)], ['104'])).
% 43.48/43.68  thf('106', plain,
% 43.48/43.68      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 43.48/43.68         <= ((((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('demod', [status(thm)], ['103', '105'])).
% 43.48/43.68  thf('107', plain,
% 43.48/43.68      (![X8 : $i, X9 : $i]:
% 43.48/43.68         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 43.48/43.68      inference('cnf', [status(esa)], [t3_subset])).
% 43.48/43.68  thf('108', plain,
% 43.48/43.68      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('sup-', [status(thm)], ['106', '107'])).
% 43.48/43.68  thf(t3_xboole_1, axiom,
% 43.48/43.68    (![A:$i]:
% 43.48/43.68     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 43.48/43.68  thf('109', plain,
% 43.48/43.68      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 43.48/43.68      inference('cnf', [status(esa)], [t3_xboole_1])).
% 43.48/43.68  thf('110', plain,
% 43.48/43.68      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('sup-', [status(thm)], ['108', '109'])).
% 43.48/43.68  thf('111', plain, ((v1_funct_1 @ sk_D)),
% 43.48/43.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.48/43.68  thf('112', plain,
% 43.48/43.68      (((v1_funct_1 @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('sup+', [status(thm)], ['110', '111'])).
% 43.48/43.68  thf(t4_subset_1, axiom,
% 43.48/43.68    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 43.48/43.68  thf('113', plain,
% 43.48/43.68      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 43.48/43.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 43.48/43.68  thf('114', plain,
% 43.48/43.68      (![X67 : $i, X68 : $i, X69 : $i, X70 : $i]:
% 43.48/43.68         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X68 @ X69)))
% 43.48/43.68          | ~ (v1_funct_1 @ X67)
% 43.48/43.68          | ((k2_partfun1 @ X68 @ X69 @ X67 @ X70) = (k7_relat_1 @ X67 @ X70)))),
% 43.48/43.68      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 43.48/43.68  thf('115', plain,
% 43.48/43.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.48/43.68         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 43.48/43.68            = (k7_relat_1 @ k1_xboole_0 @ X2))
% 43.48/43.68          | ~ (v1_funct_1 @ k1_xboole_0))),
% 43.48/43.68      inference('sup-', [status(thm)], ['113', '114'])).
% 43.48/43.68  thf('116', plain,
% 43.48/43.68      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 43.48/43.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 43.48/43.68  thf('117', plain,
% 43.48/43.68      (![X45 : $i, X46 : $i, X47 : $i]:
% 43.48/43.68         ((v4_relat_1 @ X45 @ X46)
% 43.48/43.68          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47))))),
% 43.48/43.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 43.48/43.68  thf('118', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 43.48/43.68      inference('sup-', [status(thm)], ['116', '117'])).
% 43.48/43.68  thf('119', plain,
% 43.48/43.68      (![X30 : $i, X31 : $i]:
% 43.48/43.68         (((X30) = (k7_relat_1 @ X30 @ X31))
% 43.48/43.68          | ~ (v4_relat_1 @ X30 @ X31)
% 43.48/43.68          | ~ (v1_relat_1 @ X30))),
% 43.48/43.68      inference('cnf', [status(esa)], [t209_relat_1])).
% 43.48/43.68  thf('120', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         (~ (v1_relat_1 @ k1_xboole_0)
% 43.48/43.68          | ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0)))),
% 43.48/43.68      inference('sup-', [status(thm)], ['118', '119'])).
% 43.48/43.68  thf('121', plain,
% 43.48/43.68      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 43.48/43.68      inference('simplify', [status(thm)], ['104'])).
% 43.48/43.68  thf('122', plain,
% 43.48/43.68      (![X25 : $i, X26 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X25 @ X26))),
% 43.48/43.68      inference('cnf', [status(esa)], [fc6_relat_1])).
% 43.48/43.68  thf('123', plain, ((v1_relat_1 @ k1_xboole_0)),
% 43.48/43.68      inference('sup+', [status(thm)], ['121', '122'])).
% 43.48/43.68  thf('124', plain,
% 43.48/43.68      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 43.48/43.68      inference('demod', [status(thm)], ['120', '123'])).
% 43.48/43.68  thf('125', plain,
% 43.48/43.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.48/43.68         (((k2_partfun1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))
% 43.48/43.68          | ~ (v1_funct_1 @ k1_xboole_0))),
% 43.48/43.68      inference('demod', [status(thm)], ['115', '124'])).
% 43.48/43.68  thf('126', plain,
% 43.48/43.68      ((![X0 : $i, X1 : $i, X2 : $i]:
% 43.48/43.68          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 43.48/43.68         <= ((((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('sup-', [status(thm)], ['112', '125'])).
% 43.48/43.68  thf('127', plain,
% 43.48/43.68      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('split', [status(esa)], ['99'])).
% 43.48/43.68  thf('128', plain,
% 43.48/43.68      ((~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 43.48/43.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 43.48/43.68         <= (~
% 43.48/43.68             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 43.48/43.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))))),
% 43.48/43.68      inference('split', [status(esa)], ['0'])).
% 43.48/43.68  thf('129', plain,
% 43.48/43.68      ((~ (m1_subset_1 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C) @ 
% 43.48/43.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B))))
% 43.48/43.68         <= (~
% 43.48/43.68             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 43.48/43.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) & 
% 43.48/43.68             (((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('sup-', [status(thm)], ['127', '128'])).
% 43.48/43.68  thf('130', plain,
% 43.48/43.68      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('sup-', [status(thm)], ['108', '109'])).
% 43.48/43.68  thf('131', plain,
% 43.48/43.68      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('split', [status(esa)], ['99'])).
% 43.48/43.68  thf('132', plain, ((r1_tarski @ sk_C @ sk_A)),
% 43.48/43.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.48/43.68  thf('133', plain,
% 43.48/43.68      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('sup+', [status(thm)], ['131', '132'])).
% 43.48/43.68  thf('134', plain,
% 43.48/43.68      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 43.48/43.68      inference('cnf', [status(esa)], [t3_xboole_1])).
% 43.48/43.68  thf('135', plain,
% 43.48/43.68      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('sup-', [status(thm)], ['133', '134'])).
% 43.48/43.68  thf('136', plain,
% 43.48/43.68      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('sup-', [status(thm)], ['133', '134'])).
% 43.48/43.68  thf('137', plain,
% 43.48/43.68      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 43.48/43.68      inference('simplify', [status(thm)], ['104'])).
% 43.48/43.68  thf('138', plain,
% 43.48/43.68      ((~ (m1_subset_1 @ 
% 43.48/43.68           (k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0) @ 
% 43.48/43.68           (k1_zfmisc_1 @ k1_xboole_0)))
% 43.48/43.68         <= (~
% 43.48/43.68             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 43.48/43.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) & 
% 43.48/43.68             (((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('demod', [status(thm)], ['129', '130', '135', '136', '137'])).
% 43.48/43.68  thf('139', plain,
% 43.48/43.68      ((~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ k1_xboole_0)))
% 43.48/43.68         <= (~
% 43.48/43.68             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 43.48/43.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) & 
% 43.48/43.68             (((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('sup-', [status(thm)], ['126', '138'])).
% 43.48/43.68  thf('140', plain,
% 43.48/43.68      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 43.48/43.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 43.48/43.68  thf('141', plain,
% 43.48/43.68      (((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ 
% 43.48/43.68         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))) | 
% 43.48/43.68       ~ (((sk_A) = (k1_xboole_0)))),
% 43.48/43.68      inference('demod', [status(thm)], ['139', '140'])).
% 43.48/43.68  thf('142', plain,
% 43.48/43.68      ((![X0 : $i, X1 : $i, X2 : $i]:
% 43.48/43.68          ((k2_partfun1 @ X2 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))
% 43.48/43.68         <= ((((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('sup-', [status(thm)], ['112', '125'])).
% 43.48/43.68  thf('143', plain,
% 43.48/43.68      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('sup-', [status(thm)], ['108', '109'])).
% 43.48/43.68  thf('144', plain,
% 43.48/43.68      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('split', [status(esa)], ['99'])).
% 43.48/43.68  thf('145', plain,
% 43.48/43.68      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B))
% 43.48/43.68         <= (~
% 43.48/43.68             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 43.48/43.68               sk_B)))),
% 43.48/43.68      inference('split', [status(esa)], ['0'])).
% 43.48/43.68  thf('146', plain,
% 43.48/43.68      ((~ (v1_funct_2 @ (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ sk_C) @ 
% 43.48/43.68           sk_C @ sk_B))
% 43.48/43.68         <= (~
% 43.48/43.68             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 43.48/43.68               sk_B)) & 
% 43.48/43.68             (((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('sup-', [status(thm)], ['144', '145'])).
% 43.48/43.68  thf('147', plain,
% 43.48/43.68      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('sup-', [status(thm)], ['133', '134'])).
% 43.48/43.68  thf('148', plain,
% 43.48/43.68      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('sup-', [status(thm)], ['133', '134'])).
% 43.48/43.68  thf('149', plain,
% 43.48/43.68      ((~ (v1_funct_2 @ 
% 43.48/43.68           (k2_partfun1 @ k1_xboole_0 @ sk_B @ sk_D @ k1_xboole_0) @ 
% 43.48/43.68           k1_xboole_0 @ sk_B))
% 43.48/43.68         <= (~
% 43.48/43.68             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 43.48/43.68               sk_B)) & 
% 43.48/43.68             (((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('demod', [status(thm)], ['146', '147', '148'])).
% 43.48/43.68  thf('150', plain,
% 43.48/43.68      ((~ (v1_funct_2 @ 
% 43.48/43.68           (k2_partfun1 @ k1_xboole_0 @ sk_B @ k1_xboole_0 @ k1_xboole_0) @ 
% 43.48/43.68           k1_xboole_0 @ sk_B))
% 43.48/43.68         <= (~
% 43.48/43.68             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 43.48/43.68               sk_B)) & 
% 43.48/43.68             (((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('sup-', [status(thm)], ['143', '149'])).
% 43.48/43.68  thf('151', plain,
% 43.48/43.68      ((~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_B))
% 43.48/43.68         <= (~
% 43.48/43.68             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ 
% 43.48/43.68               sk_B)) & 
% 43.48/43.68             (((sk_A) = (k1_xboole_0))))),
% 43.48/43.68      inference('sup-', [status(thm)], ['142', '150'])).
% 43.48/43.68  thf('152', plain,
% 43.48/43.68      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 43.48/43.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 43.48/43.68  thf('153', plain,
% 43.48/43.68      (![X48 : $i, X49 : $i, X50 : $i]:
% 43.48/43.68         (((k1_relset_1 @ X49 @ X50 @ X48) = (k1_relat_1 @ X48))
% 43.48/43.68          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X49 @ X50))))),
% 43.48/43.68      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 43.48/43.68  thf('154', plain,
% 43.48/43.68      (![X0 : $i, X1 : $i]:
% 43.48/43.68         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 43.48/43.68      inference('sup-', [status(thm)], ['152', '153'])).
% 43.48/43.68  thf('155', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 43.48/43.68      inference('sup-', [status(thm)], ['116', '117'])).
% 43.48/43.68  thf('156', plain,
% 43.48/43.68      (![X16 : $i, X17 : $i]:
% 43.48/43.68         (~ (v4_relat_1 @ X16 @ X17)
% 43.48/43.68          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 43.48/43.68          | ~ (v1_relat_1 @ X16))),
% 43.48/43.68      inference('cnf', [status(esa)], [d18_relat_1])).
% 43.48/43.68  thf('157', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         (~ (v1_relat_1 @ k1_xboole_0)
% 43.48/43.68          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 43.48/43.68      inference('sup-', [status(thm)], ['155', '156'])).
% 43.48/43.68  thf('158', plain, ((v1_relat_1 @ k1_xboole_0)),
% 43.48/43.68      inference('sup+', [status(thm)], ['121', '122'])).
% 43.48/43.68  thf('159', plain,
% 43.48/43.68      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 43.48/43.68      inference('demod', [status(thm)], ['157', '158'])).
% 43.48/43.68  thf('160', plain,
% 43.48/43.68      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 43.48/43.68      inference('cnf', [status(esa)], [t3_xboole_1])).
% 43.48/43.68  thf('161', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 43.48/43.68      inference('sup-', [status(thm)], ['159', '160'])).
% 43.48/43.68  thf('162', plain,
% 43.48/43.68      (![X0 : $i, X1 : $i]:
% 43.48/43.68         ((k1_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 43.48/43.68      inference('demod', [status(thm)], ['154', '161'])).
% 43.48/43.68  thf('163', plain,
% 43.48/43.68      (![X61 : $i, X62 : $i, X63 : $i]:
% 43.48/43.68         (((X61) != (k1_relset_1 @ X61 @ X62 @ X63))
% 43.48/43.68          | (v1_funct_2 @ X63 @ X61 @ X62)
% 43.48/43.68          | ~ (zip_tseitin_1 @ X63 @ X62 @ X61))),
% 43.48/43.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 43.48/43.68  thf('164', plain,
% 43.48/43.68      (![X0 : $i, X1 : $i]:
% 43.48/43.68         (((X1) != (k1_xboole_0))
% 43.48/43.68          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1)
% 43.48/43.68          | (v1_funct_2 @ k1_xboole_0 @ X1 @ X0))),
% 43.48/43.68      inference('sup-', [status(thm)], ['162', '163'])).
% 43.48/43.68  thf('165', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)
% 43.48/43.68          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 43.48/43.68      inference('simplify', [status(thm)], ['164'])).
% 43.48/43.68  thf('166', plain,
% 43.48/43.68      (![X59 : $i, X60 : $i]:
% 43.48/43.68         ((zip_tseitin_0 @ X59 @ X60) | ((X60) != (k1_xboole_0)))),
% 43.48/43.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 43.48/43.68  thf('167', plain, (![X59 : $i]: (zip_tseitin_0 @ X59 @ k1_xboole_0)),
% 43.48/43.68      inference('simplify', [status(thm)], ['166'])).
% 43.48/43.68  thf('168', plain,
% 43.48/43.68      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 43.48/43.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 43.48/43.68  thf('169', plain,
% 43.48/43.68      (![X64 : $i, X65 : $i, X66 : $i]:
% 43.48/43.68         (~ (zip_tseitin_0 @ X64 @ X65)
% 43.48/43.68          | (zip_tseitin_1 @ X66 @ X64 @ X65)
% 43.48/43.68          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X64))))),
% 43.48/43.68      inference('cnf', [status(esa)], [zf_stmt_5])).
% 43.48/43.68  thf('170', plain,
% 43.48/43.68      (![X0 : $i, X1 : $i]:
% 43.48/43.68         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 43.48/43.68      inference('sup-', [status(thm)], ['168', '169'])).
% 43.48/43.68  thf('171', plain,
% 43.48/43.68      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 43.48/43.68      inference('sup-', [status(thm)], ['167', '170'])).
% 43.48/43.68  thf('172', plain,
% 43.48/43.68      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 43.48/43.68      inference('demod', [status(thm)], ['165', '171'])).
% 43.48/43.68  thf('173', plain,
% 43.48/43.68      (~ (((sk_A) = (k1_xboole_0))) | 
% 43.48/43.68       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_B @ sk_D @ sk_C) @ sk_C @ sk_B))),
% 43.48/43.68      inference('demod', [status(thm)], ['151', '172'])).
% 43.48/43.68  thf('174', plain,
% 43.48/43.68      (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 43.48/43.68      inference('split', [status(esa)], ['99'])).
% 43.48/43.68  thf('175', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 43.48/43.68      inference('sat_resolution*', [status(thm)],
% 43.48/43.68                ['19', '141', '173', '69', '174'])).
% 43.48/43.68  thf('176', plain, (((sk_B) != (k1_xboole_0))),
% 43.48/43.68      inference('simpl_trail', [status(thm)], ['100', '175'])).
% 43.48/43.68  thf('177', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_D @ sk_C)) = (sk_C))),
% 43.48/43.68      inference('simplify_reflect-', [status(thm)], ['98', '176'])).
% 43.48/43.68  thf('178', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 43.48/43.68          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 43.48/43.68      inference('demod', [status(thm)], ['59', '60'])).
% 43.48/43.68  thf('179', plain,
% 43.48/43.68      (![X45 : $i, X46 : $i, X47 : $i]:
% 43.48/43.68         ((v5_relat_1 @ X45 @ X47)
% 43.48/43.68          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47))))),
% 43.48/43.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 43.48/43.68  thf('180', plain,
% 43.48/43.68      (![X0 : $i]: (v5_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ sk_B)),
% 43.48/43.68      inference('sup-', [status(thm)], ['178', '179'])).
% 43.48/43.68  thf(d19_relat_1, axiom,
% 43.48/43.68    (![A:$i,B:$i]:
% 43.48/43.68     ( ( v1_relat_1 @ B ) =>
% 43.48/43.68       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 43.48/43.68  thf('181', plain,
% 43.48/43.68      (![X18 : $i, X19 : $i]:
% 43.48/43.68         (~ (v5_relat_1 @ X18 @ X19)
% 43.48/43.68          | (r1_tarski @ (k2_relat_1 @ X18) @ X19)
% 43.48/43.68          | ~ (v1_relat_1 @ X18))),
% 43.48/43.68      inference('cnf', [status(esa)], [d19_relat_1])).
% 43.48/43.68  thf('182', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 43.48/43.68          | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 43.48/43.68      inference('sup-', [status(thm)], ['180', '181'])).
% 43.48/43.68  thf('183', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 43.48/43.68      inference('demod', [status(thm)], ['51', '52'])).
% 43.48/43.68  thf('184', plain,
% 43.48/43.68      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 43.48/43.68      inference('demod', [status(thm)], ['182', '183'])).
% 43.48/43.68  thf(t4_funct_2, axiom,
% 43.48/43.68    (![A:$i,B:$i]:
% 43.48/43.68     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 43.48/43.68       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 43.48/43.68         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 43.48/43.68           ( m1_subset_1 @
% 43.48/43.68             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 43.48/43.68  thf('185', plain,
% 43.48/43.68      (![X71 : $i, X72 : $i]:
% 43.48/43.68         (~ (r1_tarski @ (k2_relat_1 @ X71) @ X72)
% 43.48/43.68          | (v1_funct_2 @ X71 @ (k1_relat_1 @ X71) @ X72)
% 43.48/43.68          | ~ (v1_funct_1 @ X71)
% 43.48/43.68          | ~ (v1_relat_1 @ X71))),
% 43.48/43.68      inference('cnf', [status(esa)], [t4_funct_2])).
% 43.48/43.68  thf('186', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 43.48/43.68          | ~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 43.48/43.68          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 43.48/43.68             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 43.48/43.68      inference('sup-', [status(thm)], ['184', '185'])).
% 43.48/43.68  thf('187', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 43.48/43.68      inference('demod', [status(thm)], ['51', '52'])).
% 43.48/43.68  thf('188', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         (~ (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 43.48/43.68          | (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 43.48/43.68             (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B))),
% 43.48/43.68      inference('demod', [status(thm)], ['186', '187'])).
% 43.48/43.68  thf(t87_relat_1, axiom,
% 43.48/43.68    (![A:$i,B:$i]:
% 43.48/43.68     ( ( v1_relat_1 @ B ) =>
% 43.48/43.68       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 43.48/43.68  thf('189', plain,
% 43.48/43.68      (![X32 : $i, X33 : $i]:
% 43.48/43.68         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X32 @ X33)) @ X33)
% 43.48/43.68          | ~ (v1_relat_1 @ X32))),
% 43.48/43.68      inference('cnf', [status(esa)], [t87_relat_1])).
% 43.48/43.68  thf(t103_relat_1, axiom,
% 43.48/43.68    (![A:$i,B:$i,C:$i]:
% 43.48/43.68     ( ( v1_relat_1 @ C ) =>
% 43.48/43.68       ( ( r1_tarski @ A @ B ) =>
% 43.48/43.68         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 43.48/43.68  thf('190', plain,
% 43.48/43.68      (![X27 : $i, X28 : $i, X29 : $i]:
% 43.48/43.68         (~ (r1_tarski @ X27 @ X28)
% 43.48/43.68          | ~ (v1_relat_1 @ X29)
% 43.48/43.68          | ((k7_relat_1 @ (k7_relat_1 @ X29 @ X28) @ X27)
% 43.48/43.68              = (k7_relat_1 @ X29 @ X27)))),
% 43.48/43.68      inference('cnf', [status(esa)], [t103_relat_1])).
% 43.48/43.68  thf('191', plain,
% 43.48/43.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 43.48/43.68         (~ (v1_relat_1 @ X1)
% 43.48/43.68          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ X0) @ 
% 43.48/43.68              (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 43.48/43.68              = (k7_relat_1 @ X2 @ (k1_relat_1 @ (k7_relat_1 @ X1 @ X0))))
% 43.48/43.68          | ~ (v1_relat_1 @ X2))),
% 43.48/43.68      inference('sup-', [status(thm)], ['189', '190'])).
% 43.48/43.68  thf('192', plain, (![X0 : $i]: (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0)),
% 43.48/43.68      inference('demod', [status(thm)], ['24', '25'])).
% 43.48/43.68  thf('193', plain,
% 43.48/43.68      (![X30 : $i, X31 : $i]:
% 43.48/43.68         (((X30) = (k7_relat_1 @ X30 @ X31))
% 43.48/43.68          | ~ (v4_relat_1 @ X30 @ X31)
% 43.48/43.68          | ~ (v1_relat_1 @ X30))),
% 43.48/43.68      inference('cnf', [status(esa)], [t209_relat_1])).
% 43.48/43.68  thf('194', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 43.48/43.68          | ((k7_relat_1 @ sk_D @ X0)
% 43.48/43.68              = (k7_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0)))),
% 43.48/43.68      inference('sup-', [status(thm)], ['192', '193'])).
% 43.48/43.68  thf('195', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 43.48/43.68      inference('demod', [status(thm)], ['51', '52'])).
% 43.48/43.68  thf('196', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         ((k7_relat_1 @ sk_D @ X0)
% 43.48/43.68           = (k7_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0))),
% 43.48/43.68      inference('demod', [status(thm)], ['194', '195'])).
% 43.48/43.68  thf('197', plain,
% 43.48/43.68      (![X40 : $i]:
% 43.48/43.68         (((k7_relat_1 @ X40 @ (k1_relat_1 @ X40)) = (X40))
% 43.48/43.68          | ~ (v1_relat_1 @ X40))),
% 43.48/43.68      inference('cnf', [status(esa)], [t98_relat_1])).
% 43.48/43.68  thf('198', plain,
% 43.48/43.68      (![X32 : $i, X33 : $i]:
% 43.48/43.68         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X32 @ X33)) @ X33)
% 43.48/43.68          | ~ (v1_relat_1 @ X32))),
% 43.48/43.68      inference('cnf', [status(esa)], [t87_relat_1])).
% 43.48/43.68  thf('199', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         ((r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 43.48/43.68          | ~ (v1_relat_1 @ X0)
% 43.48/43.68          | ~ (v1_relat_1 @ X0))),
% 43.48/43.68      inference('sup+', [status(thm)], ['197', '198'])).
% 43.48/43.68  thf('200', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         (~ (v1_relat_1 @ X0)
% 43.48/43.68          | (r1_tarski @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 43.48/43.68      inference('simplify', [status(thm)], ['199'])).
% 43.48/43.68  thf('201', plain,
% 43.48/43.68      (![X16 : $i, X17 : $i]:
% 43.48/43.68         (~ (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 43.48/43.68          | (v4_relat_1 @ X16 @ X17)
% 43.48/43.68          | ~ (v1_relat_1 @ X16))),
% 43.48/43.68      inference('cnf', [status(esa)], [d18_relat_1])).
% 43.48/43.68  thf('202', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         (~ (v1_relat_1 @ X0)
% 43.48/43.68          | ~ (v1_relat_1 @ X0)
% 43.48/43.68          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 43.48/43.68      inference('sup-', [status(thm)], ['200', '201'])).
% 43.48/43.68  thf('203', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         ((v4_relat_1 @ X0 @ (k1_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 43.48/43.68      inference('simplify', [status(thm)], ['202'])).
% 43.48/43.68  thf('204', plain,
% 43.48/43.68      (![X22 : $i, X23 : $i, X24 : $i]:
% 43.48/43.68         ((v4_relat_1 @ (k7_relat_1 @ X22 @ X23) @ X24)
% 43.48/43.68          | ~ (v4_relat_1 @ X22 @ X24)
% 43.48/43.68          | ~ (v1_relat_1 @ X22))),
% 43.48/43.68      inference('cnf', [status(esa)], [fc23_relat_1])).
% 43.48/43.68  thf('205', plain,
% 43.48/43.68      (![X0 : $i, X1 : $i]:
% 43.48/43.68         (~ (v1_relat_1 @ X0)
% 43.48/43.68          | ~ (v1_relat_1 @ X0)
% 43.48/43.68          | (v4_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 43.48/43.68      inference('sup-', [status(thm)], ['203', '204'])).
% 43.48/43.68  thf('206', plain,
% 43.48/43.68      (![X0 : $i, X1 : $i]:
% 43.48/43.68         ((v4_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 43.48/43.68          | ~ (v1_relat_1 @ X0))),
% 43.48/43.68      inference('simplify', [status(thm)], ['205'])).
% 43.48/43.68  thf('207', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         ((v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 43.48/43.68           (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))
% 43.48/43.68          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 43.48/43.68      inference('sup+', [status(thm)], ['196', '206'])).
% 43.48/43.68  thf('208', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 43.48/43.68      inference('demod', [status(thm)], ['51', '52'])).
% 43.48/43.68  thf('209', plain,
% 43.48/43.68      (![X0 : $i]:
% 43.48/43.68         (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 43.48/43.68          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 43.48/43.68      inference('demod', [status(thm)], ['207', '208'])).
% 43.48/43.68  thf('210', plain,
% 43.48/43.68      (![X30 : $i, X31 : $i]:
% 43.48/43.68         (((X30) = (k7_relat_1 @ X30 @ X31))
% 43.48/43.68          | ~ (v4_relat_1 @ X30 @ X31)
% 43.48/43.68          | ~ (v1_relat_1 @ X30))),
% 43.48/43.68      inference('cnf', [status(esa)], [t209_relat_1])).
% 43.48/43.69  thf('211', plain,
% 43.48/43.69      (![X0 : $i]:
% 43.48/43.69         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 43.48/43.69          | ((k7_relat_1 @ sk_D @ X0)
% 43.48/43.69              = (k7_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 43.48/43.69                 (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))))),
% 43.48/43.69      inference('sup-', [status(thm)], ['209', '210'])).
% 43.48/43.69  thf('212', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 43.48/43.69      inference('demod', [status(thm)], ['51', '52'])).
% 43.48/43.69  thf('213', plain,
% 43.48/43.69      (![X0 : $i]:
% 43.48/43.69         ((k7_relat_1 @ sk_D @ X0)
% 43.48/43.69           = (k7_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 43.48/43.69              (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0))))),
% 43.48/43.69      inference('demod', [status(thm)], ['211', '212'])).
% 43.48/43.69  thf('214', plain,
% 43.48/43.69      (![X0 : $i]:
% 43.48/43.69         (((k7_relat_1 @ sk_D @ X0)
% 43.48/43.69            = (k7_relat_1 @ sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0))))
% 43.48/43.69          | ~ (v1_relat_1 @ sk_D)
% 43.48/43.69          | ~ (v1_relat_1 @ sk_D))),
% 43.48/43.69      inference('sup+', [status(thm)], ['191', '213'])).
% 43.48/43.69  thf('215', plain, ((v1_relat_1 @ sk_D)),
% 43.48/43.69      inference('demod', [status(thm)], ['15', '16'])).
% 43.48/43.69  thf('216', plain, ((v1_relat_1 @ sk_D)),
% 43.48/43.69      inference('demod', [status(thm)], ['15', '16'])).
% 43.48/43.69  thf('217', plain,
% 43.48/43.69      (![X0 : $i]:
% 43.48/43.69         ((k7_relat_1 @ sk_D @ X0)
% 43.48/43.69           = (k7_relat_1 @ sk_D @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0))))),
% 43.48/43.69      inference('demod', [status(thm)], ['214', '215', '216'])).
% 43.48/43.69  thf('218', plain,
% 43.48/43.69      (![X43 : $i, X44 : $i]:
% 43.48/43.69         (~ (v1_funct_1 @ X43)
% 43.48/43.69          | ~ (v1_relat_1 @ X43)
% 43.48/43.69          | (v1_funct_1 @ (k7_relat_1 @ X43 @ X44)))),
% 43.48/43.69      inference('cnf', [status(esa)], [fc8_funct_1])).
% 43.48/43.69  thf('219', plain,
% 43.48/43.69      (![X0 : $i]:
% 43.48/43.69         ((v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))
% 43.48/43.69          | ~ (v1_relat_1 @ sk_D)
% 43.48/43.69          | ~ (v1_funct_1 @ sk_D))),
% 43.48/43.69      inference('sup+', [status(thm)], ['217', '218'])).
% 43.48/43.69  thf('220', plain, ((v1_relat_1 @ sk_D)),
% 43.48/43.69      inference('demod', [status(thm)], ['15', '16'])).
% 43.48/43.69  thf('221', plain, ((v1_funct_1 @ sk_D)),
% 43.48/43.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 43.48/43.69  thf('222', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_D @ X0))),
% 43.48/43.69      inference('demod', [status(thm)], ['219', '220', '221'])).
% 43.48/43.69  thf('223', plain,
% 43.48/43.69      (![X0 : $i]:
% 43.48/43.69         (v1_funct_2 @ (k7_relat_1 @ sk_D @ X0) @ 
% 43.48/43.69          (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_B)),
% 43.48/43.69      inference('demod', [status(thm)], ['188', '222'])).
% 43.48/43.69  thf('224', plain, ((v1_funct_2 @ (k7_relat_1 @ sk_D @ sk_C) @ sk_C @ sk_B)),
% 43.48/43.69      inference('sup+', [status(thm)], ['177', '223'])).
% 43.48/43.69  thf('225', plain, ($false), inference('demod', [status(thm)], ['71', '224'])).
% 43.48/43.69  
% 43.48/43.69  % SZS output end Refutation
% 43.48/43.69  
% 43.53/43.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
