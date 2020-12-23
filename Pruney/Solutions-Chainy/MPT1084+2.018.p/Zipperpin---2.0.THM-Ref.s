%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.glldN707rW

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  123 (2282 expanded)
%              Number of leaves         :   32 ( 696 expanded)
%              Depth                    :   24
%              Number of atoms          : 1119 (34617 expanded)
%              Number of equality atoms :   62 (1222 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t201_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ A @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ( ( k3_funct_2 @ A @ A @ B @ C )
                  = C ) )
           => ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ( v1_funct_1 @ B )
              & ( v1_funct_2 @ B @ A @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ! [C: $i] :
                  ( ( m1_subset_1 @ C @ A )
                 => ( ( k3_funct_2 @ A @ A @ B @ C )
                    = C ) )
             => ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t201_funct_2])).

thf('0',plain,(
    ~ ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( v1_partfun1 @ X12 @ X13 )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_partfun1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['6','7'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('9',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_partfun1 @ X16 @ X15 )
      | ( ( k1_relat_1 @ X16 )
        = X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v4_relat_1 @ sk_B @ sk_A )
    | ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('18',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['10','15','18'])).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
       != X6 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 )
      | ( X7
        = ( k6_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('21',plain,(
    ! [X7: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) )
      | ( r2_hidden @ ( sk_C @ X7 @ ( k1_relat_1 @ X7 ) ) @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('22',plain,(
    ! [X26: $i] :
      ( ( k6_partfun1 @ X26 )
      = ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    ! [X7: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k6_partfun1 @ ( k1_relat_1 @ X7 ) ) )
      | ( r2_hidden @ ( sk_C @ X7 @ ( k1_relat_1 @ X7 ) ) @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['19','23'])).

thf('25',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['10','15','18'])).

thf('26',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['10','15','18'])).

thf('27',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['13','14'])).

thf('29',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26','27','28'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('31',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X27: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X27 )
        = X27 )
      | ~ ( m1_subset_1 @ X27 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      = ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('36',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X22 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ X23 )
      | ( ( k3_funct_2 @ X23 @ X24 @ X22 @ X25 )
        = ( k1_funct_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','42'])).

thf('44',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['33','43'])).

thf('45',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['10','15','18'])).

thf('47',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
       != X6 )
      | ( ( k1_funct_1 @ X7 @ ( sk_C @ X7 @ X6 ) )
       != ( sk_C @ X7 @ X6 ) )
      | ( X7
        = ( k6_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('48',plain,(
    ! [X7: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k6_relat_1 @ ( k1_relat_1 @ X7 ) ) )
      | ( ( k1_funct_1 @ X7 @ ( sk_C @ X7 @ ( k1_relat_1 @ X7 ) ) )
       != ( sk_C @ X7 @ ( k1_relat_1 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X26: $i] :
      ( ( k6_partfun1 @ X26 )
      = ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('50',plain,(
    ! [X7: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( X7
        = ( k6_partfun1 @ ( k1_relat_1 @ X7 ) ) )
      | ( ( k1_funct_1 @ X7 @ ( sk_C @ X7 @ ( k1_relat_1 @ X7 ) ) )
       != ( sk_C @ X7 @ ( k1_relat_1 @ X7 ) ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
     != ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['46','50'])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['10','15','18'])).

thf('53',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['10','15','18'])).

thf('54',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['13','14'])).

thf('56',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
     != ( sk_C @ sk_B @ sk_A ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('57',plain,
    ( sk_B
    = ( k6_partfun1 @ sk_A ) ),
    inference(clc,[status(thm)],['45','56'])).

thf('58',plain,(
    ~ ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['0','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r2_funct_2 @ A @ B @ C @ D )
          <=> ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) ) ) ) ) )).

thf('62',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( m1_subset_1 @ ( sk_E @ X17 @ X20 @ X18 ) @ X18 )
      | ( r2_funct_2 @ X18 @ X19 @ X20 @ X17 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_2])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_funct_2 @ sk_A @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_B @ X0 @ sk_A ) @ sk_A )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_funct_2 @ sk_A @ sk_A @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_E @ sk_B @ X0 @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_B @ sk_B @ sk_A ) @ sk_A )
    | ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','66'])).

thf('68',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( m1_subset_1 @ ( sk_E @ sk_B @ sk_B @ sk_A ) @ sk_A )
    | ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ~ ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['0','57'])).

thf('72',plain,(
    m1_subset_1 @ ( sk_E @ sk_B @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('74',plain,
    ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_E @ sk_B @ sk_B @ sk_A ) )
    = ( k1_funct_1 @ sk_B @ ( sk_E @ sk_B @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ ( sk_E @ sk_B @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['70','71'])).

thf('76',plain,(
    ! [X27: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X27 )
        = X27 )
      | ~ ( m1_subset_1 @ X27 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_E @ sk_B @ sk_B @ sk_A ) )
    = ( sk_E @ sk_B @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_E @ sk_B @ sk_B @ sk_A ) )
    = ( sk_E @ sk_B @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['74','77'])).

thf('79',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( ( k1_funct_1 @ X20 @ ( sk_E @ X17 @ X20 @ X18 ) )
       != ( k1_funct_1 @ X17 @ ( sk_E @ X17 @ X20 @ X18 ) ) )
      | ( r2_funct_2 @ X18 @ X19 @ X20 @ X17 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_2])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( sk_E @ sk_B @ sk_B @ sk_A )
       != ( k1_funct_1 @ sk_B @ ( sk_E @ sk_B @ sk_B @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_funct_2 @ sk_A @ X0 @ sk_B @ sk_B )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ X0 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( k1_funct_1 @ sk_B @ ( sk_E @ sk_B @ sk_B @ sk_A ) )
    = ( sk_E @ sk_B @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['74','77'])).

thf('82',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( sk_E @ sk_B @ sk_B @ sk_A )
       != ( sk_E @ sk_B @ sk_B @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ( r2_funct_2 @ sk_A @ X0 @ sk_B @ sk_B )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81','82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r2_funct_2 @ sk_A @ X0 @ sk_B @ sk_B )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['59','85'])).

thf('87',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    $false ),
    inference(demod,[status(thm)],['58','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.glldN707rW
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:13:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 52 iterations in 0.027s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.49  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.49  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(t201_funct_2, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.49             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.49           ( ( ![C:$i]:
% 0.21/0.49               ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.49                 ( ( k3_funct_2 @ A @ A @ B @ C ) = ( C ) ) ) ) =>
% 0.21/0.49             ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.49                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.49              ( ( ![C:$i]:
% 0.21/0.49                  ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.49                    ( ( k3_funct_2 @ A @ A @ B @ C ) = ( C ) ) ) ) =>
% 0.21/0.49                ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t201_funct_2])).
% 0.21/0.49  thf('0', plain, (~ (r2_funct_2 @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(cc5_funct_2, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.49       ( ![C:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.21/0.49             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.21/0.49          | (v1_partfun1 @ X12 @ X13)
% 0.21/0.49          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 0.21/0.49          | ~ (v1_funct_1 @ X12)
% 0.21/0.49          | (v1_xboole_0 @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (((v1_xboole_0 @ sk_A)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.49        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.49        | (v1_partfun1 @ sk_B @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('6', plain, (((v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_B @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.49  thf('7', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('8', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.21/0.49      inference('clc', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf(d4_partfun1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.49       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (~ (v1_partfun1 @ X16 @ X15)
% 0.21/0.49          | ((k1_relat_1 @ X16) = (X15))
% 0.21/0.49          | ~ (v4_relat_1 @ X16 @ X15)
% 0.21/0.49          | ~ (v1_relat_1 @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ sk_B)
% 0.21/0.49        | ~ (v4_relat_1 @ sk_B @ sk_A)
% 0.21/0.49        | ((k1_relat_1 @ sk_B) = (sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(cc2_relat_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.21/0.49          | (v1_relat_1 @ X2)
% 0.21/0.49          | ~ (v1_relat_1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf(fc6_relat_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.49  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(cc2_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.49         ((v4_relat_1 @ X9 @ X10)
% 0.21/0.49          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.49  thf('18', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.21/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.49  thf('19', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '15', '18'])).
% 0.21/0.49  thf(t34_funct_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.49       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.21/0.49         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i]:
% 0.21/0.49         (((k1_relat_1 @ X7) != (X6))
% 0.21/0.49          | (r2_hidden @ (sk_C @ X7 @ X6) @ X6)
% 0.21/0.49          | ((X7) = (k6_relat_1 @ X6))
% 0.21/0.49          | ~ (v1_funct_1 @ X7)
% 0.21/0.49          | ~ (v1_relat_1 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X7 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X7)
% 0.21/0.49          | ~ (v1_funct_1 @ X7)
% 0.21/0.49          | ((X7) = (k6_relat_1 @ (k1_relat_1 @ X7)))
% 0.21/0.49          | (r2_hidden @ (sk_C @ X7 @ (k1_relat_1 @ X7)) @ (k1_relat_1 @ X7)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.49  thf(redefinition_k6_partfun1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.49  thf('22', plain, (![X26 : $i]: ((k6_partfun1 @ X26) = (k6_relat_1 @ X26))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X7 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X7)
% 0.21/0.49          | ~ (v1_funct_1 @ X7)
% 0.21/0.49          | ((X7) = (k6_partfun1 @ (k1_relat_1 @ X7)))
% 0.21/0.49          | (r2_hidden @ (sk_C @ X7 @ (k1_relat_1 @ X7)) @ (k1_relat_1 @ X7)))),
% 0.21/0.49      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (((r2_hidden @ (sk_C @ sk_B @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.21/0.49        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.21/0.49        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.49        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.49      inference('sup+', [status(thm)], ['19', '23'])).
% 0.21/0.49  thf('25', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '15', '18'])).
% 0.21/0.49  thf('26', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '15', '18'])).
% 0.21/0.49  thf('27', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('28', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (((r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.49        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['24', '25', '26', '27', '28'])).
% 0.21/0.49  thf(t1_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.21/0.49        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X27 : $i]:
% 0.21/0.49         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X27) = (X27))
% 0.21/0.49          | ~ (m1_subset_1 @ X27 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.21/0.49        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.21/0.49            = (sk_C @ sk_B @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.21/0.49        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(redefinition_k3_funct_2, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.49         ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.49         ( m1_subset_1 @ D @ A ) ) =>
% 0.21/0.49       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.21/0.49          | ~ (v1_funct_2 @ X22 @ X23 @ X24)
% 0.21/0.49          | ~ (v1_funct_1 @ X22)
% 0.21/0.49          | (v1_xboole_0 @ X23)
% 0.21/0.49          | ~ (m1_subset_1 @ X25 @ X23)
% 0.21/0.49          | ((k3_funct_2 @ X23 @ X24 @ X22 @ X25) = (k1_funct_1 @ X22 @ X25)))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.49          | (v1_xboole_0 @ sk_A)
% 0.21/0.49          | ~ (v1_funct_1 @ sk_B)
% 0.21/0.49          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.49  thf('38', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('39', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.49          | (v1_xboole_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.21/0.49  thf('41', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.49          | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0)))),
% 0.21/0.49      inference('clc', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.21/0.49        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.21/0.49            = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['34', '42'])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      ((((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)))
% 0.21/0.49        | ((sk_B) = (k6_partfun1 @ sk_A))
% 0.21/0.49        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['33', '43'])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.21/0.49        | ((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.49  thf('46', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '15', '18'])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i]:
% 0.21/0.49         (((k1_relat_1 @ X7) != (X6))
% 0.21/0.49          | ((k1_funct_1 @ X7 @ (sk_C @ X7 @ X6)) != (sk_C @ X7 @ X6))
% 0.21/0.49          | ((X7) = (k6_relat_1 @ X6))
% 0.21/0.49          | ~ (v1_funct_1 @ X7)
% 0.21/0.49          | ~ (v1_relat_1 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (![X7 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X7)
% 0.21/0.49          | ~ (v1_funct_1 @ X7)
% 0.21/0.49          | ((X7) = (k6_relat_1 @ (k1_relat_1 @ X7)))
% 0.21/0.49          | ((k1_funct_1 @ X7 @ (sk_C @ X7 @ (k1_relat_1 @ X7)))
% 0.21/0.49              != (sk_C @ X7 @ (k1_relat_1 @ X7))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.49  thf('49', plain, (![X26 : $i]: ((k6_partfun1 @ X26) = (k6_relat_1 @ X26))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      (![X7 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X7)
% 0.21/0.49          | ~ (v1_funct_1 @ X7)
% 0.21/0.49          | ((X7) = (k6_partfun1 @ (k1_relat_1 @ X7)))
% 0.21/0.49          | ((k1_funct_1 @ X7 @ (sk_C @ X7 @ (k1_relat_1 @ X7)))
% 0.21/0.49              != (sk_C @ X7 @ (k1_relat_1 @ X7))))),
% 0.21/0.49      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.21/0.49          != (sk_C @ sk_B @ (k1_relat_1 @ sk_B)))
% 0.21/0.49        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.21/0.49        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.49        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['46', '50'])).
% 0.21/0.49  thf('52', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '15', '18'])).
% 0.21/0.49  thf('53', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '15', '18'])).
% 0.21/0.49  thf('54', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('55', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)) != (sk_C @ sk_B @ sk_A))
% 0.21/0.49        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 0.21/0.49  thf('57', plain, (((sk_B) = (k6_partfun1 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['45', '56'])).
% 0.21/0.49  thf('58', plain, (~ (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '57'])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d9_funct_2, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.49       ( ![D:$i]:
% 0.21/0.49         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.49             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.49           ( ( r2_funct_2 @ A @ B @ C @ D ) <=>
% 0.21/0.49             ( ![E:$i]:
% 0.21/0.49               ( ( m1_subset_1 @ E @ A ) =>
% 0.21/0.49                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('62', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.49         (~ (v1_funct_1 @ X17)
% 0.21/0.49          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.21/0.49          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.21/0.49          | (m1_subset_1 @ (sk_E @ X17 @ X20 @ X18) @ X18)
% 0.21/0.49          | (r2_funct_2 @ X18 @ X19 @ X20 @ X17)
% 0.21/0.49          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.21/0.49          | ~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.21/0.49          | ~ (v1_funct_1 @ X20))),
% 0.21/0.49      inference('cnf', [status(esa)], [d9_funct_2])).
% 0.21/0.49  thf('63', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.49          | (r2_funct_2 @ sk_A @ sk_A @ X0 @ sk_B)
% 0.21/0.49          | (m1_subset_1 @ (sk_E @ sk_B @ X0 @ sk_A) @ sk_A)
% 0.21/0.49          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.49          | ~ (v1_funct_1 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.49  thf('64', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('65', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('66', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.49          | (r2_funct_2 @ sk_A @ sk_A @ X0 @ sk_B)
% 0.21/0.49          | (m1_subset_1 @ (sk_E @ sk_B @ X0 @ sk_A) @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.21/0.49  thf('67', plain,
% 0.21/0.49      (((m1_subset_1 @ (sk_E @ sk_B @ sk_B @ sk_A) @ sk_A)
% 0.21/0.49        | (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)
% 0.21/0.49        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['60', '66'])).
% 0.21/0.49  thf('68', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('69', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('70', plain,
% 0.21/0.49      (((m1_subset_1 @ (sk_E @ sk_B @ sk_B @ sk_A) @ sk_A)
% 0.21/0.49        | (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.21/0.49  thf('71', plain, (~ (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '57'])).
% 0.21/0.49  thf('72', plain, ((m1_subset_1 @ (sk_E @ sk_B @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.49      inference('clc', [status(thm)], ['70', '71'])).
% 0.21/0.49  thf('73', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.49          | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0)))),
% 0.21/0.49      inference('clc', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf('74', plain,
% 0.21/0.49      (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_E @ sk_B @ sk_B @ sk_A))
% 0.21/0.49         = (k1_funct_1 @ sk_B @ (sk_E @ sk_B @ sk_B @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.49  thf('75', plain, ((m1_subset_1 @ (sk_E @ sk_B @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.49      inference('clc', [status(thm)], ['70', '71'])).
% 0.21/0.49  thf('76', plain,
% 0.21/0.49      (![X27 : $i]:
% 0.21/0.49         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X27) = (X27))
% 0.21/0.49          | ~ (m1_subset_1 @ X27 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('77', plain,
% 0.21/0.49      (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_E @ sk_B @ sk_B @ sk_A))
% 0.21/0.49         = (sk_E @ sk_B @ sk_B @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.49  thf('78', plain,
% 0.21/0.49      (((k1_funct_1 @ sk_B @ (sk_E @ sk_B @ sk_B @ sk_A))
% 0.21/0.49         = (sk_E @ sk_B @ sk_B @ sk_A))),
% 0.21/0.49      inference('sup+', [status(thm)], ['74', '77'])).
% 0.21/0.49  thf('79', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.49         (~ (v1_funct_1 @ X17)
% 0.21/0.49          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.21/0.49          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.21/0.49          | ((k1_funct_1 @ X20 @ (sk_E @ X17 @ X20 @ X18))
% 0.21/0.49              != (k1_funct_1 @ X17 @ (sk_E @ X17 @ X20 @ X18)))
% 0.21/0.49          | (r2_funct_2 @ X18 @ X19 @ X20 @ X17)
% 0.21/0.49          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.21/0.49          | ~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.21/0.49          | ~ (v1_funct_1 @ X20))),
% 0.21/0.49      inference('cnf', [status(esa)], [d9_funct_2])).
% 0.21/0.49  thf('80', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_E @ sk_B @ sk_B @ sk_A)
% 0.21/0.49            != (k1_funct_1 @ sk_B @ (sk_E @ sk_B @ sk_B @ sk_A)))
% 0.21/0.49          | ~ (v1_funct_1 @ sk_B)
% 0.21/0.49          | ~ (v1_funct_2 @ sk_B @ sk_A @ X0)
% 0.21/0.49          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.21/0.49          | (r2_funct_2 @ sk_A @ X0 @ sk_B @ sk_B)
% 0.21/0.49          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.21/0.49          | ~ (v1_funct_2 @ sk_B @ sk_A @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['78', '79'])).
% 0.21/0.49  thf('81', plain,
% 0.21/0.49      (((k1_funct_1 @ sk_B @ (sk_E @ sk_B @ sk_B @ sk_A))
% 0.21/0.49         = (sk_E @ sk_B @ sk_B @ sk_A))),
% 0.21/0.49      inference('sup+', [status(thm)], ['74', '77'])).
% 0.21/0.49  thf('82', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('83', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('84', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((sk_E @ sk_B @ sk_B @ sk_A) != (sk_E @ sk_B @ sk_B @ sk_A))
% 0.21/0.49          | ~ (v1_funct_2 @ sk_B @ sk_A @ X0)
% 0.21/0.49          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.21/0.49          | (r2_funct_2 @ sk_A @ X0 @ sk_B @ sk_B)
% 0.21/0.49          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.21/0.49          | ~ (v1_funct_2 @ sk_B @ sk_A @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['80', '81', '82', '83'])).
% 0.21/0.49  thf('85', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((r2_funct_2 @ sk_A @ X0 @ sk_B @ sk_B)
% 0.21/0.49          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.21/0.49          | ~ (v1_funct_2 @ sk_B @ sk_A @ X0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['84'])).
% 0.21/0.49  thf('86', plain,
% 0.21/0.49      ((~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.49        | (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['59', '85'])).
% 0.21/0.49  thf('87', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('88', plain, ((r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['86', '87'])).
% 0.21/0.49  thf('89', plain, ($false), inference('demod', [status(thm)], ['58', '88'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
