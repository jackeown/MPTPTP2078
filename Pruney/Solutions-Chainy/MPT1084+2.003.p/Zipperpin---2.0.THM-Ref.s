%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kberzSHP7A

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 501 expanded)
%              Number of leaves         :   30 ( 163 expanded)
%              Depth                    :   15
%              Number of atoms          :  853 (7776 expanded)
%              Number of equality atoms :   54 ( 274 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_relat_1 @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('16',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['10','13','16'])).

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

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
       != X3 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 )
      | ( X4
        = ( k6_relat_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('19',plain,(
    ! [X4: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4
        = ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ( r2_hidden @ ( sk_C @ X4 @ ( k1_relat_1 @ X4 ) ) @ ( k1_relat_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('20',plain,(
    ! [X21: $i] :
      ( ( k6_partfun1 @ X21 )
      = ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('21',plain,(
    ! [X4: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4
        = ( k6_partfun1 @ ( k1_relat_1 @ X4 ) ) )
      | ( r2_hidden @ ( sk_C @ X4 @ ( k1_relat_1 @ X4 ) ) @ ( k1_relat_1 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( m1_subset_1 @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['17','23'])).

thf('25',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['10','13','16'])).

thf('26',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['10','13','16'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('28',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['10','13','16'])).

thf('30',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26','27','28','29'])).

thf('31',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X26: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X26 )
        = X26 )
      | ~ ( m1_subset_1 @ X26 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      = ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('36',plain,(
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

thf('37',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ X18 )
      | ( ( k3_funct_2 @ X18 @ X19 @ X17 @ X20 )
        = ( k1_funct_1 @ X17 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','44'])).

thf('46',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['10','13','16'])).

thf('48',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
       != X3 )
      | ( ( k1_funct_1 @ X4 @ ( sk_C @ X4 @ X3 ) )
       != ( sk_C @ X4 @ X3 ) )
      | ( X4
        = ( k6_relat_1 @ X3 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('49',plain,(
    ! [X4: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4
        = ( k6_relat_1 @ ( k1_relat_1 @ X4 ) ) )
      | ( ( k1_funct_1 @ X4 @ ( sk_C @ X4 @ ( k1_relat_1 @ X4 ) ) )
       != ( sk_C @ X4 @ ( k1_relat_1 @ X4 ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X21: $i] :
      ( ( k6_partfun1 @ X21 )
      = ( k6_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('51',plain,(
    ! [X4: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( X4
        = ( k6_partfun1 @ ( k1_relat_1 @ X4 ) ) )
      | ( ( k1_funct_1 @ X4 @ ( sk_C @ X4 @ ( k1_relat_1 @ X4 ) ) )
       != ( sk_C @ X4 @ ( k1_relat_1 @ X4 ) ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
     != ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['10','13','16'])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['10','13','16'])).

thf('55',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('57',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
     != ( sk_C @ sk_B @ sk_A ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53','54','55','56'])).

thf('58',plain,
    ( sk_B
    = ( k6_partfun1 @ sk_A ) ),
    inference(clc,[status(thm)],['46','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('61',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( r2_funct_2 @ X22 @ X23 @ X24 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
      | ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,
    ( ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['0','58','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kberzSHP7A
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:10:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 55 iterations in 0.029s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.21/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.49  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.49  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.21/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
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
% 0.21/0.49  thf(cc1_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( v1_relat_1 @ C ) ))).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.49         ((v1_relat_1 @ X6)
% 0.21/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.49  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(cc2_relset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.49         ((v4_relat_1 @ X9 @ X10)
% 0.21/0.49          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.49  thf('16', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.21/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('17', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '13', '16'])).
% 0.21/0.49  thf(t34_funct_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.49       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.21/0.49         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         (((k1_relat_1 @ X4) != (X3))
% 0.21/0.49          | (r2_hidden @ (sk_C @ X4 @ X3) @ X3)
% 0.21/0.49          | ((X4) = (k6_relat_1 @ X3))
% 0.21/0.49          | ~ (v1_funct_1 @ X4)
% 0.21/0.49          | ~ (v1_relat_1 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X4 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X4)
% 0.21/0.49          | ~ (v1_funct_1 @ X4)
% 0.21/0.49          | ((X4) = (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.21/0.49          | (r2_hidden @ (sk_C @ X4 @ (k1_relat_1 @ X4)) @ (k1_relat_1 @ X4)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.49  thf(redefinition_k6_partfun1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.49  thf('20', plain, (![X21 : $i]: ((k6_partfun1 @ X21) = (k6_relat_1 @ X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X4 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X4)
% 0.21/0.49          | ~ (v1_funct_1 @ X4)
% 0.21/0.49          | ((X4) = (k6_partfun1 @ (k1_relat_1 @ X4)))
% 0.21/0.49          | (r2_hidden @ (sk_C @ X4 @ (k1_relat_1 @ X4)) @ (k1_relat_1 @ X4)))),
% 0.21/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf(d2_subset_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.49         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.49       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.49          | (m1_subset_1 @ X0 @ X1)
% 0.21/0.49          | (v1_xboole_0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((X0) = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ X0)
% 0.21/0.49          | (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.21/0.49          | (m1_subset_1 @ (sk_C @ X0 @ (k1_relat_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (((m1_subset_1 @ (sk_C @ sk_B @ (k1_relat_1 @ sk_B)) @ sk_A)
% 0.21/0.49        | (v1_xboole_0 @ (k1_relat_1 @ sk_B))
% 0.21/0.49        | ~ (v1_relat_1 @ sk_B)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.49        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B))))),
% 0.21/0.49      inference('sup+', [status(thm)], ['17', '23'])).
% 0.21/0.49  thf('25', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '13', '16'])).
% 0.21/0.49  thf('26', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '13', '16'])).
% 0.21/0.49  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('29', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '13', '16'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.49        | (v1_xboole_0 @ sk_A)
% 0.21/0.49        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['24', '25', '26', '27', '28', '29'])).
% 0.21/0.49  thf('31', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.21/0.49        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['30', '31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (![X26 : $i]:
% 0.21/0.49         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X26) = (X26))
% 0.21/0.49          | ~ (m1_subset_1 @ X26 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.21/0.49        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.21/0.49            = (sk_C @ sk_B @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.21/0.49        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['30', '31'])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(redefinition_k3_funct_2, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.49         ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.49         ( m1_subset_1 @ D @ A ) ) =>
% 0.21/0.49       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.21/0.49          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.21/0.49          | ~ (v1_funct_1 @ X17)
% 0.21/0.49          | (v1_xboole_0 @ X18)
% 0.21/0.49          | ~ (m1_subset_1 @ X20 @ X18)
% 0.21/0.49          | ((k3_funct_2 @ X18 @ X19 @ X17 @ X20) = (k1_funct_1 @ X17 @ X20)))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.49          | (v1_xboole_0 @ sk_A)
% 0.21/0.49          | ~ (v1_funct_1 @ sk_B)
% 0.21/0.49          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.49  thf('39', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('40', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.49          | (v1_xboole_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.21/0.49  thf('42', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.49          | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0)))),
% 0.21/0.49      inference('clc', [status(thm)], ['41', '42'])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.21/0.49        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.21/0.49            = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['35', '43'])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      ((((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)))
% 0.21/0.49        | ((sk_B) = (k6_partfun1 @ sk_A))
% 0.21/0.49        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['34', '44'])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.21/0.49        | ((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.49  thf('47', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '13', '16'])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (![X3 : $i, X4 : $i]:
% 0.21/0.49         (((k1_relat_1 @ X4) != (X3))
% 0.21/0.49          | ((k1_funct_1 @ X4 @ (sk_C @ X4 @ X3)) != (sk_C @ X4 @ X3))
% 0.21/0.49          | ((X4) = (k6_relat_1 @ X3))
% 0.21/0.49          | ~ (v1_funct_1 @ X4)
% 0.21/0.49          | ~ (v1_relat_1 @ X4))),
% 0.21/0.49      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (![X4 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X4)
% 0.21/0.49          | ~ (v1_funct_1 @ X4)
% 0.21/0.49          | ((X4) = (k6_relat_1 @ (k1_relat_1 @ X4)))
% 0.21/0.49          | ((k1_funct_1 @ X4 @ (sk_C @ X4 @ (k1_relat_1 @ X4)))
% 0.21/0.49              != (sk_C @ X4 @ (k1_relat_1 @ X4))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['48'])).
% 0.21/0.49  thf('50', plain, (![X21 : $i]: ((k6_partfun1 @ X21) = (k6_relat_1 @ X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (![X4 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X4)
% 0.21/0.49          | ~ (v1_funct_1 @ X4)
% 0.21/0.49          | ((X4) = (k6_partfun1 @ (k1_relat_1 @ X4)))
% 0.21/0.49          | ((k1_funct_1 @ X4 @ (sk_C @ X4 @ (k1_relat_1 @ X4)))
% 0.21/0.49              != (sk_C @ X4 @ (k1_relat_1 @ X4))))),
% 0.21/0.49      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.21/0.49          != (sk_C @ sk_B @ (k1_relat_1 @ sk_B)))
% 0.21/0.49        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.21/0.49        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.49        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['47', '51'])).
% 0.21/0.49  thf('53', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '13', '16'])).
% 0.21/0.49  thf('54', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '13', '16'])).
% 0.21/0.49  thf('55', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('56', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('57', plain,
% 0.21/0.49      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)) != (sk_C @ sk_B @ sk_A))
% 0.21/0.49        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['52', '53', '54', '55', '56'])).
% 0.21/0.49  thf('58', plain, (((sk_B) = (k6_partfun1 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['46', '57'])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(reflexivity_r2_funct_2, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.49         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.49       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.49         ((r2_funct_2 @ X22 @ X23 @ X24 @ X24)
% 0.21/0.49          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.21/0.49          | ~ (v1_funct_2 @ X24 @ X22 @ X23)
% 0.21/0.49          | ~ (v1_funct_1 @ X24)
% 0.21/0.49          | ~ (v1_funct_1 @ X25)
% 0.21/0.49          | ~ (v1_funct_2 @ X25 @ X22 @ X23)
% 0.21/0.49          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.21/0.49      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.21/0.49  thf('62', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.49          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ sk_B)
% 0.21/0.49          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.21/0.49          | (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.49  thf('63', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('64', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('65', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.49          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.21/0.49  thf('66', plain,
% 0.21/0.49      (((r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_B)
% 0.21/0.49        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['59', '65'])).
% 0.21/0.49  thf('67', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('68', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('69', plain, ((r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.21/0.49  thf('70', plain, ($false),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '58', '69'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
