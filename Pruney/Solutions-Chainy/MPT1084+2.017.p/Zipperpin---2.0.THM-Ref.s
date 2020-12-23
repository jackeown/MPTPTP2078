%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qov8kAkLu6

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 534 expanded)
%              Number of leaves         :   31 ( 174 expanded)
%              Depth                    :   16
%              Number of atoms          :  843 (7768 expanded)
%              Number of equality atoms :   56 ( 270 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( v1_partfun1 @ X13 @ X14 )
      | ~ ( v1_funct_2 @ X13 @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ( v1_xboole_0 @ X15 ) ) ),
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
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_partfun1 @ X17 @ X16 )
      | ( ( k1_relat_1 @ X17 )
        = X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v4_relat_1 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( ( k1_relat_1 @ X8 )
       != X7 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 )
      | ( X8
        = ( k6_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('21',plain,(
    ! [X8: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k6_relat_1 @ ( k1_relat_1 @ X8 ) ) )
      | ( r2_hidden @ ( sk_C @ X8 @ ( k1_relat_1 @ X8 ) ) @ ( k1_relat_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('22',plain,(
    ! [X22: $i] :
      ( ( k6_partfun1 @ X22 )
      = ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    ! [X8: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k6_partfun1 @ ( k1_relat_1 @ X8 ) ) )
      | ( r2_hidden @ ( sk_C @ X8 @ ( k1_relat_1 @ X8 ) ) @ ( k1_relat_1 @ X8 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( m1_subset_1 @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) @ sk_A )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['19','25'])).

thf('27',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['10','15','18'])).

thf('28',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['10','15','18'])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['13','14'])).

thf('30',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['10','15','18'])).

thf('32',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30','31'])).

thf('33',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X27: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X27 )
        = X27 )
      | ~ ( m1_subset_1 @ X27 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      = ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ X19 )
      | ( ( k3_funct_2 @ X19 @ X20 @ X18 @ X21 )
        = ( k1_funct_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','45'])).

thf('47',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['36','46'])).

thf('48',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['10','15','18'])).

thf('50',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k1_relat_1 @ X8 )
       != X7 )
      | ( ( k1_funct_1 @ X8 @ ( sk_C @ X8 @ X7 ) )
       != ( sk_C @ X8 @ X7 ) )
      | ( X8
        = ( k6_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('51',plain,(
    ! [X8: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k6_relat_1 @ ( k1_relat_1 @ X8 ) ) )
      | ( ( k1_funct_1 @ X8 @ ( sk_C @ X8 @ ( k1_relat_1 @ X8 ) ) )
       != ( sk_C @ X8 @ ( k1_relat_1 @ X8 ) ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X22: $i] :
      ( ( k6_partfun1 @ X22 )
      = ( k6_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('53',plain,(
    ! [X8: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k6_partfun1 @ ( k1_relat_1 @ X8 ) ) )
      | ( ( k1_funct_1 @ X8 @ ( sk_C @ X8 @ ( k1_relat_1 @ X8 ) ) )
       != ( sk_C @ X8 @ ( k1_relat_1 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
     != ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['49','53'])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['10','15','18'])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['10','15','18'])).

thf('57',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['13','14'])).

thf('59',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
     != ( sk_C @ sk_B @ sk_A ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58'])).

thf('60',plain,
    ( sk_B
    = ( k6_partfun1 @ sk_A ) ),
    inference(clc,[status(thm)],['48','59'])).

thf('61',plain,(
    ~ ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['0','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('63',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( r2_funct_2 @ X24 @ X25 @ X23 @ X26 )
      | ( X23 != X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('64',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_funct_2 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['61','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qov8kAkLu6
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:29:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 61 iterations in 0.032s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.48  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.20/0.48  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(t201_funct_2, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.48             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.48           ( ( ![C:$i]:
% 0.20/0.48               ( ( m1_subset_1 @ C @ A ) =>
% 0.20/0.48                 ( ( k3_funct_2 @ A @ A @ B @ C ) = ( C ) ) ) ) =>
% 0.20/0.48             ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.48                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.48              ( ( ![C:$i]:
% 0.20/0.48                  ( ( m1_subset_1 @ C @ A ) =>
% 0.20/0.48                    ( ( k3_funct_2 @ A @ A @ B @ C ) = ( C ) ) ) ) =>
% 0.20/0.48                ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t201_funct_2])).
% 0.20/0.48  thf('0', plain, (~ (r2_funct_2 @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(cc5_funct_2, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.48       ( ![C:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.20/0.48             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.20/0.48          | (v1_partfun1 @ X13 @ X14)
% 0.20/0.48          | ~ (v1_funct_2 @ X13 @ X14 @ X15)
% 0.20/0.48          | ~ (v1_funct_1 @ X13)
% 0.20/0.48          | (v1_xboole_0 @ X15))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (((v1_xboole_0 @ sk_A)
% 0.20/0.48        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.48        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.20/0.48        | (v1_partfun1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('5', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('6', plain, (((v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_B @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.20/0.48  thf('7', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('8', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf(d4_partfun1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.48       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X16 : $i, X17 : $i]:
% 0.20/0.48         (~ (v1_partfun1 @ X17 @ X16)
% 0.20/0.48          | ((k1_relat_1 @ X17) = (X16))
% 0.20/0.48          | ~ (v4_relat_1 @ X17 @ X16)
% 0.20/0.48          | ~ (v1_relat_1 @ X17))),
% 0.20/0.48      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.48        | ~ (v4_relat_1 @ sk_B @ sk_A)
% 0.20/0.48        | ((k1_relat_1 @ sk_B) = (sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(cc2_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.20/0.48          | (v1_relat_1 @ X3)
% 0.20/0.48          | ~ (v1_relat_1 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.48  thf(fc6_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.48  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(cc2_relset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.48       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.48         ((v4_relat_1 @ X10 @ X11)
% 0.20/0.48          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.48  thf('18', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.20/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('19', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['10', '15', '18'])).
% 0.20/0.48  thf(t34_funct_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.48       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.20/0.48         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]:
% 0.20/0.48         (((k1_relat_1 @ X8) != (X7))
% 0.20/0.48          | (r2_hidden @ (sk_C @ X8 @ X7) @ X7)
% 0.20/0.48          | ((X8) = (k6_relat_1 @ X7))
% 0.20/0.48          | ~ (v1_funct_1 @ X8)
% 0.20/0.48          | ~ (v1_relat_1 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X8 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X8)
% 0.20/0.48          | ~ (v1_funct_1 @ X8)
% 0.20/0.48          | ((X8) = (k6_relat_1 @ (k1_relat_1 @ X8)))
% 0.20/0.48          | (r2_hidden @ (sk_C @ X8 @ (k1_relat_1 @ X8)) @ (k1_relat_1 @ X8)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.48  thf(redefinition_k6_partfun1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.20/0.48  thf('22', plain, (![X22 : $i]: ((k6_partfun1 @ X22) = (k6_relat_1 @ X22))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X8 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X8)
% 0.20/0.48          | ~ (v1_funct_1 @ X8)
% 0.20/0.48          | ((X8) = (k6_partfun1 @ (k1_relat_1 @ X8)))
% 0.20/0.48          | (r2_hidden @ (sk_C @ X8 @ (k1_relat_1 @ X8)) @ (k1_relat_1 @ X8)))),
% 0.20/0.48      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf(d2_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.48         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.48       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.48         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.48          | (m1_subset_1 @ X0 @ X1)
% 0.20/0.48          | (v1_xboole_0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((X0) = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.20/0.48          | ~ (v1_funct_1 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X0)
% 0.20/0.48          | (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.20/0.48          | (m1_subset_1 @ (sk_C @ X0 @ (k1_relat_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (((m1_subset_1 @ (sk_C @ sk_B @ (k1_relat_1 @ sk_B)) @ sk_A)
% 0.20/0.48        | (v1_xboole_0 @ (k1_relat_1 @ sk_B))
% 0.20/0.48        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.48        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.48        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B))))),
% 0.20/0.48      inference('sup+', [status(thm)], ['19', '25'])).
% 0.20/0.48  thf('27', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['10', '15', '18'])).
% 0.20/0.48  thf('28', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['10', '15', '18'])).
% 0.20/0.48  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.48  thf('30', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('31', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['10', '15', '18'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (((m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.48        | (v1_xboole_0 @ sk_A)
% 0.20/0.48        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['26', '27', '28', '29', '30', '31'])).
% 0.20/0.48  thf('33', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.20/0.48        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.48      inference('clc', [status(thm)], ['32', '33'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (![X27 : $i]:
% 0.20/0.48         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X27) = (X27))
% 0.20/0.48          | ~ (m1_subset_1 @ X27 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.20/0.48        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48            = (sk_C @ sk_B @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.20/0.48        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.48      inference('clc', [status(thm)], ['32', '33'])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(redefinition_k3_funct_2, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.48         ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.48         ( m1_subset_1 @ D @ A ) ) =>
% 0.20/0.48       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.20/0.48          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.20/0.48          | ~ (v1_funct_1 @ X18)
% 0.20/0.48          | (v1_xboole_0 @ X19)
% 0.20/0.48          | ~ (m1_subset_1 @ X21 @ X19)
% 0.20/0.48          | ((k3_funct_2 @ X19 @ X20 @ X18 @ X21) = (k1_funct_1 @ X18 @ X21)))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0))
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.48          | (v1_xboole_0 @ sk_A)
% 0.20/0.48          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.48          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.48  thf('41', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('42', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0))
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.48          | (v1_xboole_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.20/0.48  thf('44', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.48          | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0)))),
% 0.20/0.48      inference('clc', [status(thm)], ['43', '44'])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.20/0.48        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.20/0.48            = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['37', '45'])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      ((((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)))
% 0.20/0.48        | ((sk_B) = (k6_partfun1 @ sk_A))
% 0.20/0.48        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['36', '46'])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.20/0.48        | ((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.20/0.48      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.48  thf('49', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['10', '15', '18'])).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]:
% 0.20/0.48         (((k1_relat_1 @ X8) != (X7))
% 0.20/0.48          | ((k1_funct_1 @ X8 @ (sk_C @ X8 @ X7)) != (sk_C @ X8 @ X7))
% 0.20/0.48          | ((X8) = (k6_relat_1 @ X7))
% 0.20/0.48          | ~ (v1_funct_1 @ X8)
% 0.20/0.48          | ~ (v1_relat_1 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      (![X8 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X8)
% 0.20/0.48          | ~ (v1_funct_1 @ X8)
% 0.20/0.48          | ((X8) = (k6_relat_1 @ (k1_relat_1 @ X8)))
% 0.20/0.49          | ((k1_funct_1 @ X8 @ (sk_C @ X8 @ (k1_relat_1 @ X8)))
% 0.20/0.49              != (sk_C @ X8 @ (k1_relat_1 @ X8))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.49  thf('52', plain, (![X22 : $i]: ((k6_partfun1 @ X22) = (k6_relat_1 @ X22))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (![X8 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X8)
% 0.20/0.49          | ~ (v1_funct_1 @ X8)
% 0.20/0.49          | ((X8) = (k6_partfun1 @ (k1_relat_1 @ X8)))
% 0.20/0.49          | ((k1_funct_1 @ X8 @ (sk_C @ X8 @ (k1_relat_1 @ X8)))
% 0.20/0.49              != (sk_C @ X8 @ (k1_relat_1 @ X8))))),
% 0.20/0.49      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.49  thf('54', plain,
% 0.20/0.49      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.20/0.49          != (sk_C @ sk_B @ (k1_relat_1 @ sk_B)))
% 0.20/0.49        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.20/0.49        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.49        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['49', '53'])).
% 0.20/0.49  thf('55', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['10', '15', '18'])).
% 0.20/0.49  thf('56', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['10', '15', '18'])).
% 0.20/0.49  thf('57', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('58', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('59', plain,
% 0.20/0.49      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)) != (sk_C @ sk_B @ sk_A))
% 0.20/0.49        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['54', '55', '56', '57', '58'])).
% 0.20/0.49  thf('60', plain, (((sk_B) = (k6_partfun1 @ sk_A))),
% 0.20/0.49      inference('clc', [status(thm)], ['48', '59'])).
% 0.20/0.49  thf('61', plain, (~ (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['0', '60'])).
% 0.20/0.49  thf('62', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(redefinition_r2_funct_2, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.49         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.49       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.20/0.49  thf('63', plain,
% 0.20/0.49      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.20/0.49          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.20/0.49          | ~ (v1_funct_1 @ X23)
% 0.20/0.49          | ~ (v1_funct_1 @ X26)
% 0.20/0.49          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.20/0.49          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.20/0.49          | (r2_funct_2 @ X24 @ X25 @ X23 @ X26)
% 0.20/0.49          | ((X23) != (X26)))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.20/0.49  thf('64', plain,
% 0.20/0.49      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.49         ((r2_funct_2 @ X24 @ X25 @ X26 @ X26)
% 0.20/0.49          | ~ (v1_funct_1 @ X26)
% 0.20/0.49          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.20/0.49          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['63'])).
% 0.20/0.49  thf('65', plain,
% 0.20/0.49      ((~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.20/0.49        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.49        | (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['62', '64'])).
% 0.20/0.49  thf('66', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('67', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('68', plain, ((r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.20/0.49  thf('69', plain, ($false), inference('demod', [status(thm)], ['61', '68'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
