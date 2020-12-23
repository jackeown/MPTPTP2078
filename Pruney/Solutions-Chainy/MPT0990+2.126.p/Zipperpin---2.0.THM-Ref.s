%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.807ArKXnNr

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:16 EST 2020

% Result     : Theorem 3.99s
% Output     : Refutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :  518 (4161 expanded)
%              Number of leaves         :   55 (1315 expanded)
%              Depth                    :   63
%              Number of atoms          : 4243 (71503 expanded)
%              Number of equality atoms :  240 (4613 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X33: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k1_relat_1 @ X33 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X26: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X34: $i] :
      ( ~ ( v2_funct_1 @ X34 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X34 ) @ X34 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X59: $i] :
      ( ( k6_partfun1 @ X59 )
      = ( k6_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('5',plain,(
    ! [X34: $i] :
      ( ~ ( v2_funct_1 @ X34 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X34 ) @ X34 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ( v2_funct_1 @ X31 )
      | ( ( k2_relat_1 @ X31 )
       != ( k1_relat_1 @ X32 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X31 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X28: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('9',plain,(
    ! [X59: $i] :
      ( ( k6_partfun1 @ X59 )
      = ( k6_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,(
    ! [X28: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X28 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X26: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('20',plain,(
    ! [X33: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k2_relat_1 @ X33 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('21',plain,(
    ! [X35: $i] :
      ( ~ ( v2_funct_1 @ X35 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X35 ) )
        = X35 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('22',plain,(
    ! [X35: $i] :
      ( ~ ( v2_funct_1 @ X35 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X35 ) )
        = X35 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('23',plain,(
    ! [X26: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('25',plain,(
    ! [X26: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('26',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('27',plain,(
    ! [X33: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k2_relat_1 @ X33 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('28',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t36_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ C )
                  = B )
                & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( v2_funct_1 @ C ) )
             => ( ( A = k1_xboole_0 )
                | ( B = k1_xboole_0 )
                | ( D
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_funct_2])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k2_relset_1 @ X40 @ X41 @ X39 )
        = ( k2_relat_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('31',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('35',plain,(
    ! [X33: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k2_relat_1 @ X33 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('36',plain,(
    ! [X46: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X46 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('37',plain,(
    ! [X59: $i] :
      ( ( k6_partfun1 @ X59 )
      = ( k6_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('38',plain,(
    ! [X46: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X46 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X46 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('39',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v4_relat_1 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('41',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('44',plain,(
    ! [X59: $i] :
      ( ( k6_partfun1 @ X59 )
      = ( k6_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('45',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X27 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('46',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('47',plain,(
    ! [X59: $i] :
      ( ( k6_partfun1 @ X59 )
      = ( k6_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('48',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X20 ) )
      = X20 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['42','45','48'])).

thf('50',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['33','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('57',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('59',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['55','60','61','62'])).

thf('64',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('65',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['28','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X20 ) )
      = X20 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('71',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X27 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    v4_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_B ),
    inference('sup-',[status(thm)],['69','74'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('76',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('77',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k7_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X27 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('79',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    = ( k7_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k7_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['27','79'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['31','32'])).

thf('82',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('83',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k6_partfun1 @ X0 )
        = ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X27 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k6_partfun1 @ X0 )
      = ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['80','81','86','87','88','89'])).

thf('91',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X20 ) )
      = X20 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('92',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X20 ) )
      = X20 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('94',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('95',plain,(
    ! [X64: $i] :
      ( ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X64 ) @ ( k2_relat_1 @ X64 ) ) ) )
      | ~ ( v1_funct_1 @ X64 )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('96',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['26','96'])).

thf('98',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('99',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['25','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('103',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('106',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('108',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X33: $i] :
      ( ~ ( v2_funct_1 @ X33 )
      | ( ( k1_relat_1 @ X33 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('116',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('117',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('119',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['117','118','119','120'])).

thf('122',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','121'])).

thf('123',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('124',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('127',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','127'])).

thf('129',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('130',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('131',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['128','129','130','131','132'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('134',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X24 @ ( k1_relat_1 @ X25 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X25 @ X24 ) )
        = X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('135',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('137',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['21','137'])).

thf('139',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['31','32'])).

thf('140',plain,(
    ! [X64: $i] :
      ( ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X64 ) @ ( k2_relat_1 @ X64 ) ) ) )
      | ~ ( v1_funct_1 @ X64 )
      | ~ ( v1_relat_1 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('141',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('143',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v4_relat_1 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('146',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('148',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('150',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('152',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['138','150','151','152','153'])).

thf('155',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['20','154'])).

thf('156',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('157',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['19','157'])).

thf('159',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('160',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['18','161'])).

thf('163',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('164',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['162','163','164','165'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('167',plain,(
    ! [X23: $i] :
      ( ( ( k5_relat_1 @ X23 @ ( k6_relat_1 @ ( k2_relat_1 @ X23 ) ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('168',plain,(
    ! [X59: $i] :
      ( ( k6_partfun1 @ X59 )
      = ( k6_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('169',plain,(
    ! [X23: $i] :
      ( ( ( k5_relat_1 @ X23 @ ( k6_partfun1 @ ( k2_relat_1 @ X23 ) ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['166','169'])).

thf('171',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('172',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v4_relat_1 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('175',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('177',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('180',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('182',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['177','182'])).

thf('184',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('185',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X29 @ ( k2_relat_1 @ X30 ) )
      | ( ( k9_relat_1 @ X30 @ ( k10_relat_1 @ X30 @ X29 ) )
        = X29 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('188',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('190',plain,
    ( ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['183','189'])).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('191',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k10_relat_1 @ X14 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('192',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('194',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i,X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X48 @ X49 @ X51 @ X52 @ X47 @ X50 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('195',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['195','196'])).

thf('198',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['192','197'])).

thf('199',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('202',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i,X57: $i,X58: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_funct_1 @ X56 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) )
      | ( ( k1_partfun1 @ X54 @ X55 @ X57 @ X58 @ X53 @ X56 )
        = ( k5_relat_1 @ X53 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('203',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['203','204'])).

thf('206',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['200','205'])).

thf('207',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['198','199','208'])).

thf('210',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v4_relat_1 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('211',plain,(
    v4_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ sk_A ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('213',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['198','199','208'])).

thf('215',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('216',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('218',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ sk_A ),
    inference(demod,[status(thm)],['213','218'])).

thf('220',plain,
    ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['191','219'])).

thf('221',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('222',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['180','181'])).

thf('223',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) @ sk_A ),
    inference(demod,[status(thm)],['220','221','222'])).

thf('224',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('225',plain,(
    v4_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) @ sk_A ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('227',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) )
    | ( ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
      = ( k7_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X27 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('229',plain,
    ( ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) )
    = ( k7_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['227','228'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('230',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('231',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) )
      = ( k9_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) ) ),
    inference('sup+',[status(thm)],['229','230'])).

thf('232',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('233',plain,(
    ! [X59: $i] :
      ( ( k6_partfun1 @ X59 )
      = ( k6_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('234',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X21 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k10_relat_1 @ X14 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('236',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ sk_A ),
    inference(demod,[status(thm)],['213','218'])).

thf('237',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('238',plain,(
    v4_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) @ sk_A ),
    inference('sup-',[status(thm)],['236','237'])).

thf('239',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('240',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) )
    | ( ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
      = ( k7_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X27 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('242',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    = ( k7_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['240','241'])).

thf('243',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('244',plain,
    ( ( ( k2_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) )
      = ( k9_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) ) ),
    inference('sup+',[status(thm)],['242','243'])).

thf('245',plain,(
    ! [X21: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X21 ) )
      = X21 ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('246',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X27 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('247',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    = ( k9_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['244','245','246'])).

thf('248',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
      = ( k9_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['235','247'])).

thf('249',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('250',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['180','181'])).

thf('251',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    = ( k9_relat_1 @ ( k6_partfun1 @ ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['248','249','250'])).

thf('252',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X27 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('253',plain,
    ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) )
    = ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['231','234','251','252'])).

thf('254',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('256',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['254','255'])).

thf('257',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['198','199','208'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('258',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( X42 = X45 )
      | ~ ( r2_relset_1 @ X43 @ X44 @ X42 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('259',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['257','258'])).

thf('260',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['256','259'])).

thf('261',plain,(
    ! [X46: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X46 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X46 ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('262',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['260','261'])).

thf('263',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X20 ) )
      = X20 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('264',plain,
    ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) )
    = sk_A ),
    inference(demod,[status(thm)],['253','262','263'])).

thf('265',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['190','264'])).

thf('266',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('267',plain,(
    ! [X23: $i] :
      ( ( ( k5_relat_1 @ X23 @ ( k6_partfun1 @ ( k2_relat_1 @ X23 ) ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('268',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k10_relat_1 @ X14 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('269',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['267','268'])).

thf('270',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X20 ) )
      = X20 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('271',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X27 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('272',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['269','270','271'])).

thf('273',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['272'])).

thf('274',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['266','273'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('275',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('276',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['274','275'])).

thf('277',plain,
    ( ( ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ ( k1_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['265','276'])).

thf('278',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( v4_relat_1 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('280',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['278','279'])).

thf('281',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('282',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['280','281'])).

thf('283',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('284',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['282','283'])).

thf('285',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['282','283'])).

thf('286',plain,
    ( ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ sk_D ) )
    = sk_A ),
    inference(demod,[status(thm)],['253','262','263'])).

thf('287',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('288',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['277','284','285','286','287'])).

thf('289',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['172','288'])).

thf('290',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['260','261'])).

thf('291',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('292',plain,(
    ! [X26: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('293',plain,(
    ! [X35: $i] :
      ( ~ ( v2_funct_1 @ X35 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X35 ) )
        = X35 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('294',plain,(
    ! [X35: $i] :
      ( ~ ( v2_funct_1 @ X35 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X35 ) )
        = X35 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('295',plain,(
    ! [X35: $i] :
      ( ~ ( v2_funct_1 @ X35 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X35 ) )
        = X35 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('296',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['138','150','151','152','153'])).

thf('297',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('298',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('299',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['297','298'])).

thf('300',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['299'])).

thf('301',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('302',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['300','301'])).

thf('303',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['302'])).

thf('304',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['296','303'])).

thf('305',plain,(
    ! [X35: $i] :
      ( ~ ( v2_funct_1 @ X35 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X35 ) )
        = X35 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('306',plain,(
    ! [X35: $i] :
      ( ~ ( v2_funct_1 @ X35 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X35 ) )
        = X35 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('307',plain,(
    ! [X35: $i] :
      ( ~ ( v2_funct_1 @ X35 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X35 ) )
        = X35 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('308',plain,(
    ! [X26: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('309',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('310',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('311',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('312',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('313',plain,(
    ! [X26: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('314',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('315',plain,(
    ! [X35: $i] :
      ( ~ ( v2_funct_1 @ X35 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X35 ) )
        = X35 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('316',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('317',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['315','316'])).

thf('318',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['314','317'])).

thf('319',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['318'])).

thf('320',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['313','319'])).

thf('321',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['320'])).

thf('322',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['312','321'])).

thf('323',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['322'])).

thf('324',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('325',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['323','324'])).

thf('326',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['325'])).

thf('327',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['311','326'])).

thf('328',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['310','327'])).

thf('329',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('330',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('331',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['328','329','330'])).

thf('332',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['309','331'])).

thf('333',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('334',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('335',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('336',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['332','333','334','335'])).

thf('337',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['308','336'])).

thf('338',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('339',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('340',plain,(
    r1_tarski @ sk_B @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['337','338','339'])).

thf('341',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X29 @ ( k2_relat_1 @ X30 ) )
      | ( ( k9_relat_1 @ X30 @ ( k10_relat_1 @ X30 @ X29 ) )
        = X29 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('342',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k10_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['340','341'])).

thf('343',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k10_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) )
      = sk_B )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['307','342'])).

thf('344',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('345',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('346',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('347',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('348',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k10_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) )
      = sk_B )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['343','344','345','346','347'])).

thf('349',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k10_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['306','348'])).

thf('350',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('351',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('352',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('353',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('354',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k10_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['349','350','351','352','353'])).

thf('355',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
      = sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['305','354'])).

thf('356',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['31','32'])).

thf('357',plain,(
    ! [X23: $i] :
      ( ( ( k5_relat_1 @ X23 @ ( k6_partfun1 @ ( k2_relat_1 @ X23 ) ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('358',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['356','357'])).

thf('359',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('360',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['358','359'])).

thf('361',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k10_relat_1 @ X14 @ ( k1_relat_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf('362',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k10_relat_1 @ sk_C @ ( k1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['360','361'])).

thf('363',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X20 ) )
      = X20 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('364',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('365',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X27 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('366',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['362','363','364','365'])).

thf('367',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('368',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('369',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('370',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['355','366','367','368','369'])).

thf('371',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = sk_B )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['304','370'])).

thf('372',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['295','371'])).

thf('373',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('374',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('375',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('376',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('377',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    = sk_B ),
    inference(demod,[status(thm)],['372','373','374','375','376'])).

thf('378',plain,(
    ! [X23: $i] :
      ( ( ( k5_relat_1 @ X23 @ ( k6_partfun1 @ ( k2_relat_1 @ X23 ) ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('379',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_B ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['377','378'])).

thf('380',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_B ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['294','379'])).

thf('381',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('382',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('383',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('384',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('385',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k6_partfun1 @ sk_B ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['380','381','382','383','384'])).

thf('386',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['293','385'])).

thf('387',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['358','359'])).

thf('388',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('389',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('390',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('391',plain,
    ( sk_C
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['386','387','388','389','390'])).

thf('392',plain,(
    ! [X34: $i] :
      ( ~ ( v2_funct_1 @ X34 )
      | ( ( k5_relat_1 @ X34 @ ( k2_funct_1 @ X34 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('393',plain,(
    ! [X59: $i] :
      ( ( k6_partfun1 @ X59 )
      = ( k6_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('394',plain,(
    ! [X34: $i] :
      ( ~ ( v2_funct_1 @ X34 )
      | ( ( k5_relat_1 @ X34 @ ( k2_funct_1 @ X34 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(demod,[status(thm)],['392','393'])).

thf('395',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['391','394'])).

thf('396',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('397',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('398',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['395','396','397'])).

thf('399',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['292','398'])).

thf('400',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('401',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('402',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['399','400','401'])).

thf('403',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['291','402'])).

thf('404',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('405',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('406',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('407',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['403','404','405','406'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('408',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) @ X19 )
        = ( k5_relat_1 @ X18 @ ( k5_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('409',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['407','408'])).

thf('410',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('411',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('412',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['409','410','411'])).

thf('413',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['290','412'])).

thf('414',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['180','181'])).

thf('415',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['413','414'])).

thf('416',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['173','174'])).

thf('417',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('418',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['416','417'])).

thf('419',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['180','181'])).

thf('420',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['418','419'])).

thf('421',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('422',plain,(
    ! [X23: $i] :
      ( ( ( k5_relat_1 @ X23 @ ( k6_partfun1 @ ( k2_relat_1 @ X23 ) ) )
        = X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('423',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k6_partfun1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
        = ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['421','422'])).

thf('424',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('425',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k6_partfun1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
        = ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['423','424'])).

thf('426',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k9_relat_1 @ sk_D @ sk_B ) ) )
      = ( k7_relat_1 @ sk_D @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['420','425'])).

thf('427',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['418','419'])).

thf('428',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('429',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k9_relat_1 @ sk_D @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['427','428'])).

thf('430',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['180','181'])).

thf('431',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['429','430'])).

thf('432',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['418','419'])).

thf('433',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['180','181'])).

thf('434',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    = sk_D ),
    inference(demod,[status(thm)],['426','431','432','433'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('435',plain,(
    ! [X22: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X22 ) ) @ X22 )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('436',plain,(
    ! [X59: $i] :
      ( ( k6_partfun1 @ X59 )
      = ( k6_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('437',plain,(
    ! [X22: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X22 ) ) @ X22 )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(demod,[status(thm)],['435','436'])).

thf('438',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) @ X19 )
        = ( k5_relat_1 @ X18 @ ( k5_relat_1 @ X17 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('439',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['437','438'])).

thf('440',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X27 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('441',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['439','440'])).

thf('442',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['441'])).

thf('443',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
      = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['434','442'])).

thf('444',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    = sk_D ),
    inference(demod,[status(thm)],['426','431','432','433'])).

thf('445',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['180','181'])).

thf('446',plain,(
    ! [X27: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X27 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('447',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['443','444','445','446'])).

thf('448',plain,
    ( ( k9_relat_1 @ sk_C @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['190','264'])).

thf('449',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['282','283'])).

thf('450',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('451',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['449','450'])).

thf('452',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('453',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['451','452'])).

thf('454',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['31','32'])).

thf('455',plain,
    ( sk_B
    = ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['453','454'])).

thf('456',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['448','455'])).

thf('457',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D ) ),
    inference(demod,[status(thm)],['447','456'])).

thf('458',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['415','457'])).

thf('459',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['289','458'])).

thf('460',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('461',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['459','460'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.807ArKXnNr
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:33:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.99/4.20  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.99/4.20  % Solved by: fo/fo7.sh
% 3.99/4.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.99/4.20  % done 3677 iterations in 3.734s
% 3.99/4.20  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.99/4.20  % SZS output start Refutation
% 3.99/4.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.99/4.20  thf(sk_A_type, type, sk_A: $i).
% 3.99/4.20  thf(sk_D_type, type, sk_D: $i).
% 3.99/4.20  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 3.99/4.20  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.99/4.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.99/4.20  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.99/4.20  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.99/4.20  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.99/4.20  thf(sk_B_type, type, sk_B: $i).
% 3.99/4.20  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 3.99/4.20  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.99/4.20  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.99/4.20  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.99/4.20  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.99/4.20  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.99/4.20  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.99/4.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.99/4.20  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 3.99/4.20  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.99/4.20  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 3.99/4.20  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.99/4.20  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.99/4.20  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.99/4.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.99/4.20  thf(sk_C_type, type, sk_C: $i).
% 3.99/4.20  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.99/4.20  thf(t55_funct_1, axiom,
% 3.99/4.20    (![A:$i]:
% 3.99/4.20     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.99/4.20       ( ( v2_funct_1 @ A ) =>
% 3.99/4.20         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 3.99/4.20           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 3.99/4.20  thf('0', plain,
% 3.99/4.20      (![X33 : $i]:
% 3.99/4.20         (~ (v2_funct_1 @ X33)
% 3.99/4.20          | ((k1_relat_1 @ X33) = (k2_relat_1 @ (k2_funct_1 @ X33)))
% 3.99/4.20          | ~ (v1_funct_1 @ X33)
% 3.99/4.20          | ~ (v1_relat_1 @ X33))),
% 3.99/4.20      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.99/4.20  thf(dt_k2_funct_1, axiom,
% 3.99/4.20    (![A:$i]:
% 3.99/4.20     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.99/4.20       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 3.99/4.20         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 3.99/4.20  thf('1', plain,
% 3.99/4.20      (![X26 : $i]:
% 3.99/4.20         ((v1_funct_1 @ (k2_funct_1 @ X26))
% 3.99/4.20          | ~ (v1_funct_1 @ X26)
% 3.99/4.20          | ~ (v1_relat_1 @ X26))),
% 3.99/4.20      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.99/4.20  thf('2', plain,
% 3.99/4.20      (![X26 : $i]:
% 3.99/4.20         ((v1_relat_1 @ (k2_funct_1 @ X26))
% 3.99/4.20          | ~ (v1_funct_1 @ X26)
% 3.99/4.20          | ~ (v1_relat_1 @ X26))),
% 3.99/4.20      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.99/4.20  thf(t61_funct_1, axiom,
% 3.99/4.20    (![A:$i]:
% 3.99/4.20     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.99/4.20       ( ( v2_funct_1 @ A ) =>
% 3.99/4.20         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 3.99/4.20             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 3.99/4.20           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 3.99/4.20             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 3.99/4.20  thf('3', plain,
% 3.99/4.20      (![X34 : $i]:
% 3.99/4.20         (~ (v2_funct_1 @ X34)
% 3.99/4.20          | ((k5_relat_1 @ (k2_funct_1 @ X34) @ X34)
% 3.99/4.20              = (k6_relat_1 @ (k2_relat_1 @ X34)))
% 3.99/4.20          | ~ (v1_funct_1 @ X34)
% 3.99/4.20          | ~ (v1_relat_1 @ X34))),
% 3.99/4.20      inference('cnf', [status(esa)], [t61_funct_1])).
% 3.99/4.20  thf(redefinition_k6_partfun1, axiom,
% 3.99/4.20    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.99/4.20  thf('4', plain, (![X59 : $i]: ((k6_partfun1 @ X59) = (k6_relat_1 @ X59))),
% 3.99/4.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.99/4.20  thf('5', plain,
% 3.99/4.20      (![X34 : $i]:
% 3.99/4.20         (~ (v2_funct_1 @ X34)
% 3.99/4.20          | ((k5_relat_1 @ (k2_funct_1 @ X34) @ X34)
% 3.99/4.20              = (k6_partfun1 @ (k2_relat_1 @ X34)))
% 3.99/4.20          | ~ (v1_funct_1 @ X34)
% 3.99/4.20          | ~ (v1_relat_1 @ X34))),
% 3.99/4.20      inference('demod', [status(thm)], ['3', '4'])).
% 3.99/4.20  thf(t48_funct_1, axiom,
% 3.99/4.20    (![A:$i]:
% 3.99/4.20     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.99/4.20       ( ![B:$i]:
% 3.99/4.20         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.99/4.20           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 3.99/4.20               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 3.99/4.20             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 3.99/4.20  thf('6', plain,
% 3.99/4.20      (![X31 : $i, X32 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X31)
% 3.99/4.20          | ~ (v1_funct_1 @ X31)
% 3.99/4.20          | (v2_funct_1 @ X31)
% 3.99/4.20          | ((k2_relat_1 @ X31) != (k1_relat_1 @ X32))
% 3.99/4.20          | ~ (v2_funct_1 @ (k5_relat_1 @ X31 @ X32))
% 3.99/4.20          | ~ (v1_funct_1 @ X32)
% 3.99/4.20          | ~ (v1_relat_1 @ X32))),
% 3.99/4.20      inference('cnf', [status(esa)], [t48_funct_1])).
% 3.99/4.20  thf('7', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (~ (v2_funct_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 3.99/4.20          | ~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 3.99/4.20          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['5', '6'])).
% 3.99/4.20  thf(fc4_funct_1, axiom,
% 3.99/4.20    (![A:$i]:
% 3.99/4.20     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.99/4.20       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.99/4.20  thf('8', plain, (![X28 : $i]: (v2_funct_1 @ (k6_relat_1 @ X28))),
% 3.99/4.20      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.99/4.20  thf('9', plain, (![X59 : $i]: ((k6_partfun1 @ X59) = (k6_relat_1 @ X59))),
% 3.99/4.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.99/4.20  thf('10', plain, (![X28 : $i]: (v2_funct_1 @ (k6_partfun1 @ X28))),
% 3.99/4.20      inference('demod', [status(thm)], ['8', '9'])).
% 3.99/4.20  thf('11', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 3.99/4.20          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 3.99/4.20      inference('demod', [status(thm)], ['7', '10'])).
% 3.99/4.20  thf('12', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0))),
% 3.99/4.20      inference('simplify', [status(thm)], ['11'])).
% 3.99/4.20  thf('13', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 3.99/4.20          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['2', '12'])).
% 3.99/4.20  thf('14', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0))),
% 3.99/4.20      inference('simplify', [status(thm)], ['13'])).
% 3.99/4.20  thf('15', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 3.99/4.20          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['1', '14'])).
% 3.99/4.20  thf('16', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0))),
% 3.99/4.20      inference('simplify', [status(thm)], ['15'])).
% 3.99/4.20  thf('17', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 3.99/4.20          | ~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['0', '16'])).
% 3.99/4.20  thf('18', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0))),
% 3.99/4.20      inference('simplify', [status(thm)], ['17'])).
% 3.99/4.20  thf('19', plain,
% 3.99/4.20      (![X26 : $i]:
% 3.99/4.20         ((v1_funct_1 @ (k2_funct_1 @ X26))
% 3.99/4.20          | ~ (v1_funct_1 @ X26)
% 3.99/4.20          | ~ (v1_relat_1 @ X26))),
% 3.99/4.20      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.99/4.20  thf('20', plain,
% 3.99/4.20      (![X33 : $i]:
% 3.99/4.20         (~ (v2_funct_1 @ X33)
% 3.99/4.20          | ((k2_relat_1 @ X33) = (k1_relat_1 @ (k2_funct_1 @ X33)))
% 3.99/4.20          | ~ (v1_funct_1 @ X33)
% 3.99/4.20          | ~ (v1_relat_1 @ X33))),
% 3.99/4.20      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.99/4.20  thf(t65_funct_1, axiom,
% 3.99/4.20    (![A:$i]:
% 3.99/4.20     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.99/4.20       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 3.99/4.20  thf('21', plain,
% 3.99/4.20      (![X35 : $i]:
% 3.99/4.20         (~ (v2_funct_1 @ X35)
% 3.99/4.20          | ((k2_funct_1 @ (k2_funct_1 @ X35)) = (X35))
% 3.99/4.20          | ~ (v1_funct_1 @ X35)
% 3.99/4.20          | ~ (v1_relat_1 @ X35))),
% 3.99/4.20      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.99/4.20  thf('22', plain,
% 3.99/4.20      (![X35 : $i]:
% 3.99/4.20         (~ (v2_funct_1 @ X35)
% 3.99/4.20          | ((k2_funct_1 @ (k2_funct_1 @ X35)) = (X35))
% 3.99/4.20          | ~ (v1_funct_1 @ X35)
% 3.99/4.20          | ~ (v1_relat_1 @ X35))),
% 3.99/4.20      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.99/4.20  thf('23', plain,
% 3.99/4.20      (![X26 : $i]:
% 3.99/4.20         ((v1_funct_1 @ (k2_funct_1 @ X26))
% 3.99/4.20          | ~ (v1_funct_1 @ X26)
% 3.99/4.20          | ~ (v1_relat_1 @ X26))),
% 3.99/4.20      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.99/4.20  thf('24', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0))),
% 3.99/4.20      inference('simplify', [status(thm)], ['17'])).
% 3.99/4.20  thf('25', plain,
% 3.99/4.20      (![X26 : $i]:
% 3.99/4.20         ((v1_funct_1 @ (k2_funct_1 @ X26))
% 3.99/4.20          | ~ (v1_funct_1 @ X26)
% 3.99/4.20          | ~ (v1_relat_1 @ X26))),
% 3.99/4.20      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.99/4.20  thf('26', plain,
% 3.99/4.20      (![X26 : $i]:
% 3.99/4.20         ((v1_relat_1 @ (k2_funct_1 @ X26))
% 3.99/4.20          | ~ (v1_funct_1 @ X26)
% 3.99/4.20          | ~ (v1_relat_1 @ X26))),
% 3.99/4.20      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.99/4.20  thf('27', plain,
% 3.99/4.20      (![X33 : $i]:
% 3.99/4.20         (~ (v2_funct_1 @ X33)
% 3.99/4.20          | ((k2_relat_1 @ X33) = (k1_relat_1 @ (k2_funct_1 @ X33)))
% 3.99/4.20          | ~ (v1_funct_1 @ X33)
% 3.99/4.20          | ~ (v1_relat_1 @ X33))),
% 3.99/4.20      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.99/4.20  thf('28', plain,
% 3.99/4.20      (![X26 : $i]:
% 3.99/4.20         ((v1_relat_1 @ (k2_funct_1 @ X26))
% 3.99/4.20          | ~ (v1_funct_1 @ X26)
% 3.99/4.20          | ~ (v1_relat_1 @ X26))),
% 3.99/4.20      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.99/4.20  thf(t36_funct_2, conjecture,
% 3.99/4.20    (![A:$i,B:$i,C:$i]:
% 3.99/4.20     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.99/4.20         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.99/4.20       ( ![D:$i]:
% 3.99/4.20         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.99/4.20             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.99/4.20           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 3.99/4.20               ( r2_relset_1 @
% 3.99/4.20                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.99/4.20                 ( k6_partfun1 @ A ) ) & 
% 3.99/4.20               ( v2_funct_1 @ C ) ) =>
% 3.99/4.20             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.99/4.20               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 3.99/4.20  thf(zf_stmt_0, negated_conjecture,
% 3.99/4.20    (~( ![A:$i,B:$i,C:$i]:
% 3.99/4.20        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.99/4.20            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.99/4.20          ( ![D:$i]:
% 3.99/4.20            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.99/4.20                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.99/4.20              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 3.99/4.20                  ( r2_relset_1 @
% 3.99/4.20                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.99/4.20                    ( k6_partfun1 @ A ) ) & 
% 3.99/4.20                  ( v2_funct_1 @ C ) ) =>
% 3.99/4.20                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 3.99/4.20                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 3.99/4.20    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 3.99/4.20  thf('29', plain,
% 3.99/4.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf(redefinition_k2_relset_1, axiom,
% 3.99/4.20    (![A:$i,B:$i,C:$i]:
% 3.99/4.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.99/4.20       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.99/4.20  thf('30', plain,
% 3.99/4.20      (![X39 : $i, X40 : $i, X41 : $i]:
% 3.99/4.20         (((k2_relset_1 @ X40 @ X41 @ X39) = (k2_relat_1 @ X39))
% 3.99/4.20          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 3.99/4.20      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.99/4.20  thf('31', plain,
% 3.99/4.20      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 3.99/4.20      inference('sup-', [status(thm)], ['29', '30'])).
% 3.99/4.20  thf('32', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('33', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.99/4.20      inference('sup+', [status(thm)], ['31', '32'])).
% 3.99/4.20  thf('34', plain,
% 3.99/4.20      (![X26 : $i]:
% 3.99/4.20         ((v1_relat_1 @ (k2_funct_1 @ X26))
% 3.99/4.20          | ~ (v1_funct_1 @ X26)
% 3.99/4.20          | ~ (v1_relat_1 @ X26))),
% 3.99/4.20      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.99/4.20  thf('35', plain,
% 3.99/4.20      (![X33 : $i]:
% 3.99/4.20         (~ (v2_funct_1 @ X33)
% 3.99/4.20          | ((k2_relat_1 @ X33) = (k1_relat_1 @ (k2_funct_1 @ X33)))
% 3.99/4.20          | ~ (v1_funct_1 @ X33)
% 3.99/4.20          | ~ (v1_relat_1 @ X33))),
% 3.99/4.20      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.99/4.20  thf(t29_relset_1, axiom,
% 3.99/4.20    (![A:$i]:
% 3.99/4.20     ( m1_subset_1 @
% 3.99/4.20       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 3.99/4.20  thf('36', plain,
% 3.99/4.20      (![X46 : $i]:
% 3.99/4.20         (m1_subset_1 @ (k6_relat_1 @ X46) @ 
% 3.99/4.20          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X46)))),
% 3.99/4.20      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.99/4.20  thf('37', plain, (![X59 : $i]: ((k6_partfun1 @ X59) = (k6_relat_1 @ X59))),
% 3.99/4.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.99/4.20  thf('38', plain,
% 3.99/4.20      (![X46 : $i]:
% 3.99/4.20         (m1_subset_1 @ (k6_partfun1 @ X46) @ 
% 3.99/4.20          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X46)))),
% 3.99/4.20      inference('demod', [status(thm)], ['36', '37'])).
% 3.99/4.20  thf(cc2_relset_1, axiom,
% 3.99/4.20    (![A:$i,B:$i,C:$i]:
% 3.99/4.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.99/4.20       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.99/4.20  thf('39', plain,
% 3.99/4.20      (![X36 : $i, X37 : $i, X38 : $i]:
% 3.99/4.20         ((v4_relat_1 @ X36 @ X37)
% 3.99/4.20          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 3.99/4.20      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.99/4.20  thf('40', plain, (![X0 : $i]: (v4_relat_1 @ (k6_partfun1 @ X0) @ X0)),
% 3.99/4.20      inference('sup-', [status(thm)], ['38', '39'])).
% 3.99/4.20  thf(d18_relat_1, axiom,
% 3.99/4.20    (![A:$i,B:$i]:
% 3.99/4.20     ( ( v1_relat_1 @ B ) =>
% 3.99/4.20       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 3.99/4.20  thf('41', plain,
% 3.99/4.20      (![X5 : $i, X6 : $i]:
% 3.99/4.20         (~ (v4_relat_1 @ X5 @ X6)
% 3.99/4.20          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 3.99/4.20          | ~ (v1_relat_1 @ X5))),
% 3.99/4.20      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.99/4.20  thf('42', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 3.99/4.20          | (r1_tarski @ (k1_relat_1 @ (k6_partfun1 @ X0)) @ X0))),
% 3.99/4.20      inference('sup-', [status(thm)], ['40', '41'])).
% 3.99/4.20  thf('43', plain, (![X27 : $i]: (v1_relat_1 @ (k6_relat_1 @ X27))),
% 3.99/4.20      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.99/4.20  thf('44', plain, (![X59 : $i]: ((k6_partfun1 @ X59) = (k6_relat_1 @ X59))),
% 3.99/4.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.99/4.20  thf('45', plain, (![X27 : $i]: (v1_relat_1 @ (k6_partfun1 @ X27))),
% 3.99/4.20      inference('demod', [status(thm)], ['43', '44'])).
% 3.99/4.20  thf(t71_relat_1, axiom,
% 3.99/4.20    (![A:$i]:
% 3.99/4.20     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 3.99/4.20       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 3.99/4.20  thf('46', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X20)) = (X20))),
% 3.99/4.20      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.99/4.20  thf('47', plain, (![X59 : $i]: ((k6_partfun1 @ X59) = (k6_relat_1 @ X59))),
% 3.99/4.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.99/4.20  thf('48', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X20)) = (X20))),
% 3.99/4.20      inference('demod', [status(thm)], ['46', '47'])).
% 3.99/4.20  thf('49', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 3.99/4.20      inference('demod', [status(thm)], ['42', '45', '48'])).
% 3.99/4.20  thf('50', plain,
% 3.99/4.20      (![X5 : $i, X6 : $i]:
% 3.99/4.20         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 3.99/4.20          | (v4_relat_1 @ X5 @ X6)
% 3.99/4.20          | ~ (v1_relat_1 @ X5))),
% 3.99/4.20      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.99/4.20  thf('51', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['49', '50'])).
% 3.99/4.20  thf('52', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 3.99/4.20          | ~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 3.99/4.20      inference('sup+', [status(thm)], ['35', '51'])).
% 3.99/4.20  thf('53', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0)
% 3.99/4.20          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['34', '52'])).
% 3.99/4.20  thf('54', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0))),
% 3.99/4.20      inference('simplify', [status(thm)], ['53'])).
% 3.99/4.20  thf('55', plain,
% 3.99/4.20      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 3.99/4.20        | ~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ sk_C)
% 3.99/4.20        | ~ (v2_funct_1 @ sk_C))),
% 3.99/4.20      inference('sup+', [status(thm)], ['33', '54'])).
% 3.99/4.20  thf('56', plain,
% 3.99/4.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf(cc2_relat_1, axiom,
% 3.99/4.20    (![A:$i]:
% 3.99/4.20     ( ( v1_relat_1 @ A ) =>
% 3.99/4.20       ( ![B:$i]:
% 3.99/4.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.99/4.20  thf('57', plain,
% 3.99/4.20      (![X3 : $i, X4 : $i]:
% 3.99/4.20         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 3.99/4.20          | (v1_relat_1 @ X3)
% 3.99/4.20          | ~ (v1_relat_1 @ X4))),
% 3.99/4.20      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.99/4.20  thf('58', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 3.99/4.20      inference('sup-', [status(thm)], ['56', '57'])).
% 3.99/4.20  thf(fc6_relat_1, axiom,
% 3.99/4.20    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.99/4.20  thf('59', plain,
% 3.99/4.20      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 3.99/4.20      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.99/4.20  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('61', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('62', plain, ((v2_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('63', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 3.99/4.20      inference('demod', [status(thm)], ['55', '60', '61', '62'])).
% 3.99/4.20  thf('64', plain,
% 3.99/4.20      (![X5 : $i, X6 : $i]:
% 3.99/4.20         (~ (v4_relat_1 @ X5 @ X6)
% 3.99/4.20          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 3.99/4.20          | ~ (v1_relat_1 @ X5))),
% 3.99/4.20      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.99/4.20  thf('65', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 3.99/4.20      inference('sup-', [status(thm)], ['63', '64'])).
% 3.99/4.20  thf('66', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ sk_C)
% 3.99/4.20        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 3.99/4.20      inference('sup-', [status(thm)], ['28', '65'])).
% 3.99/4.20  thf('67', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('69', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 3.99/4.20      inference('demod', [status(thm)], ['66', '67', '68'])).
% 3.99/4.20  thf('70', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X20)) = (X20))),
% 3.99/4.20      inference('demod', [status(thm)], ['46', '47'])).
% 3.99/4.20  thf('71', plain,
% 3.99/4.20      (![X5 : $i, X6 : $i]:
% 3.99/4.20         (~ (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 3.99/4.20          | (v4_relat_1 @ X5 @ X6)
% 3.99/4.20          | ~ (v1_relat_1 @ X5))),
% 3.99/4.20      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.99/4.20  thf('72', plain,
% 3.99/4.20      (![X0 : $i, X1 : $i]:
% 3.99/4.20         (~ (r1_tarski @ X0 @ X1)
% 3.99/4.20          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 3.99/4.20          | (v4_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 3.99/4.20      inference('sup-', [status(thm)], ['70', '71'])).
% 3.99/4.20  thf('73', plain, (![X27 : $i]: (v1_relat_1 @ (k6_partfun1 @ X27))),
% 3.99/4.20      inference('demod', [status(thm)], ['43', '44'])).
% 3.99/4.20  thf('74', plain,
% 3.99/4.20      (![X0 : $i, X1 : $i]:
% 3.99/4.20         (~ (r1_tarski @ X0 @ X1) | (v4_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 3.99/4.20      inference('demod', [status(thm)], ['72', '73'])).
% 3.99/4.20  thf('75', plain,
% 3.99/4.20      ((v4_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) @ sk_B)),
% 3.99/4.20      inference('sup-', [status(thm)], ['69', '74'])).
% 3.99/4.20  thf(t209_relat_1, axiom,
% 3.99/4.20    (![A:$i,B:$i]:
% 3.99/4.20     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 3.99/4.20       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 3.99/4.20  thf('76', plain,
% 3.99/4.20      (![X15 : $i, X16 : $i]:
% 3.99/4.20         (((X15) = (k7_relat_1 @ X15 @ X16))
% 3.99/4.20          | ~ (v4_relat_1 @ X15 @ X16)
% 3.99/4.20          | ~ (v1_relat_1 @ X15))),
% 3.99/4.20      inference('cnf', [status(esa)], [t209_relat_1])).
% 3.99/4.20  thf('77', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 3.99/4.20        | ((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 3.99/4.20            = (k7_relat_1 @ 
% 3.99/4.20               (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) @ sk_B)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['75', '76'])).
% 3.99/4.20  thf('78', plain, (![X27 : $i]: (v1_relat_1 @ (k6_partfun1 @ X27))),
% 3.99/4.20      inference('demod', [status(thm)], ['43', '44'])).
% 3.99/4.20  thf('79', plain,
% 3.99/4.20      (((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 3.99/4.20         = (k7_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))) @ 
% 3.99/4.20            sk_B))),
% 3.99/4.20      inference('demod', [status(thm)], ['77', '78'])).
% 3.99/4.20  thf('80', plain,
% 3.99/4.20      ((((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 3.99/4.20          = (k7_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ sk_B))
% 3.99/4.20        | ~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ sk_C)
% 3.99/4.20        | ~ (v2_funct_1 @ sk_C))),
% 3.99/4.20      inference('sup+', [status(thm)], ['27', '79'])).
% 3.99/4.20  thf('81', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.99/4.20      inference('sup+', [status(thm)], ['31', '32'])).
% 3.99/4.20  thf('82', plain, (![X0 : $i]: (v4_relat_1 @ (k6_partfun1 @ X0) @ X0)),
% 3.99/4.20      inference('sup-', [status(thm)], ['38', '39'])).
% 3.99/4.20  thf('83', plain,
% 3.99/4.20      (![X15 : $i, X16 : $i]:
% 3.99/4.20         (((X15) = (k7_relat_1 @ X15 @ X16))
% 3.99/4.20          | ~ (v4_relat_1 @ X15 @ X16)
% 3.99/4.20          | ~ (v1_relat_1 @ X15))),
% 3.99/4.20      inference('cnf', [status(esa)], [t209_relat_1])).
% 3.99/4.20  thf('84', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 3.99/4.20          | ((k6_partfun1 @ X0) = (k7_relat_1 @ (k6_partfun1 @ X0) @ X0)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['82', '83'])).
% 3.99/4.20  thf('85', plain, (![X27 : $i]: (v1_relat_1 @ (k6_partfun1 @ X27))),
% 3.99/4.20      inference('demod', [status(thm)], ['43', '44'])).
% 3.99/4.20  thf('86', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         ((k6_partfun1 @ X0) = (k7_relat_1 @ (k6_partfun1 @ X0) @ X0))),
% 3.99/4.20      inference('demod', [status(thm)], ['84', '85'])).
% 3.99/4.20  thf('87', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('89', plain, ((v2_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('90', plain,
% 3.99/4.20      (((k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 3.99/4.20         = (k6_partfun1 @ sk_B))),
% 3.99/4.20      inference('demod', [status(thm)], ['80', '81', '86', '87', '88', '89'])).
% 3.99/4.20  thf('91', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X20)) = (X20))),
% 3.99/4.20      inference('demod', [status(thm)], ['46', '47'])).
% 3.99/4.20  thf('92', plain,
% 3.99/4.20      (((k1_relat_1 @ (k6_partfun1 @ sk_B))
% 3.99/4.20         = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.99/4.20      inference('sup+', [status(thm)], ['90', '91'])).
% 3.99/4.20  thf('93', plain, (![X20 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X20)) = (X20))),
% 3.99/4.20      inference('demod', [status(thm)], ['46', '47'])).
% 3.99/4.20  thf('94', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.99/4.20      inference('demod', [status(thm)], ['92', '93'])).
% 3.99/4.20  thf(t3_funct_2, axiom,
% 3.99/4.20    (![A:$i]:
% 3.99/4.20     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.99/4.20       ( ( v1_funct_1 @ A ) & 
% 3.99/4.20         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 3.99/4.20         ( m1_subset_1 @
% 3.99/4.20           A @ 
% 3.99/4.20           ( k1_zfmisc_1 @
% 3.99/4.20             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 3.99/4.20  thf('95', plain,
% 3.99/4.20      (![X64 : $i]:
% 3.99/4.20         ((m1_subset_1 @ X64 @ 
% 3.99/4.20           (k1_zfmisc_1 @ 
% 3.99/4.20            (k2_zfmisc_1 @ (k1_relat_1 @ X64) @ (k2_relat_1 @ X64))))
% 3.99/4.20          | ~ (v1_funct_1 @ X64)
% 3.99/4.20          | ~ (v1_relat_1 @ X64))),
% 3.99/4.20      inference('cnf', [status(esa)], [t3_funct_2])).
% 3.99/4.20  thf('96', plain,
% 3.99/4.20      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.99/4.20         (k1_zfmisc_1 @ 
% 3.99/4.20          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 3.99/4.20        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.99/4.20      inference('sup+', [status(thm)], ['94', '95'])).
% 3.99/4.20  thf('97', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.99/4.20           (k1_zfmisc_1 @ 
% 3.99/4.20            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 3.99/4.20      inference('sup-', [status(thm)], ['26', '96'])).
% 3.99/4.20  thf('98', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('99', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('100', plain,
% 3.99/4.20      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.99/4.20           (k1_zfmisc_1 @ 
% 3.99/4.20            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 3.99/4.20      inference('demod', [status(thm)], ['97', '98', '99'])).
% 3.99/4.20  thf('101', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ sk_C)
% 3.99/4.20        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.99/4.20           (k1_zfmisc_1 @ 
% 3.99/4.20            (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))))),
% 3.99/4.20      inference('sup-', [status(thm)], ['25', '100'])).
% 3.99/4.20  thf('102', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('103', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('104', plain,
% 3.99/4.20      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 3.99/4.20        (k1_zfmisc_1 @ 
% 3.99/4.20         (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 3.99/4.20      inference('demod', [status(thm)], ['101', '102', '103'])).
% 3.99/4.20  thf('105', plain,
% 3.99/4.20      (![X3 : $i, X4 : $i]:
% 3.99/4.20         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 3.99/4.20          | (v1_relat_1 @ X3)
% 3.99/4.20          | ~ (v1_relat_1 @ X4))),
% 3.99/4.20      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.99/4.20  thf('106', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ 
% 3.99/4.20           (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 3.99/4.20        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['104', '105'])).
% 3.99/4.20  thf('107', plain,
% 3.99/4.20      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 3.99/4.20      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.99/4.20  thf('108', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 3.99/4.20      inference('demod', [status(thm)], ['106', '107'])).
% 3.99/4.20  thf('109', plain,
% 3.99/4.20      (![X33 : $i]:
% 3.99/4.20         (~ (v2_funct_1 @ X33)
% 3.99/4.20          | ((k1_relat_1 @ X33) = (k2_relat_1 @ (k2_funct_1 @ X33)))
% 3.99/4.20          | ~ (v1_funct_1 @ X33)
% 3.99/4.20          | ~ (v1_relat_1 @ X33))),
% 3.99/4.20      inference('cnf', [status(esa)], [t55_funct_1])).
% 3.99/4.20  thf('110', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0))),
% 3.99/4.20      inference('simplify', [status(thm)], ['53'])).
% 3.99/4.20  thf('111', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 3.99/4.20          | ~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 3.99/4.20      inference('sup+', [status(thm)], ['109', '110'])).
% 3.99/4.20  thf('112', plain,
% 3.99/4.20      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20        | ~ (v2_funct_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ sk_C)
% 3.99/4.20        | ~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.99/4.20           (k1_relat_1 @ sk_C)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['108', '111'])).
% 3.99/4.20  thf('113', plain, ((v2_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('115', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('116', plain,
% 3.99/4.20      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20        | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.99/4.20           (k1_relat_1 @ sk_C)))),
% 3.99/4.20      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 3.99/4.20  thf('117', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ sk_C)
% 3.99/4.20        | ~ (v2_funct_1 @ sk_C)
% 3.99/4.20        | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.99/4.20           (k1_relat_1 @ sk_C))
% 3.99/4.20        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['24', '116'])).
% 3.99/4.20  thf('118', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('119', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('120', plain, ((v2_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('121', plain,
% 3.99/4.20      (((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k1_relat_1 @ sk_C))
% 3.99/4.20        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.99/4.20      inference('demod', [status(thm)], ['117', '118', '119', '120'])).
% 3.99/4.20  thf('122', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ sk_C)
% 3.99/4.20        | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.99/4.20           (k1_relat_1 @ sk_C)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['23', '121'])).
% 3.99/4.20  thf('123', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('124', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('125', plain,
% 3.99/4.20      ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k1_relat_1 @ sk_C))),
% 3.99/4.20      inference('demod', [status(thm)], ['122', '123', '124'])).
% 3.99/4.20  thf('126', plain,
% 3.99/4.20      (![X5 : $i, X6 : $i]:
% 3.99/4.20         (~ (v4_relat_1 @ X5 @ X6)
% 3.99/4.20          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 3.99/4.20          | ~ (v1_relat_1 @ X5))),
% 3.99/4.20      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.99/4.20  thf('127', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.99/4.20        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) @ 
% 3.99/4.20           (k1_relat_1 @ sk_C)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['125', '126'])).
% 3.99/4.20  thf('128', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ sk_C)
% 3.99/4.20        | ~ (v2_funct_1 @ sk_C)
% 3.99/4.20        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) @ 
% 3.99/4.20           (k1_relat_1 @ sk_C)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['22', '127'])).
% 3.99/4.20  thf('129', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('130', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('131', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('132', plain, ((v2_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('133', plain,
% 3.99/4.20      ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) @ 
% 3.99/4.20        (k1_relat_1 @ sk_C))),
% 3.99/4.20      inference('demod', [status(thm)], ['128', '129', '130', '131', '132'])).
% 3.99/4.20  thf(t91_relat_1, axiom,
% 3.99/4.20    (![A:$i,B:$i]:
% 3.99/4.20     ( ( v1_relat_1 @ B ) =>
% 3.99/4.20       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 3.99/4.20         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 3.99/4.20  thf('134', plain,
% 3.99/4.20      (![X24 : $i, X25 : $i]:
% 3.99/4.20         (~ (r1_tarski @ X24 @ (k1_relat_1 @ X25))
% 3.99/4.20          | ((k1_relat_1 @ (k7_relat_1 @ X25 @ X24)) = (X24))
% 3.99/4.20          | ~ (v1_relat_1 @ X25))),
% 3.99/4.20      inference('cnf', [status(esa)], [t91_relat_1])).
% 3.99/4.20  thf('135', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ((k1_relat_1 @ 
% 3.99/4.20            (k7_relat_1 @ sk_C @ 
% 3.99/4.20             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))
% 3.99/4.20            = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 3.99/4.20      inference('sup-', [status(thm)], ['133', '134'])).
% 3.99/4.20  thf('136', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('137', plain,
% 3.99/4.20      (((k1_relat_1 @ 
% 3.99/4.20         (k7_relat_1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))
% 3.99/4.20         = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.99/4.20      inference('demod', [status(thm)], ['135', '136'])).
% 3.99/4.20  thf('138', plain,
% 3.99/4.20      ((((k1_relat_1 @ (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 3.99/4.20          = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 3.99/4.20        | ~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ sk_C)
% 3.99/4.20        | ~ (v2_funct_1 @ sk_C))),
% 3.99/4.20      inference('sup+', [status(thm)], ['21', '137'])).
% 3.99/4.20  thf('139', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.99/4.20      inference('sup+', [status(thm)], ['31', '32'])).
% 3.99/4.20  thf('140', plain,
% 3.99/4.20      (![X64 : $i]:
% 3.99/4.20         ((m1_subset_1 @ X64 @ 
% 3.99/4.20           (k1_zfmisc_1 @ 
% 3.99/4.20            (k2_zfmisc_1 @ (k1_relat_1 @ X64) @ (k2_relat_1 @ X64))))
% 3.99/4.20          | ~ (v1_funct_1 @ X64)
% 3.99/4.20          | ~ (v1_relat_1 @ X64))),
% 3.99/4.20      inference('cnf', [status(esa)], [t3_funct_2])).
% 3.99/4.20  thf('141', plain,
% 3.99/4.20      (((m1_subset_1 @ sk_C @ 
% 3.99/4.20         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))
% 3.99/4.20        | ~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ sk_C))),
% 3.99/4.20      inference('sup+', [status(thm)], ['139', '140'])).
% 3.99/4.20  thf('142', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('143', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('144', plain,
% 3.99/4.20      ((m1_subset_1 @ sk_C @ 
% 3.99/4.20        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 3.99/4.20      inference('demod', [status(thm)], ['141', '142', '143'])).
% 3.99/4.20  thf('145', plain,
% 3.99/4.20      (![X36 : $i, X37 : $i, X38 : $i]:
% 3.99/4.20         ((v4_relat_1 @ X36 @ X37)
% 3.99/4.20          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 3.99/4.20      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.99/4.20  thf('146', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 3.99/4.20      inference('sup-', [status(thm)], ['144', '145'])).
% 3.99/4.20  thf('147', plain,
% 3.99/4.20      (![X15 : $i, X16 : $i]:
% 3.99/4.20         (((X15) = (k7_relat_1 @ X15 @ X16))
% 3.99/4.20          | ~ (v4_relat_1 @ X15 @ X16)
% 3.99/4.20          | ~ (v1_relat_1 @ X15))),
% 3.99/4.20      inference('cnf', [status(esa)], [t209_relat_1])).
% 3.99/4.20  thf('148', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))))),
% 3.99/4.20      inference('sup-', [status(thm)], ['146', '147'])).
% 3.99/4.20  thf('149', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('150', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 3.99/4.20      inference('demod', [status(thm)], ['148', '149'])).
% 3.99/4.20  thf('151', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('152', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('153', plain, ((v2_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('154', plain,
% 3.99/4.20      (((k1_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.99/4.20      inference('demod', [status(thm)], ['138', '150', '151', '152', '153'])).
% 3.99/4.20  thf('155', plain,
% 3.99/4.20      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 3.99/4.20        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.99/4.20      inference('sup+', [status(thm)], ['20', '154'])).
% 3.99/4.20  thf('156', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 3.99/4.20      inference('demod', [status(thm)], ['106', '107'])).
% 3.99/4.20  thf('157', plain,
% 3.99/4.20      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 3.99/4.20        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.99/4.20      inference('demod', [status(thm)], ['155', '156'])).
% 3.99/4.20  thf('158', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ sk_C)
% 3.99/4.20        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 3.99/4.20      inference('sup-', [status(thm)], ['19', '157'])).
% 3.99/4.20  thf('159', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('160', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('161', plain,
% 3.99/4.20      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 3.99/4.20      inference('demod', [status(thm)], ['158', '159', '160'])).
% 3.99/4.20  thf('162', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ sk_C)
% 3.99/4.20        | ~ (v2_funct_1 @ sk_C)
% 3.99/4.20        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 3.99/4.20      inference('sup-', [status(thm)], ['18', '161'])).
% 3.99/4.20  thf('163', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('164', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('165', plain, ((v2_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('166', plain,
% 3.99/4.20      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.99/4.20      inference('demod', [status(thm)], ['162', '163', '164', '165'])).
% 3.99/4.20  thf(t80_relat_1, axiom,
% 3.99/4.20    (![A:$i]:
% 3.99/4.20     ( ( v1_relat_1 @ A ) =>
% 3.99/4.20       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 3.99/4.20  thf('167', plain,
% 3.99/4.20      (![X23 : $i]:
% 3.99/4.20         (((k5_relat_1 @ X23 @ (k6_relat_1 @ (k2_relat_1 @ X23))) = (X23))
% 3.99/4.20          | ~ (v1_relat_1 @ X23))),
% 3.99/4.20      inference('cnf', [status(esa)], [t80_relat_1])).
% 3.99/4.20  thf('168', plain, (![X59 : $i]: ((k6_partfun1 @ X59) = (k6_relat_1 @ X59))),
% 3.99/4.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.99/4.20  thf('169', plain,
% 3.99/4.20      (![X23 : $i]:
% 3.99/4.20         (((k5_relat_1 @ X23 @ (k6_partfun1 @ (k2_relat_1 @ X23))) = (X23))
% 3.99/4.20          | ~ (v1_relat_1 @ X23))),
% 3.99/4.20      inference('demod', [status(thm)], ['167', '168'])).
% 3.99/4.20  thf('170', plain,
% 3.99/4.20      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 3.99/4.20          (k6_partfun1 @ (k1_relat_1 @ sk_C))) = (k2_funct_1 @ sk_C))
% 3.99/4.20        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.99/4.20      inference('sup+', [status(thm)], ['166', '169'])).
% 3.99/4.20  thf('171', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 3.99/4.20      inference('demod', [status(thm)], ['106', '107'])).
% 3.99/4.20  thf('172', plain,
% 3.99/4.20      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ (k1_relat_1 @ sk_C)))
% 3.99/4.20         = (k2_funct_1 @ sk_C))),
% 3.99/4.20      inference('demod', [status(thm)], ['170', '171'])).
% 3.99/4.20  thf('173', plain,
% 3.99/4.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('174', plain,
% 3.99/4.20      (![X36 : $i, X37 : $i, X38 : $i]:
% 3.99/4.20         ((v4_relat_1 @ X36 @ X37)
% 3.99/4.20          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 3.99/4.20      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.99/4.20  thf('175', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 3.99/4.20      inference('sup-', [status(thm)], ['173', '174'])).
% 3.99/4.20  thf('176', plain,
% 3.99/4.20      (![X5 : $i, X6 : $i]:
% 3.99/4.20         (~ (v4_relat_1 @ X5 @ X6)
% 3.99/4.20          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 3.99/4.20          | ~ (v1_relat_1 @ X5))),
% 3.99/4.20      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.99/4.20  thf('177', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 3.99/4.20      inference('sup-', [status(thm)], ['175', '176'])).
% 3.99/4.20  thf('178', plain,
% 3.99/4.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('179', plain,
% 3.99/4.20      (![X3 : $i, X4 : $i]:
% 3.99/4.20         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 3.99/4.20          | (v1_relat_1 @ X3)
% 3.99/4.20          | ~ (v1_relat_1 @ X4))),
% 3.99/4.20      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.99/4.20  thf('180', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 3.99/4.20      inference('sup-', [status(thm)], ['178', '179'])).
% 3.99/4.20  thf('181', plain,
% 3.99/4.20      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 3.99/4.20      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.99/4.20  thf('182', plain, ((v1_relat_1 @ sk_D)),
% 3.99/4.20      inference('demod', [status(thm)], ['180', '181'])).
% 3.99/4.20  thf('183', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 3.99/4.20      inference('demod', [status(thm)], ['177', '182'])).
% 3.99/4.20  thf('184', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.99/4.20      inference('sup+', [status(thm)], ['31', '32'])).
% 3.99/4.20  thf(t147_funct_1, axiom,
% 3.99/4.20    (![A:$i,B:$i]:
% 3.99/4.20     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.99/4.20       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 3.99/4.20         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 3.99/4.20  thf('185', plain,
% 3.99/4.20      (![X29 : $i, X30 : $i]:
% 3.99/4.20         (~ (r1_tarski @ X29 @ (k2_relat_1 @ X30))
% 3.99/4.20          | ((k9_relat_1 @ X30 @ (k10_relat_1 @ X30 @ X29)) = (X29))
% 3.99/4.20          | ~ (v1_funct_1 @ X30)
% 3.99/4.20          | ~ (v1_relat_1 @ X30))),
% 3.99/4.20      inference('cnf', [status(esa)], [t147_funct_1])).
% 3.99/4.20  thf('186', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (~ (r1_tarski @ X0 @ sk_B)
% 3.99/4.20          | ~ (v1_relat_1 @ sk_C)
% 3.99/4.20          | ~ (v1_funct_1 @ sk_C)
% 3.99/4.20          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['184', '185'])).
% 3.99/4.20  thf('187', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('188', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('189', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (~ (r1_tarski @ X0 @ sk_B)
% 3.99/4.20          | ((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ X0)) = (X0)))),
% 3.99/4.20      inference('demod', [status(thm)], ['186', '187', '188'])).
% 3.99/4.20  thf('190', plain,
% 3.99/4.20      (((k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 3.99/4.20         = (k1_relat_1 @ sk_D))),
% 3.99/4.20      inference('sup-', [status(thm)], ['183', '189'])).
% 3.99/4.20  thf(t182_relat_1, axiom,
% 3.99/4.20    (![A:$i]:
% 3.99/4.20     ( ( v1_relat_1 @ A ) =>
% 3.99/4.20       ( ![B:$i]:
% 3.99/4.20         ( ( v1_relat_1 @ B ) =>
% 3.99/4.20           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 3.99/4.20             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 3.99/4.20  thf('191', plain,
% 3.99/4.20      (![X13 : $i, X14 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X13)
% 3.99/4.20          | ((k1_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 3.99/4.20              = (k10_relat_1 @ X14 @ (k1_relat_1 @ X13)))
% 3.99/4.20          | ~ (v1_relat_1 @ X14))),
% 3.99/4.20      inference('cnf', [status(esa)], [t182_relat_1])).
% 3.99/4.20  thf('192', plain,
% 3.99/4.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('193', plain,
% 3.99/4.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf(dt_k1_partfun1, axiom,
% 3.99/4.20    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.99/4.20     ( ( ( v1_funct_1 @ E ) & 
% 3.99/4.20         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.99/4.20         ( v1_funct_1 @ F ) & 
% 3.99/4.20         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.99/4.20       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.99/4.20         ( m1_subset_1 @
% 3.99/4.20           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.99/4.20           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.99/4.20  thf('194', plain,
% 3.99/4.20      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i]:
% 3.99/4.20         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 3.99/4.20          | ~ (v1_funct_1 @ X47)
% 3.99/4.20          | ~ (v1_funct_1 @ X50)
% 3.99/4.20          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52)))
% 3.99/4.20          | (m1_subset_1 @ (k1_partfun1 @ X48 @ X49 @ X51 @ X52 @ X47 @ X50) @ 
% 3.99/4.20             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X52))))),
% 3.99/4.20      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.99/4.20  thf('195', plain,
% 3.99/4.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.99/4.20         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.99/4.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.99/4.20          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.99/4.20          | ~ (v1_funct_1 @ X1)
% 3.99/4.20          | ~ (v1_funct_1 @ sk_C))),
% 3.99/4.20      inference('sup-', [status(thm)], ['193', '194'])).
% 3.99/4.20  thf('196', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('197', plain,
% 3.99/4.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.99/4.20         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.99/4.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.99/4.20          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.99/4.20          | ~ (v1_funct_1 @ X1))),
% 3.99/4.20      inference('demod', [status(thm)], ['195', '196'])).
% 3.99/4.20  thf('198', plain,
% 3.99/4.20      ((~ (v1_funct_1 @ sk_D)
% 3.99/4.20        | (m1_subset_1 @ 
% 3.99/4.20           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.99/4.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.99/4.20      inference('sup-', [status(thm)], ['192', '197'])).
% 3.99/4.20  thf('199', plain, ((v1_funct_1 @ sk_D)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('200', plain,
% 3.99/4.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('201', plain,
% 3.99/4.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf(redefinition_k1_partfun1, axiom,
% 3.99/4.20    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.99/4.20     ( ( ( v1_funct_1 @ E ) & 
% 3.99/4.20         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.99/4.20         ( v1_funct_1 @ F ) & 
% 3.99/4.20         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.99/4.20       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.99/4.20  thf('202', plain,
% 3.99/4.20      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i]:
% 3.99/4.20         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55)))
% 3.99/4.20          | ~ (v1_funct_1 @ X53)
% 3.99/4.20          | ~ (v1_funct_1 @ X56)
% 3.99/4.20          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58)))
% 3.99/4.20          | ((k1_partfun1 @ X54 @ X55 @ X57 @ X58 @ X53 @ X56)
% 3.99/4.20              = (k5_relat_1 @ X53 @ X56)))),
% 3.99/4.20      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.99/4.20  thf('203', plain,
% 3.99/4.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.99/4.20         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.99/4.20            = (k5_relat_1 @ sk_C @ X0))
% 3.99/4.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ sk_C))),
% 3.99/4.20      inference('sup-', [status(thm)], ['201', '202'])).
% 3.99/4.20  thf('204', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('205', plain,
% 3.99/4.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.99/4.20         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.99/4.20            = (k5_relat_1 @ sk_C @ X0))
% 3.99/4.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.99/4.20          | ~ (v1_funct_1 @ X0))),
% 3.99/4.20      inference('demod', [status(thm)], ['203', '204'])).
% 3.99/4.20  thf('206', plain,
% 3.99/4.20      ((~ (v1_funct_1 @ sk_D)
% 3.99/4.20        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.99/4.20            = (k5_relat_1 @ sk_C @ sk_D)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['200', '205'])).
% 3.99/4.20  thf('207', plain, ((v1_funct_1 @ sk_D)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('208', plain,
% 3.99/4.20      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.99/4.20         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.99/4.20      inference('demod', [status(thm)], ['206', '207'])).
% 3.99/4.20  thf('209', plain,
% 3.99/4.20      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 3.99/4.20        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.99/4.20      inference('demod', [status(thm)], ['198', '199', '208'])).
% 3.99/4.20  thf('210', plain,
% 3.99/4.20      (![X36 : $i, X37 : $i, X38 : $i]:
% 3.99/4.20         ((v4_relat_1 @ X36 @ X37)
% 3.99/4.20          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 3.99/4.20      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.99/4.20  thf('211', plain, ((v4_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ sk_A)),
% 3.99/4.20      inference('sup-', [status(thm)], ['209', '210'])).
% 3.99/4.20  thf('212', plain,
% 3.99/4.20      (![X5 : $i, X6 : $i]:
% 3.99/4.20         (~ (v4_relat_1 @ X5 @ X6)
% 3.99/4.20          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 3.99/4.20          | ~ (v1_relat_1 @ X5))),
% 3.99/4.20      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.99/4.20  thf('213', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 3.99/4.20        | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ sk_A))),
% 3.99/4.20      inference('sup-', [status(thm)], ['211', '212'])).
% 3.99/4.20  thf('214', plain,
% 3.99/4.20      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 3.99/4.20        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.99/4.20      inference('demod', [status(thm)], ['198', '199', '208'])).
% 3.99/4.20  thf('215', plain,
% 3.99/4.20      (![X3 : $i, X4 : $i]:
% 3.99/4.20         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 3.99/4.20          | (v1_relat_1 @ X3)
% 3.99/4.20          | ~ (v1_relat_1 @ X4))),
% 3.99/4.20      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.99/4.20  thf('216', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 3.99/4.20        | (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['214', '215'])).
% 3.99/4.20  thf('217', plain,
% 3.99/4.20      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 3.99/4.20      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.99/4.20  thf('218', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 3.99/4.20      inference('demod', [status(thm)], ['216', '217'])).
% 3.99/4.20  thf('219', plain,
% 3.99/4.20      ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ sk_A)),
% 3.99/4.20      inference('demod', [status(thm)], ['213', '218'])).
% 3.99/4.20  thf('220', plain,
% 3.99/4.20      (((r1_tarski @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)) @ sk_A)
% 3.99/4.20        | ~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_relat_1 @ sk_D))),
% 3.99/4.20      inference('sup+', [status(thm)], ['191', '219'])).
% 3.99/4.20  thf('221', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('222', plain, ((v1_relat_1 @ sk_D)),
% 3.99/4.20      inference('demod', [status(thm)], ['180', '181'])).
% 3.99/4.20  thf('223', plain,
% 3.99/4.20      ((r1_tarski @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)) @ sk_A)),
% 3.99/4.20      inference('demod', [status(thm)], ['220', '221', '222'])).
% 3.99/4.20  thf('224', plain,
% 3.99/4.20      (![X0 : $i, X1 : $i]:
% 3.99/4.20         (~ (r1_tarski @ X0 @ X1) | (v4_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 3.99/4.20      inference('demod', [status(thm)], ['72', '73'])).
% 3.99/4.20  thf('225', plain,
% 3.99/4.20      ((v4_relat_1 @ 
% 3.99/4.20        (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A)),
% 3.99/4.20      inference('sup-', [status(thm)], ['223', '224'])).
% 3.99/4.20  thf('226', plain,
% 3.99/4.20      (![X15 : $i, X16 : $i]:
% 3.99/4.20         (((X15) = (k7_relat_1 @ X15 @ X16))
% 3.99/4.20          | ~ (v4_relat_1 @ X15 @ X16)
% 3.99/4.20          | ~ (v1_relat_1 @ X15))),
% 3.99/4.20      inference('cnf', [status(esa)], [t209_relat_1])).
% 3.99/4.20  thf('227', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ 
% 3.99/4.20           (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))))
% 3.99/4.20        | ((k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 3.99/4.20            = (k7_relat_1 @ 
% 3.99/4.20               (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ 
% 3.99/4.20               sk_A)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['225', '226'])).
% 3.99/4.20  thf('228', plain, (![X27 : $i]: (v1_relat_1 @ (k6_partfun1 @ X27))),
% 3.99/4.20      inference('demod', [status(thm)], ['43', '44'])).
% 3.99/4.20  thf('229', plain,
% 3.99/4.20      (((k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))
% 3.99/4.20         = (k7_relat_1 @ 
% 3.99/4.20            (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A))),
% 3.99/4.20      inference('demod', [status(thm)], ['227', '228'])).
% 3.99/4.20  thf(t148_relat_1, axiom,
% 3.99/4.20    (![A:$i,B:$i]:
% 3.99/4.20     ( ( v1_relat_1 @ B ) =>
% 3.99/4.20       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 3.99/4.20  thf('230', plain,
% 3.99/4.20      (![X11 : $i, X12 : $i]:
% 3.99/4.20         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 3.99/4.20          | ~ (v1_relat_1 @ X11))),
% 3.99/4.20      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.99/4.20  thf('231', plain,
% 3.99/4.20      ((((k2_relat_1 @ 
% 3.99/4.20          (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))))
% 3.99/4.20          = (k9_relat_1 @ 
% 3.99/4.20             (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A))
% 3.99/4.20        | ~ (v1_relat_1 @ 
% 3.99/4.20             (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)))))),
% 3.99/4.20      inference('sup+', [status(thm)], ['229', '230'])).
% 3.99/4.20  thf('232', plain, (![X21 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X21)) = (X21))),
% 3.99/4.20      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.99/4.20  thf('233', plain, (![X59 : $i]: ((k6_partfun1 @ X59) = (k6_relat_1 @ X59))),
% 3.99/4.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.99/4.20  thf('234', plain,
% 3.99/4.20      (![X21 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X21)) = (X21))),
% 3.99/4.20      inference('demod', [status(thm)], ['232', '233'])).
% 3.99/4.20  thf('235', plain,
% 3.99/4.20      (![X13 : $i, X14 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X13)
% 3.99/4.20          | ((k1_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 3.99/4.20              = (k10_relat_1 @ X14 @ (k1_relat_1 @ X13)))
% 3.99/4.20          | ~ (v1_relat_1 @ X14))),
% 3.99/4.20      inference('cnf', [status(esa)], [t182_relat_1])).
% 3.99/4.20  thf('236', plain,
% 3.99/4.20      ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ sk_A)),
% 3.99/4.20      inference('demod', [status(thm)], ['213', '218'])).
% 3.99/4.20  thf('237', plain,
% 3.99/4.20      (![X0 : $i, X1 : $i]:
% 3.99/4.20         (~ (r1_tarski @ X0 @ X1) | (v4_relat_1 @ (k6_partfun1 @ X0) @ X1))),
% 3.99/4.20      inference('demod', [status(thm)], ['72', '73'])).
% 3.99/4.20  thf('238', plain,
% 3.99/4.20      ((v4_relat_1 @ 
% 3.99/4.20        (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A)),
% 3.99/4.20      inference('sup-', [status(thm)], ['236', '237'])).
% 3.99/4.20  thf('239', plain,
% 3.99/4.20      (![X15 : $i, X16 : $i]:
% 3.99/4.20         (((X15) = (k7_relat_1 @ X15 @ X16))
% 3.99/4.20          | ~ (v4_relat_1 @ X15 @ X16)
% 3.99/4.20          | ~ (v1_relat_1 @ X15))),
% 3.99/4.20      inference('cnf', [status(esa)], [t209_relat_1])).
% 3.99/4.20  thf('240', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ 
% 3.99/4.20           (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))
% 3.99/4.20        | ((k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 3.99/4.20            = (k7_relat_1 @ 
% 3.99/4.20               (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['238', '239'])).
% 3.99/4.20  thf('241', plain, (![X27 : $i]: (v1_relat_1 @ (k6_partfun1 @ X27))),
% 3.99/4.20      inference('demod', [status(thm)], ['43', '44'])).
% 3.99/4.20  thf('242', plain,
% 3.99/4.20      (((k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 3.99/4.20         = (k7_relat_1 @ 
% 3.99/4.20            (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A))),
% 3.99/4.20      inference('demod', [status(thm)], ['240', '241'])).
% 3.99/4.20  thf('243', plain,
% 3.99/4.20      (![X11 : $i, X12 : $i]:
% 3.99/4.20         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 3.99/4.20          | ~ (v1_relat_1 @ X11))),
% 3.99/4.20      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.99/4.20  thf('244', plain,
% 3.99/4.20      ((((k2_relat_1 @ 
% 3.99/4.20          (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))
% 3.99/4.20          = (k9_relat_1 @ 
% 3.99/4.20             (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A))
% 3.99/4.20        | ~ (v1_relat_1 @ 
% 3.99/4.20             (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))))),
% 3.99/4.20      inference('sup+', [status(thm)], ['242', '243'])).
% 3.99/4.20  thf('245', plain,
% 3.99/4.20      (![X21 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X21)) = (X21))),
% 3.99/4.20      inference('demod', [status(thm)], ['232', '233'])).
% 3.99/4.20  thf('246', plain, (![X27 : $i]: (v1_relat_1 @ (k6_partfun1 @ X27))),
% 3.99/4.20      inference('demod', [status(thm)], ['43', '44'])).
% 3.99/4.20  thf('247', plain,
% 3.99/4.20      (((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 3.99/4.20         = (k9_relat_1 @ 
% 3.99/4.20            (k6_partfun1 @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))) @ sk_A))),
% 3.99/4.20      inference('demod', [status(thm)], ['244', '245', '246'])).
% 3.99/4.20  thf('248', plain,
% 3.99/4.20      ((((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 3.99/4.20          = (k9_relat_1 @ 
% 3.99/4.20             (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A))
% 3.99/4.20        | ~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_relat_1 @ sk_D))),
% 3.99/4.20      inference('sup+', [status(thm)], ['235', '247'])).
% 3.99/4.20  thf('249', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('250', plain, ((v1_relat_1 @ sk_D)),
% 3.99/4.20      inference('demod', [status(thm)], ['180', '181'])).
% 3.99/4.20  thf('251', plain,
% 3.99/4.20      (((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 3.99/4.20         = (k9_relat_1 @ 
% 3.99/4.20            (k6_partfun1 @ (k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))) @ sk_A))),
% 3.99/4.20      inference('demod', [status(thm)], ['248', '249', '250'])).
% 3.99/4.20  thf('252', plain, (![X27 : $i]: (v1_relat_1 @ (k6_partfun1 @ X27))),
% 3.99/4.20      inference('demod', [status(thm)], ['43', '44'])).
% 3.99/4.20  thf('253', plain,
% 3.99/4.20      (((k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D))
% 3.99/4.20         = (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))),
% 3.99/4.20      inference('demod', [status(thm)], ['231', '234', '251', '252'])).
% 3.99/4.20  thf('254', plain,
% 3.99/4.20      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.99/4.20        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.99/4.20        (k6_partfun1 @ sk_A))),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('255', plain,
% 3.99/4.20      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.99/4.20         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.99/4.20      inference('demod', [status(thm)], ['206', '207'])).
% 3.99/4.20  thf('256', plain,
% 3.99/4.20      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 3.99/4.20        (k6_partfun1 @ sk_A))),
% 3.99/4.20      inference('demod', [status(thm)], ['254', '255'])).
% 3.99/4.20  thf('257', plain,
% 3.99/4.20      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 3.99/4.20        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.99/4.20      inference('demod', [status(thm)], ['198', '199', '208'])).
% 3.99/4.20  thf(redefinition_r2_relset_1, axiom,
% 3.99/4.20    (![A:$i,B:$i,C:$i,D:$i]:
% 3.99/4.20     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.99/4.20         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.99/4.20       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.99/4.20  thf('258', plain,
% 3.99/4.20      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 3.99/4.20         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 3.99/4.20          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 3.99/4.20          | ((X42) = (X45))
% 3.99/4.20          | ~ (r2_relset_1 @ X43 @ X44 @ X42 @ X45))),
% 3.99/4.20      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.99/4.20  thf('259', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 3.99/4.20          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 3.99/4.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.99/4.20      inference('sup-', [status(thm)], ['257', '258'])).
% 3.99/4.20  thf('260', plain,
% 3.99/4.20      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 3.99/4.20           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.99/4.20        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['256', '259'])).
% 3.99/4.20  thf('261', plain,
% 3.99/4.20      (![X46 : $i]:
% 3.99/4.20         (m1_subset_1 @ (k6_partfun1 @ X46) @ 
% 3.99/4.20          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X46)))),
% 3.99/4.20      inference('demod', [status(thm)], ['36', '37'])).
% 3.99/4.20  thf('262', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 3.99/4.20      inference('demod', [status(thm)], ['260', '261'])).
% 3.99/4.20  thf('263', plain,
% 3.99/4.20      (![X20 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X20)) = (X20))),
% 3.99/4.20      inference('demod', [status(thm)], ['46', '47'])).
% 3.99/4.20  thf('264', plain, (((k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)) = (sk_A))),
% 3.99/4.20      inference('demod', [status(thm)], ['253', '262', '263'])).
% 3.99/4.20  thf('265', plain, (((k9_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_D))),
% 3.99/4.20      inference('demod', [status(thm)], ['190', '264'])).
% 3.99/4.20  thf('266', plain,
% 3.99/4.20      (![X11 : $i, X12 : $i]:
% 3.99/4.20         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 3.99/4.20          | ~ (v1_relat_1 @ X11))),
% 3.99/4.20      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.99/4.20  thf('267', plain,
% 3.99/4.20      (![X23 : $i]:
% 3.99/4.20         (((k5_relat_1 @ X23 @ (k6_partfun1 @ (k2_relat_1 @ X23))) = (X23))
% 3.99/4.20          | ~ (v1_relat_1 @ X23))),
% 3.99/4.20      inference('demod', [status(thm)], ['167', '168'])).
% 3.99/4.20  thf('268', plain,
% 3.99/4.20      (![X13 : $i, X14 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X13)
% 3.99/4.20          | ((k1_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 3.99/4.20              = (k10_relat_1 @ X14 @ (k1_relat_1 @ X13)))
% 3.99/4.20          | ~ (v1_relat_1 @ X14))),
% 3.99/4.20      inference('cnf', [status(esa)], [t182_relat_1])).
% 3.99/4.20  thf('269', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (((k1_relat_1 @ X0)
% 3.99/4.20            = (k10_relat_1 @ X0 @ 
% 3.99/4.20               (k1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)))))
% 3.99/4.20          | ~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 3.99/4.20      inference('sup+', [status(thm)], ['267', '268'])).
% 3.99/4.20  thf('270', plain,
% 3.99/4.20      (![X20 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X20)) = (X20))),
% 3.99/4.20      inference('demod', [status(thm)], ['46', '47'])).
% 3.99/4.20  thf('271', plain, (![X27 : $i]: (v1_relat_1 @ (k6_partfun1 @ X27))),
% 3.99/4.20      inference('demod', [status(thm)], ['43', '44'])).
% 3.99/4.20  thf('272', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0)))
% 3.99/4.20          | ~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0))),
% 3.99/4.20      inference('demod', [status(thm)], ['269', '270', '271'])).
% 3.99/4.20  thf('273', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X0)
% 3.99/4.20          | ((k1_relat_1 @ X0) = (k10_relat_1 @ X0 @ (k2_relat_1 @ X0))))),
% 3.99/4.20      inference('simplify', [status(thm)], ['272'])).
% 3.99/4.20  thf('274', plain,
% 3.99/4.20      (![X0 : $i, X1 : $i]:
% 3.99/4.20         (((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 3.99/4.20            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0)))
% 3.99/4.20          | ~ (v1_relat_1 @ X1)
% 3.99/4.20          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 3.99/4.20      inference('sup+', [status(thm)], ['266', '273'])).
% 3.99/4.20  thf(dt_k7_relat_1, axiom,
% 3.99/4.20    (![A:$i,B:$i]:
% 3.99/4.20     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 3.99/4.20  thf('275', plain,
% 3.99/4.20      (![X7 : $i, X8 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 3.99/4.20      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 3.99/4.20  thf('276', plain,
% 3.99/4.20      (![X0 : $i, X1 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X1)
% 3.99/4.20          | ((k1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 3.99/4.20              = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))))),
% 3.99/4.20      inference('clc', [status(thm)], ['274', '275'])).
% 3.99/4.20  thf('277', plain,
% 3.99/4.20      ((((k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_A))
% 3.99/4.20          = (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ (k1_relat_1 @ sk_D)))
% 3.99/4.20        | ~ (v1_relat_1 @ sk_C))),
% 3.99/4.20      inference('sup+', [status(thm)], ['265', '276'])).
% 3.99/4.20  thf('278', plain,
% 3.99/4.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('279', plain,
% 3.99/4.20      (![X36 : $i, X37 : $i, X38 : $i]:
% 3.99/4.20         ((v4_relat_1 @ X36 @ X37)
% 3.99/4.20          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 3.99/4.20      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.99/4.20  thf('280', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 3.99/4.20      inference('sup-', [status(thm)], ['278', '279'])).
% 3.99/4.20  thf('281', plain,
% 3.99/4.20      (![X15 : $i, X16 : $i]:
% 3.99/4.20         (((X15) = (k7_relat_1 @ X15 @ X16))
% 3.99/4.20          | ~ (v4_relat_1 @ X15 @ X16)
% 3.99/4.20          | ~ (v1_relat_1 @ X15))),
% 3.99/4.20      inference('cnf', [status(esa)], [t209_relat_1])).
% 3.99/4.20  thf('282', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['280', '281'])).
% 3.99/4.20  thf('283', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('284', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 3.99/4.20      inference('demod', [status(thm)], ['282', '283'])).
% 3.99/4.20  thf('285', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 3.99/4.20      inference('demod', [status(thm)], ['282', '283'])).
% 3.99/4.20  thf('286', plain, (((k10_relat_1 @ sk_C @ (k1_relat_1 @ sk_D)) = (sk_A))),
% 3.99/4.20      inference('demod', [status(thm)], ['253', '262', '263'])).
% 3.99/4.20  thf('287', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('288', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 3.99/4.20      inference('demod', [status(thm)], ['277', '284', '285', '286', '287'])).
% 3.99/4.20  thf('289', plain,
% 3.99/4.20      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 3.99/4.20         = (k2_funct_1 @ sk_C))),
% 3.99/4.20      inference('demod', [status(thm)], ['172', '288'])).
% 3.99/4.20  thf('290', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 3.99/4.20      inference('demod', [status(thm)], ['260', '261'])).
% 3.99/4.20  thf('291', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0))),
% 3.99/4.20      inference('simplify', [status(thm)], ['17'])).
% 3.99/4.20  thf('292', plain,
% 3.99/4.20      (![X26 : $i]:
% 3.99/4.20         ((v1_funct_1 @ (k2_funct_1 @ X26))
% 3.99/4.20          | ~ (v1_funct_1 @ X26)
% 3.99/4.20          | ~ (v1_relat_1 @ X26))),
% 3.99/4.20      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.99/4.20  thf('293', plain,
% 3.99/4.20      (![X35 : $i]:
% 3.99/4.20         (~ (v2_funct_1 @ X35)
% 3.99/4.20          | ((k2_funct_1 @ (k2_funct_1 @ X35)) = (X35))
% 3.99/4.20          | ~ (v1_funct_1 @ X35)
% 3.99/4.20          | ~ (v1_relat_1 @ X35))),
% 3.99/4.20      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.99/4.20  thf('294', plain,
% 3.99/4.20      (![X35 : $i]:
% 3.99/4.20         (~ (v2_funct_1 @ X35)
% 3.99/4.20          | ((k2_funct_1 @ (k2_funct_1 @ X35)) = (X35))
% 3.99/4.20          | ~ (v1_funct_1 @ X35)
% 3.99/4.20          | ~ (v1_relat_1 @ X35))),
% 3.99/4.20      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.99/4.20  thf('295', plain,
% 3.99/4.20      (![X35 : $i]:
% 3.99/4.20         (~ (v2_funct_1 @ X35)
% 3.99/4.20          | ((k2_funct_1 @ (k2_funct_1 @ X35)) = (X35))
% 3.99/4.20          | ~ (v1_funct_1 @ X35)
% 3.99/4.20          | ~ (v1_relat_1 @ X35))),
% 3.99/4.20      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.99/4.20  thf('296', plain,
% 3.99/4.20      (((k1_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.99/4.20      inference('demod', [status(thm)], ['138', '150', '151', '152', '153'])).
% 3.99/4.20  thf('297', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['49', '50'])).
% 3.99/4.20  thf('298', plain,
% 3.99/4.20      (![X15 : $i, X16 : $i]:
% 3.99/4.20         (((X15) = (k7_relat_1 @ X15 @ X16))
% 3.99/4.20          | ~ (v4_relat_1 @ X15 @ X16)
% 3.99/4.20          | ~ (v1_relat_1 @ X15))),
% 3.99/4.20      inference('cnf', [status(esa)], [t209_relat_1])).
% 3.99/4.20  thf('299', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0)
% 3.99/4.20          | ((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 3.99/4.20      inference('sup-', [status(thm)], ['297', '298'])).
% 3.99/4.20  thf('300', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))) | ~ (v1_relat_1 @ X0))),
% 3.99/4.20      inference('simplify', [status(thm)], ['299'])).
% 3.99/4.20  thf('301', plain,
% 3.99/4.20      (![X11 : $i, X12 : $i]:
% 3.99/4.20         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 3.99/4.20          | ~ (v1_relat_1 @ X11))),
% 3.99/4.20      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.99/4.20  thf('302', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 3.99/4.20          | ~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0))),
% 3.99/4.20      inference('sup+', [status(thm)], ['300', '301'])).
% 3.99/4.20  thf('303', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X0)
% 3.99/4.20          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 3.99/4.20      inference('simplify', [status(thm)], ['302'])).
% 3.99/4.20  thf('304', plain,
% 3.99/4.20      ((((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.99/4.20          = (k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.99/4.20             (k1_relat_1 @ sk_C)))
% 3.99/4.20        | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.99/4.20      inference('sup+', [status(thm)], ['296', '303'])).
% 3.99/4.20  thf('305', plain,
% 3.99/4.20      (![X35 : $i]:
% 3.99/4.20         (~ (v2_funct_1 @ X35)
% 3.99/4.20          | ((k2_funct_1 @ (k2_funct_1 @ X35)) = (X35))
% 3.99/4.20          | ~ (v1_funct_1 @ X35)
% 3.99/4.20          | ~ (v1_relat_1 @ X35))),
% 3.99/4.20      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.99/4.20  thf('306', plain,
% 3.99/4.20      (![X35 : $i]:
% 3.99/4.20         (~ (v2_funct_1 @ X35)
% 3.99/4.20          | ((k2_funct_1 @ (k2_funct_1 @ X35)) = (X35))
% 3.99/4.20          | ~ (v1_funct_1 @ X35)
% 3.99/4.20          | ~ (v1_relat_1 @ X35))),
% 3.99/4.20      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.99/4.20  thf('307', plain,
% 3.99/4.20      (![X35 : $i]:
% 3.99/4.20         (~ (v2_funct_1 @ X35)
% 3.99/4.20          | ((k2_funct_1 @ (k2_funct_1 @ X35)) = (X35))
% 3.99/4.20          | ~ (v1_funct_1 @ X35)
% 3.99/4.20          | ~ (v1_relat_1 @ X35))),
% 3.99/4.20      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.99/4.20  thf('308', plain,
% 3.99/4.20      (![X26 : $i]:
% 3.99/4.20         ((v1_funct_1 @ (k2_funct_1 @ X26))
% 3.99/4.20          | ~ (v1_funct_1 @ X26)
% 3.99/4.20          | ~ (v1_relat_1 @ X26))),
% 3.99/4.20      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.99/4.20  thf('309', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0))),
% 3.99/4.20      inference('simplify', [status(thm)], ['17'])).
% 3.99/4.20  thf('310', plain,
% 3.99/4.20      (![X26 : $i]:
% 3.99/4.20         ((v1_relat_1 @ (k2_funct_1 @ X26))
% 3.99/4.20          | ~ (v1_funct_1 @ X26)
% 3.99/4.20          | ~ (v1_relat_1 @ X26))),
% 3.99/4.20      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.99/4.20  thf('311', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.99/4.20      inference('demod', [status(thm)], ['92', '93'])).
% 3.99/4.20  thf('312', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0))),
% 3.99/4.20      inference('simplify', [status(thm)], ['17'])).
% 3.99/4.20  thf('313', plain,
% 3.99/4.20      (![X26 : $i]:
% 3.99/4.20         ((v1_funct_1 @ (k2_funct_1 @ X26))
% 3.99/4.20          | ~ (v1_funct_1 @ X26)
% 3.99/4.20          | ~ (v1_relat_1 @ X26))),
% 3.99/4.20      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.99/4.20  thf('314', plain,
% 3.99/4.20      (![X26 : $i]:
% 3.99/4.20         ((v1_relat_1 @ (k2_funct_1 @ X26))
% 3.99/4.20          | ~ (v1_funct_1 @ X26)
% 3.99/4.20          | ~ (v1_relat_1 @ X26))),
% 3.99/4.20      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 3.99/4.20  thf('315', plain,
% 3.99/4.20      (![X35 : $i]:
% 3.99/4.20         (~ (v2_funct_1 @ X35)
% 3.99/4.20          | ((k2_funct_1 @ (k2_funct_1 @ X35)) = (X35))
% 3.99/4.20          | ~ (v1_funct_1 @ X35)
% 3.99/4.20          | ~ (v1_relat_1 @ X35))),
% 3.99/4.20      inference('cnf', [status(esa)], [t65_funct_1])).
% 3.99/4.20  thf('316', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0))),
% 3.99/4.20      inference('simplify', [status(thm)], ['53'])).
% 3.99/4.20  thf('317', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         ((v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.99/4.20          | ~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 3.99/4.20      inference('sup+', [status(thm)], ['315', '316'])).
% 3.99/4.20  thf('318', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0)
% 3.99/4.20          | (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.99/4.20      inference('sup-', [status(thm)], ['314', '317'])).
% 3.99/4.20  thf('319', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         ((v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0))),
% 3.99/4.20      inference('simplify', [status(thm)], ['318'])).
% 3.99/4.20  thf('320', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.99/4.20      inference('sup-', [status(thm)], ['313', '319'])).
% 3.99/4.20  thf('321', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         ((v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0))),
% 3.99/4.20      inference('simplify', [status(thm)], ['320'])).
% 3.99/4.20  thf('322', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.99/4.20      inference('sup-', [status(thm)], ['312', '321'])).
% 3.99/4.20  thf('323', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         ((v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0))),
% 3.99/4.20      inference('simplify', [status(thm)], ['322'])).
% 3.99/4.20  thf('324', plain,
% 3.99/4.20      (![X5 : $i, X6 : $i]:
% 3.99/4.20         (~ (v4_relat_1 @ X5 @ X6)
% 3.99/4.20          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 3.99/4.20          | ~ (v1_relat_1 @ X5))),
% 3.99/4.20      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.99/4.20  thf('325', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0)
% 3.99/4.20          | (r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 3.99/4.20      inference('sup-', [status(thm)], ['323', '324'])).
% 3.99/4.20  thf('326', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         ((r1_tarski @ (k1_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 3.99/4.20          | ~ (v2_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_funct_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X0))),
% 3.99/4.20      inference('simplify', [status(thm)], ['325'])).
% 3.99/4.20  thf('327', plain,
% 3.99/4.20      (((r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 3.99/4.20        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.99/4.20      inference('sup+', [status(thm)], ['311', '326'])).
% 3.99/4.20  thf('328', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ sk_C)
% 3.99/4.20        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20        | (r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 3.99/4.20      inference('sup-', [status(thm)], ['310', '327'])).
% 3.99/4.20  thf('329', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('330', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('331', plain,
% 3.99/4.20      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20        | (r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 3.99/4.20      inference('demod', [status(thm)], ['328', '329', '330'])).
% 3.99/4.20  thf('332', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ sk_C)
% 3.99/4.20        | ~ (v2_funct_1 @ sk_C)
% 3.99/4.20        | (r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 3.99/4.20        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['309', '331'])).
% 3.99/4.20  thf('333', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('334', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('335', plain, ((v2_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('336', plain,
% 3.99/4.20      (((r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 3.99/4.20        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.99/4.20      inference('demod', [status(thm)], ['332', '333', '334', '335'])).
% 3.99/4.20  thf('337', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ sk_C)
% 3.99/4.20        | (r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 3.99/4.20      inference('sup-', [status(thm)], ['308', '336'])).
% 3.99/4.20  thf('338', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('339', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('340', plain,
% 3.99/4.20      ((r1_tarski @ sk_B @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.99/4.20      inference('demod', [status(thm)], ['337', '338', '339'])).
% 3.99/4.20  thf('341', plain,
% 3.99/4.20      (![X29 : $i, X30 : $i]:
% 3.99/4.20         (~ (r1_tarski @ X29 @ (k2_relat_1 @ X30))
% 3.99/4.20          | ((k9_relat_1 @ X30 @ (k10_relat_1 @ X30 @ X29)) = (X29))
% 3.99/4.20          | ~ (v1_funct_1 @ X30)
% 3.99/4.20          | ~ (v1_relat_1 @ X30))),
% 3.99/4.20      inference('cnf', [status(esa)], [t147_funct_1])).
% 3.99/4.20  thf('342', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.99/4.20        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.99/4.20        | ((k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.99/4.20            (k10_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_B)) = (
% 3.99/4.20            sk_B)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['340', '341'])).
% 3.99/4.20  thf('343', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ sk_C)
% 3.99/4.20        | ~ (v2_funct_1 @ sk_C)
% 3.99/4.20        | ((k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.99/4.20            (k10_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_B)) = (
% 3.99/4.20            sk_B))
% 3.99/4.20        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.99/4.20      inference('sup-', [status(thm)], ['307', '342'])).
% 3.99/4.20  thf('344', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('345', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('346', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('347', plain, ((v2_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('348', plain,
% 3.99/4.20      ((((k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.99/4.20          (k10_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_B)) = (
% 3.99/4.20          sk_B))
% 3.99/4.20        | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.99/4.20      inference('demod', [status(thm)], ['343', '344', '345', '346', '347'])).
% 3.99/4.20  thf('349', plain,
% 3.99/4.20      ((~ (v1_funct_1 @ sk_C)
% 3.99/4.20        | ~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ sk_C)
% 3.99/4.20        | ~ (v2_funct_1 @ sk_C)
% 3.99/4.20        | ((k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.99/4.20            (k10_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_B)) = (
% 3.99/4.20            sk_B)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['306', '348'])).
% 3.99/4.20  thf('350', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('351', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('352', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('353', plain, ((v2_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('354', plain,
% 3.99/4.20      (((k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.99/4.20         (k10_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_B)) = (
% 3.99/4.20         sk_B))),
% 3.99/4.20      inference('demod', [status(thm)], ['349', '350', '351', '352', '353'])).
% 3.99/4.20  thf('355', plain,
% 3.99/4.20      ((((k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.99/4.20          (k10_relat_1 @ sk_C @ sk_B)) = (sk_B))
% 3.99/4.20        | ~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ sk_C)
% 3.99/4.20        | ~ (v2_funct_1 @ sk_C))),
% 3.99/4.20      inference('sup+', [status(thm)], ['305', '354'])).
% 3.99/4.20  thf('356', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.99/4.20      inference('sup+', [status(thm)], ['31', '32'])).
% 3.99/4.20  thf('357', plain,
% 3.99/4.20      (![X23 : $i]:
% 3.99/4.20         (((k5_relat_1 @ X23 @ (k6_partfun1 @ (k2_relat_1 @ X23))) = (X23))
% 3.99/4.20          | ~ (v1_relat_1 @ X23))),
% 3.99/4.20      inference('demod', [status(thm)], ['167', '168'])).
% 3.99/4.20  thf('358', plain,
% 3.99/4.20      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))
% 3.99/4.20        | ~ (v1_relat_1 @ sk_C))),
% 3.99/4.20      inference('sup+', [status(thm)], ['356', '357'])).
% 3.99/4.20  thf('359', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('360', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 3.99/4.20      inference('demod', [status(thm)], ['358', '359'])).
% 3.99/4.20  thf('361', plain,
% 3.99/4.20      (![X13 : $i, X14 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X13)
% 3.99/4.20          | ((k1_relat_1 @ (k5_relat_1 @ X14 @ X13))
% 3.99/4.20              = (k10_relat_1 @ X14 @ (k1_relat_1 @ X13)))
% 3.99/4.20          | ~ (v1_relat_1 @ X14))),
% 3.99/4.20      inference('cnf', [status(esa)], [t182_relat_1])).
% 3.99/4.20  thf('362', plain,
% 3.99/4.20      ((((k1_relat_1 @ sk_C)
% 3.99/4.20          = (k10_relat_1 @ sk_C @ (k1_relat_1 @ (k6_partfun1 @ sk_B))))
% 3.99/4.20        | ~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B)))),
% 3.99/4.20      inference('sup+', [status(thm)], ['360', '361'])).
% 3.99/4.20  thf('363', plain,
% 3.99/4.20      (![X20 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X20)) = (X20))),
% 3.99/4.20      inference('demod', [status(thm)], ['46', '47'])).
% 3.99/4.20  thf('364', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('365', plain, (![X27 : $i]: (v1_relat_1 @ (k6_partfun1 @ X27))),
% 3.99/4.20      inference('demod', [status(thm)], ['43', '44'])).
% 3.99/4.20  thf('366', plain, (((k1_relat_1 @ sk_C) = (k10_relat_1 @ sk_C @ sk_B))),
% 3.99/4.20      inference('demod', [status(thm)], ['362', '363', '364', '365'])).
% 3.99/4.20  thf('367', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('368', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('369', plain, ((v2_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('370', plain,
% 3.99/4.20      (((k9_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k1_relat_1 @ sk_C))
% 3.99/4.20         = (sk_B))),
% 3.99/4.20      inference('demod', [status(thm)], ['355', '366', '367', '368', '369'])).
% 3.99/4.20  thf('371', plain,
% 3.99/4.20      ((((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B))
% 3.99/4.20        | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.99/4.20      inference('demod', [status(thm)], ['304', '370'])).
% 3.99/4.20  thf('372', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ sk_C)
% 3.99/4.20        | ~ (v2_funct_1 @ sk_C)
% 3.99/4.20        | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['295', '371'])).
% 3.99/4.20  thf('373', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('374', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('375', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('376', plain, ((v2_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('377', plain,
% 3.99/4.20      (((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (sk_B))),
% 3.99/4.20      inference('demod', [status(thm)], ['372', '373', '374', '375', '376'])).
% 3.99/4.20  thf('378', plain,
% 3.99/4.20      (![X23 : $i]:
% 3.99/4.20         (((k5_relat_1 @ X23 @ (k6_partfun1 @ (k2_relat_1 @ X23))) = (X23))
% 3.99/4.20          | ~ (v1_relat_1 @ X23))),
% 3.99/4.20      inference('demod', [status(thm)], ['167', '168'])).
% 3.99/4.20  thf('379', plain,
% 3.99/4.20      ((((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.99/4.20          (k6_partfun1 @ sk_B)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.99/4.20        | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.99/4.20      inference('sup+', [status(thm)], ['377', '378'])).
% 3.99/4.20  thf('380', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ sk_C)
% 3.99/4.20        | ~ (v2_funct_1 @ sk_C)
% 3.99/4.20        | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 3.99/4.20            (k6_partfun1 @ sk_B)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 3.99/4.20      inference('sup-', [status(thm)], ['294', '379'])).
% 3.99/4.20  thf('381', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('382', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('383', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('384', plain, ((v2_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('385', plain,
% 3.99/4.20      (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k6_partfun1 @ sk_B))
% 3.99/4.20         = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.99/4.20      inference('demod', [status(thm)], ['380', '381', '382', '383', '384'])).
% 3.99/4.20  thf('386', plain,
% 3.99/4.20      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B))
% 3.99/4.20          = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 3.99/4.20        | ~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ sk_C)
% 3.99/4.20        | ~ (v2_funct_1 @ sk_C))),
% 3.99/4.20      inference('sup+', [status(thm)], ['293', '385'])).
% 3.99/4.20  thf('387', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 3.99/4.20      inference('demod', [status(thm)], ['358', '359'])).
% 3.99/4.20  thf('388', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('389', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('390', plain, ((v2_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('391', plain, (((sk_C) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.99/4.20      inference('demod', [status(thm)], ['386', '387', '388', '389', '390'])).
% 3.99/4.20  thf('392', plain,
% 3.99/4.20      (![X34 : $i]:
% 3.99/4.20         (~ (v2_funct_1 @ X34)
% 3.99/4.20          | ((k5_relat_1 @ X34 @ (k2_funct_1 @ X34))
% 3.99/4.20              = (k6_relat_1 @ (k1_relat_1 @ X34)))
% 3.99/4.20          | ~ (v1_funct_1 @ X34)
% 3.99/4.20          | ~ (v1_relat_1 @ X34))),
% 3.99/4.20      inference('cnf', [status(esa)], [t61_funct_1])).
% 3.99/4.20  thf('393', plain, (![X59 : $i]: ((k6_partfun1 @ X59) = (k6_relat_1 @ X59))),
% 3.99/4.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.99/4.20  thf('394', plain,
% 3.99/4.20      (![X34 : $i]:
% 3.99/4.20         (~ (v2_funct_1 @ X34)
% 3.99/4.20          | ((k5_relat_1 @ X34 @ (k2_funct_1 @ X34))
% 3.99/4.20              = (k6_partfun1 @ (k1_relat_1 @ X34)))
% 3.99/4.20          | ~ (v1_funct_1 @ X34)
% 3.99/4.20          | ~ (v1_relat_1 @ X34))),
% 3.99/4.20      inference('demod', [status(thm)], ['392', '393'])).
% 3.99/4.20  thf('395', plain,
% 3.99/4.20      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 3.99/4.20          = (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 3.99/4.20        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.99/4.20      inference('sup+', [status(thm)], ['391', '394'])).
% 3.99/4.20  thf('396', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 3.99/4.20      inference('demod', [status(thm)], ['92', '93'])).
% 3.99/4.20  thf('397', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 3.99/4.20      inference('demod', [status(thm)], ['106', '107'])).
% 3.99/4.20  thf('398', plain,
% 3.99/4.20      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 3.99/4.20        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 3.99/4.20      inference('demod', [status(thm)], ['395', '396', '397'])).
% 3.99/4.20  thf('399', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ sk_C)
% 3.99/4.20        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['292', '398'])).
% 3.99/4.20  thf('400', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('401', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('402', plain,
% 3.99/4.20      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 3.99/4.20      inference('demod', [status(thm)], ['399', '400', '401'])).
% 3.99/4.20  thf('403', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ sk_C)
% 3.99/4.20        | ~ (v1_funct_1 @ sk_C)
% 3.99/4.20        | ~ (v2_funct_1 @ sk_C)
% 3.99/4.20        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['291', '402'])).
% 3.99/4.20  thf('404', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('405', plain, ((v1_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('406', plain, ((v2_funct_1 @ sk_C)),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('407', plain,
% 3.99/4.20      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 3.99/4.20      inference('demod', [status(thm)], ['403', '404', '405', '406'])).
% 3.99/4.20  thf(t55_relat_1, axiom,
% 3.99/4.20    (![A:$i]:
% 3.99/4.20     ( ( v1_relat_1 @ A ) =>
% 3.99/4.20       ( ![B:$i]:
% 3.99/4.20         ( ( v1_relat_1 @ B ) =>
% 3.99/4.20           ( ![C:$i]:
% 3.99/4.20             ( ( v1_relat_1 @ C ) =>
% 3.99/4.20               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 3.99/4.20                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 3.99/4.20  thf('408', plain,
% 3.99/4.20      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X17)
% 3.99/4.20          | ((k5_relat_1 @ (k5_relat_1 @ X18 @ X17) @ X19)
% 3.99/4.20              = (k5_relat_1 @ X18 @ (k5_relat_1 @ X17 @ X19)))
% 3.99/4.20          | ~ (v1_relat_1 @ X19)
% 3.99/4.20          | ~ (v1_relat_1 @ X18))),
% 3.99/4.20      inference('cnf', [status(esa)], [t55_relat_1])).
% 3.99/4.20  thf('409', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 3.99/4.20            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 3.99/4.20          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 3.99/4.20          | ~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ sk_C))),
% 3.99/4.20      inference('sup+', [status(thm)], ['407', '408'])).
% 3.99/4.20  thf('410', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 3.99/4.20      inference('demod', [status(thm)], ['106', '107'])).
% 3.99/4.20  thf('411', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('412', plain,
% 3.99/4.20      (![X0 : $i]:
% 3.99/4.20         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 3.99/4.20            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 3.99/4.20          | ~ (v1_relat_1 @ X0))),
% 3.99/4.20      inference('demod', [status(thm)], ['409', '410', '411'])).
% 3.99/4.20  thf('413', plain,
% 3.99/4.20      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 3.99/4.20          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 3.99/4.20        | ~ (v1_relat_1 @ sk_D))),
% 3.99/4.20      inference('sup+', [status(thm)], ['290', '412'])).
% 3.99/4.20  thf('414', plain, ((v1_relat_1 @ sk_D)),
% 3.99/4.20      inference('demod', [status(thm)], ['180', '181'])).
% 3.99/4.20  thf('415', plain,
% 3.99/4.20      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D)
% 3.99/4.20         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))),
% 3.99/4.20      inference('demod', [status(thm)], ['413', '414'])).
% 3.99/4.20  thf('416', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 3.99/4.20      inference('sup-', [status(thm)], ['173', '174'])).
% 3.99/4.20  thf('417', plain,
% 3.99/4.20      (![X15 : $i, X16 : $i]:
% 3.99/4.20         (((X15) = (k7_relat_1 @ X15 @ X16))
% 3.99/4.20          | ~ (v4_relat_1 @ X15 @ X16)
% 3.99/4.20          | ~ (v1_relat_1 @ X15))),
% 3.99/4.20      inference('cnf', [status(esa)], [t209_relat_1])).
% 3.99/4.20  thf('418', plain,
% 3.99/4.20      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_B)))),
% 3.99/4.20      inference('sup-', [status(thm)], ['416', '417'])).
% 3.99/4.20  thf('419', plain, ((v1_relat_1 @ sk_D)),
% 3.99/4.20      inference('demod', [status(thm)], ['180', '181'])).
% 3.99/4.20  thf('420', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 3.99/4.20      inference('demod', [status(thm)], ['418', '419'])).
% 3.99/4.20  thf('421', plain,
% 3.99/4.20      (![X11 : $i, X12 : $i]:
% 3.99/4.20         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 3.99/4.20          | ~ (v1_relat_1 @ X11))),
% 3.99/4.20      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.99/4.20  thf('422', plain,
% 3.99/4.20      (![X23 : $i]:
% 3.99/4.20         (((k5_relat_1 @ X23 @ (k6_partfun1 @ (k2_relat_1 @ X23))) = (X23))
% 3.99/4.20          | ~ (v1_relat_1 @ X23))),
% 3.99/4.20      inference('demod', [status(thm)], ['167', '168'])).
% 3.99/4.20  thf('423', plain,
% 3.99/4.20      (![X0 : $i, X1 : $i]:
% 3.99/4.20         (((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 3.99/4.20            (k6_partfun1 @ (k9_relat_1 @ X1 @ X0))) = (k7_relat_1 @ X1 @ X0))
% 3.99/4.20          | ~ (v1_relat_1 @ X1)
% 3.99/4.20          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 3.99/4.20      inference('sup+', [status(thm)], ['421', '422'])).
% 3.99/4.20  thf('424', plain,
% 3.99/4.20      (![X7 : $i, X8 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 3.99/4.20      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 3.99/4.20  thf('425', plain,
% 3.99/4.20      (![X0 : $i, X1 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X1)
% 3.99/4.20          | ((k5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 3.99/4.20              (k6_partfun1 @ (k9_relat_1 @ X1 @ X0))) = (k7_relat_1 @ X1 @ X0)))),
% 3.99/4.20      inference('clc', [status(thm)], ['423', '424'])).
% 3.99/4.20  thf('426', plain,
% 3.99/4.20      ((((k5_relat_1 @ sk_D @ (k6_partfun1 @ (k9_relat_1 @ sk_D @ sk_B)))
% 3.99/4.20          = (k7_relat_1 @ sk_D @ sk_B))
% 3.99/4.20        | ~ (v1_relat_1 @ sk_D))),
% 3.99/4.20      inference('sup+', [status(thm)], ['420', '425'])).
% 3.99/4.20  thf('427', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 3.99/4.20      inference('demod', [status(thm)], ['418', '419'])).
% 3.99/4.20  thf('428', plain,
% 3.99/4.20      (![X11 : $i, X12 : $i]:
% 3.99/4.20         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 3.99/4.20          | ~ (v1_relat_1 @ X11))),
% 3.99/4.20      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.99/4.20  thf('429', plain,
% 3.99/4.20      ((((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ sk_B))
% 3.99/4.20        | ~ (v1_relat_1 @ sk_D))),
% 3.99/4.20      inference('sup+', [status(thm)], ['427', '428'])).
% 3.99/4.20  thf('430', plain, ((v1_relat_1 @ sk_D)),
% 3.99/4.20      inference('demod', [status(thm)], ['180', '181'])).
% 3.99/4.20  thf('431', plain, (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ sk_B))),
% 3.99/4.20      inference('demod', [status(thm)], ['429', '430'])).
% 3.99/4.20  thf('432', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 3.99/4.20      inference('demod', [status(thm)], ['418', '419'])).
% 3.99/4.20  thf('433', plain, ((v1_relat_1 @ sk_D)),
% 3.99/4.20      inference('demod', [status(thm)], ['180', '181'])).
% 3.99/4.20  thf('434', plain,
% 3.99/4.20      (((k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))) = (sk_D))),
% 3.99/4.20      inference('demod', [status(thm)], ['426', '431', '432', '433'])).
% 3.99/4.20  thf(t78_relat_1, axiom,
% 3.99/4.20    (![A:$i]:
% 3.99/4.20     ( ( v1_relat_1 @ A ) =>
% 3.99/4.20       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 3.99/4.20  thf('435', plain,
% 3.99/4.20      (![X22 : $i]:
% 3.99/4.20         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X22)) @ X22) = (X22))
% 3.99/4.20          | ~ (v1_relat_1 @ X22))),
% 3.99/4.20      inference('cnf', [status(esa)], [t78_relat_1])).
% 3.99/4.20  thf('436', plain, (![X59 : $i]: ((k6_partfun1 @ X59) = (k6_relat_1 @ X59))),
% 3.99/4.20      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.99/4.20  thf('437', plain,
% 3.99/4.20      (![X22 : $i]:
% 3.99/4.20         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X22)) @ X22) = (X22))
% 3.99/4.20          | ~ (v1_relat_1 @ X22))),
% 3.99/4.20      inference('demod', [status(thm)], ['435', '436'])).
% 3.99/4.20  thf('438', plain,
% 3.99/4.20      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X17)
% 3.99/4.20          | ((k5_relat_1 @ (k5_relat_1 @ X18 @ X17) @ X19)
% 3.99/4.20              = (k5_relat_1 @ X18 @ (k5_relat_1 @ X17 @ X19)))
% 3.99/4.20          | ~ (v1_relat_1 @ X19)
% 3.99/4.20          | ~ (v1_relat_1 @ X18))),
% 3.99/4.20      inference('cnf', [status(esa)], [t55_relat_1])).
% 3.99/4.20  thf('439', plain,
% 3.99/4.20      (![X0 : $i, X1 : $i]:
% 3.99/4.20         (((k5_relat_1 @ X0 @ X1)
% 3.99/4.20            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 3.99/4.20               (k5_relat_1 @ X0 @ X1)))
% 3.99/4.20          | ~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 3.99/4.20          | ~ (v1_relat_1 @ X1)
% 3.99/4.20          | ~ (v1_relat_1 @ X0))),
% 3.99/4.20      inference('sup+', [status(thm)], ['437', '438'])).
% 3.99/4.20  thf('440', plain, (![X27 : $i]: (v1_relat_1 @ (k6_partfun1 @ X27))),
% 3.99/4.20      inference('demod', [status(thm)], ['43', '44'])).
% 3.99/4.20  thf('441', plain,
% 3.99/4.20      (![X0 : $i, X1 : $i]:
% 3.99/4.20         (((k5_relat_1 @ X0 @ X1)
% 3.99/4.20            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 3.99/4.20               (k5_relat_1 @ X0 @ X1)))
% 3.99/4.20          | ~ (v1_relat_1 @ X0)
% 3.99/4.20          | ~ (v1_relat_1 @ X1)
% 3.99/4.20          | ~ (v1_relat_1 @ X0))),
% 3.99/4.20      inference('demod', [status(thm)], ['439', '440'])).
% 3.99/4.20  thf('442', plain,
% 3.99/4.20      (![X0 : $i, X1 : $i]:
% 3.99/4.20         (~ (v1_relat_1 @ X1)
% 3.99/4.20          | ~ (v1_relat_1 @ X0)
% 3.99/4.20          | ((k5_relat_1 @ X0 @ X1)
% 3.99/4.20              = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 3.99/4.20                 (k5_relat_1 @ X0 @ X1))))),
% 3.99/4.20      inference('simplify', [status(thm)], ['441'])).
% 3.99/4.20  thf('443', plain,
% 3.99/4.20      ((((k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 3.99/4.20          = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D))
% 3.99/4.20        | ~ (v1_relat_1 @ sk_D)
% 3.99/4.20        | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))),
% 3.99/4.20      inference('sup+', [status(thm)], ['434', '442'])).
% 3.99/4.20  thf('444', plain,
% 3.99/4.20      (((k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))) = (sk_D))),
% 3.99/4.20      inference('demod', [status(thm)], ['426', '431', '432', '433'])).
% 3.99/4.20  thf('445', plain, ((v1_relat_1 @ sk_D)),
% 3.99/4.20      inference('demod', [status(thm)], ['180', '181'])).
% 3.99/4.20  thf('446', plain, (![X27 : $i]: (v1_relat_1 @ (k6_partfun1 @ X27))),
% 3.99/4.20      inference('demod', [status(thm)], ['43', '44'])).
% 3.99/4.20  thf('447', plain,
% 3.99/4.20      (((sk_D) = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ sk_D)) @ sk_D))),
% 3.99/4.20      inference('demod', [status(thm)], ['443', '444', '445', '446'])).
% 3.99/4.20  thf('448', plain, (((k9_relat_1 @ sk_C @ sk_A) = (k1_relat_1 @ sk_D))),
% 3.99/4.20      inference('demod', [status(thm)], ['190', '264'])).
% 3.99/4.20  thf('449', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 3.99/4.20      inference('demod', [status(thm)], ['282', '283'])).
% 3.99/4.20  thf('450', plain,
% 3.99/4.20      (![X11 : $i, X12 : $i]:
% 3.99/4.20         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 3.99/4.20          | ~ (v1_relat_1 @ X11))),
% 3.99/4.20      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.99/4.20  thf('451', plain,
% 3.99/4.20      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))
% 3.99/4.20        | ~ (v1_relat_1 @ sk_C))),
% 3.99/4.20      inference('sup+', [status(thm)], ['449', '450'])).
% 3.99/4.20  thf('452', plain, ((v1_relat_1 @ sk_C)),
% 3.99/4.20      inference('demod', [status(thm)], ['58', '59'])).
% 3.99/4.20  thf('453', plain, (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ sk_A))),
% 3.99/4.20      inference('demod', [status(thm)], ['451', '452'])).
% 3.99/4.20  thf('454', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 3.99/4.20      inference('sup+', [status(thm)], ['31', '32'])).
% 3.99/4.20  thf('455', plain, (((sk_B) = (k9_relat_1 @ sk_C @ sk_A))),
% 3.99/4.20      inference('demod', [status(thm)], ['453', '454'])).
% 3.99/4.20  thf('456', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 3.99/4.20      inference('sup+', [status(thm)], ['448', '455'])).
% 3.99/4.20  thf('457', plain, (((sk_D) = (k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D))),
% 3.99/4.20      inference('demod', [status(thm)], ['447', '456'])).
% 3.99/4.20  thf('458', plain,
% 3.99/4.20      (((sk_D) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))),
% 3.99/4.20      inference('demod', [status(thm)], ['415', '457'])).
% 3.99/4.20  thf('459', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 3.99/4.20      inference('sup+', [status(thm)], ['289', '458'])).
% 3.99/4.20  thf('460', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 3.99/4.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.99/4.20  thf('461', plain, ($false),
% 3.99/4.20      inference('simplify_reflect-', [status(thm)], ['459', '460'])).
% 3.99/4.20  
% 3.99/4.20  % SZS output end Refutation
% 3.99/4.20  
% 3.99/4.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
