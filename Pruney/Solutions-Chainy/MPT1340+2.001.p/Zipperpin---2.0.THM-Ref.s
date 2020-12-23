%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.I4YKN7Zd2O

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:04 EST 2020

% Result     : Theorem 8.73s
% Output     : Refutation 8.73s
% Verified   : 
% Statistics : Number of formulae       :  372 (13100 expanded)
%              Number of leaves         :   59 (3850 expanded)
%              Depth                    :   39
%              Number of atoms          : 3386 (281020 expanded)
%              Number of equality atoms :  210 (8357 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(t64_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_struct_0 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ B ) )
                    & ( v2_funct_1 @ C ) )
                 => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_tops_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X62: $i] :
      ( ( ( k2_struct_0 @ X62 )
        = ( u1_struct_0 @ X62 ) )
      | ~ ( l1_struct_0 @ X62 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X62: $i] :
      ( ( ( k2_struct_0 @ X62 )
        = ( u1_struct_0 @ X62 ) )
      | ~ ( l1_struct_0 @ X62 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( X58 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( v1_funct_2 @ X59 @ X60 @ X58 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X58 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X59 ) @ X59 )
        = ( k6_partfun1 @ X58 ) )
      | ~ ( v2_funct_1 @ X59 )
      | ( ( k2_relset_1 @ X60 @ X58 @ X59 )
       != X58 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('11',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_C_1 )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X62: $i] :
      ( ( ( k2_struct_0 @ X62 )
        = ( u1_struct_0 @ X62 ) )
      | ~ ( l1_struct_0 @ X62 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('13',plain,(
    ! [X62: $i] :
      ( ( ( k2_struct_0 @ X62 )
        = ( u1_struct_0 @ X62 ) )
      | ~ ( l1_struct_0 @ X62 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('14',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X62: $i] :
      ( ( ( k2_struct_0 @ X62 )
        = ( u1_struct_0 @ X62 ) )
      | ~ ( l1_struct_0 @ X62 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('23',plain,(
    ! [X62: $i] :
      ( ( ( k2_struct_0 @ X62 )
        = ( u1_struct_0 @ X62 ) )
      | ~ ( l1_struct_0 @ X62 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('24',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['22','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_C_1 )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_B ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','20','21','30','31'])).

thf('33',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ sk_C_1 )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf(t63_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ( X26
        = ( k2_funct_1 @ X27 ) )
      | ( ( k5_relat_1 @ X27 @ X26 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X27 ) ) )
      | ( ( k2_relat_1 @ X27 )
       != ( k1_relat_1 @ X26 ) )
      | ~ ( v2_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('35',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('36',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v1_funct_1 @ X26 )
      | ( X26
        = ( k2_funct_1 @ X27 ) )
      | ( ( k5_relat_1 @ X27 @ X26 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X27 ) ) )
      | ( ( k2_relat_1 @ X27 )
       != ( k1_relat_1 @ X26 ) )
      | ~ ( v2_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k6_partfun1 @ ( k2_struct_0 @ sk_B ) )
     != ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
     != ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_C_1
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t31_funct_2,axiom,(
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

thf('39',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( v2_funct_1 @ X55 )
      | ( ( k2_relset_1 @ X57 @ X56 @ X55 )
       != X56 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X55 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X57 ) ) )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X56 ) ) )
      | ~ ( v1_funct_2 @ X55 @ X57 @ X56 )
      | ~ ( v1_funct_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('40',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('43',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('44',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41','42','43','44'])).

thf('46',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('47',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('48',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('50',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( v2_funct_1 @ X55 )
      | ( ( k2_relset_1 @ X57 @ X56 @ X55 )
       != X56 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X55 ) )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X56 ) ) )
      | ~ ( v1_funct_2 @ X55 @ X57 @ X56 )
      | ~ ( v1_funct_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('51',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('54',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('55',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['51','52','53','54','55'])).

thf('57',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('59',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( v1_partfun1 @ X37 @ X38 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( v1_funct_1 @ X37 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('64',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_partfun1 @ X44 @ X43 )
      | ( ( k1_relat_1 @ X44 )
        = X43 )
      | ~ ( v4_relat_1 @ X44 @ X43 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v4_relat_1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('67',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( v1_relat_1 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('69',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('70',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('72',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('73',plain,(
    v4_relat_1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','70','73'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('75',plain,(
    ! [X63: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X63 ) )
      | ~ ( l1_struct_0 @ X63 )
      | ( v2_struct_0 @ X63 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('76',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['68','69'])).

thf('83',plain,
    ( ( ( k6_partfun1 @ ( k2_struct_0 @ sk_B ) )
     != ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( sk_C_1
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['37','48','57','80','81','82'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('84',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relat_1 @ X25 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('86',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf(t177_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf('88',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X21 @ ( k1_relat_1 @ X22 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X22 ) @ ( k9_relat_1 @ X22 @ X21 ) )
        = X21 )
      | ~ ( v2_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t177_funct_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v2_funct_1 @ sk_C_1 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k9_relat_1 @ sk_C_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['68','69'])).

thf('91',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_struct_0 @ sk_A ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k9_relat_1 @ sk_C_1 @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['89','90','91','92'])).

thf('94',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k9_relat_1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['86','93'])).

thf('95',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('96',plain,(
    ! [X14: $i] :
      ( ( ( k9_relat_1 @ X14 @ ( k1_relat_1 @ X14 ) )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('97',plain,
    ( ( ( k9_relat_1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) )
      = ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('99',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_relset_1 @ X35 @ X36 @ X34 )
        = ( k2_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('100',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['68','69'])).

thf('104',plain,
    ( ( k9_relat_1 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['97','102','103'])).

thf('105',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['94','104'])).

thf('106',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('107',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( v1_partfun1 @ X37 @ X38 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( v1_funct_1 @ X37 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('108',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('110',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('111',plain,(
    ! [X55: $i,X56: $i,X57: $i] :
      ( ~ ( v2_funct_1 @ X55 )
      | ( ( k2_relset_1 @ X57 @ X56 @ X55 )
       != X56 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X55 ) @ X56 @ X57 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X56 ) ) )
      | ~ ( v1_funct_2 @ X55 @ X57 @ X56 )
      | ~ ( v1_funct_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('112',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('115',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('116',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116'])).

thf('118',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['108','109','118'])).

thf('120',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_partfun1 @ X44 @ X43 )
      | ( ( k1_relat_1 @ X44 )
        = X43 )
      | ~ ( v4_relat_1 @ X44 @ X43 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('121',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('123',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('124',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('125',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['121','122','125'])).

thf('127',plain,(
    ! [X14: $i] :
      ( ( ( k9_relat_1 @ X14 @ ( k1_relat_1 @ X14 ) )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('128',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('130',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['105','130'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('132',plain,(
    ! [X61: $i] :
      ( ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X61 ) @ ( k2_relat_1 @ X61 ) ) ) )
      | ~ ( v1_funct_1 @ X61 )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('133',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('135',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('136',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('138',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('139',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('140',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('142',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('143',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['141','143'])).

thf('145',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('147',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['142'])).

thf('148',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v4_relat_1 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['146','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['145','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['144','151'])).

thf('153',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
      | ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['138','154'])).

thf('156',plain,(
    ! [X43: $i,X44: $i] :
      ( ( ( k1_relat_1 @ X44 )
       != X43 )
      | ( v1_partfun1 @ X44 @ X43 )
      | ~ ( v4_relat_1 @ X44 @ X43 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('157',plain,(
    ! [X44: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ~ ( v4_relat_1 @ X44 @ ( k1_relat_1 @ X44 ) )
      | ( v1_partfun1 @ X44 @ ( k1_relat_1 @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['155','157'])).

thf('159',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('160',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['84','160'])).

thf('162',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('163',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['68','69'])).

thf('164',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['161','162','163','164','165'])).

thf('167',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_partfun1 @ X44 @ X43 )
      | ( ( k1_relat_1 @ X44 )
        = X43 )
      | ~ ( v4_relat_1 @ X44 @ X43 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('168',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('170',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('171',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('172',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('173',plain,(
    ! [X14: $i] :
      ( ( ( k9_relat_1 @ X14 @ ( k1_relat_1 @ X14 ) )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('174',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('175',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['94','104'])).

thf('176',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('177',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,
    ( ( ( k6_partfun1 @ ( k2_struct_0 @ sk_B ) )
     != ( k6_partfun1 @ ( k2_struct_0 @ sk_B ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( sk_C_1
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['83','171','177'])).

thf('179',plain,
    ( ( sk_C_1
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,(
    ! [X25: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relat_1 @ X25 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('181',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('182',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( X58 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X59 )
      | ~ ( v1_funct_2 @ X59 @ X60 @ X58 )
      | ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X58 ) ) )
      | ( ( k5_relat_1 @ X59 @ ( k2_funct_1 @ X59 ) )
        = ( k6_partfun1 @ X60 ) )
      | ~ ( v2_funct_1 @ X59 )
      | ( ( k2_relset_1 @ X60 @ X58 @ X59 )
       != X58 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('183',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k5_relat_1 @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('185',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('187',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k5_relat_1 @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['183','184','185','186','187'])).

thf('189',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C_1 @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['188'])).

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

thf('190',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ( v2_funct_1 @ X24 )
      | ( ( k2_relat_1 @ X23 )
       != ( k1_relat_1 @ X24 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X23 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('191',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('192',plain,(
    ! [X19: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('193',plain,(
    ! [X47: $i] :
      ( ( k6_partfun1 @ X47 )
      = ( k6_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('194',plain,(
    ! [X19: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('196',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('197',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('198',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['68','69'])).

thf('200',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['191','194','195','196','197','198','199'])).

thf('201',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['180','200'])).

thf('202',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('203',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['68','69'])).

thf('204',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['201','202','203','204','205'])).

thf('207',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['206'])).

thf('208',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( sk_C_1
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['179','207'])).

thf('209',plain,(
    ! [X62: $i] :
      ( ( ( k2_struct_0 @ X62 )
        = ( u1_struct_0 @ X62 ) )
      | ~ ( l1_struct_0 @ X62 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('210',plain,(
    ! [X62: $i] :
      ( ( ( k2_struct_0 @ X62 )
        = ( u1_struct_0 @ X62 ) )
      | ~ ( l1_struct_0 @ X62 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('211',plain,(
    ! [X62: $i] :
      ( ( ( k2_struct_0 @ X62 )
        = ( u1_struct_0 @ X62 ) )
      | ~ ( l1_struct_0 @ X62 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('212',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['210','215'])).

thf('217',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['216','217'])).

thf('219',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( v1_partfun1 @ X37 @ X38 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( v1_funct_1 @ X37 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('221',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['221','222','223'])).

thf('225',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_partfun1 @ X44 @ X43 )
      | ( ( k1_relat_1 @ X44 )
        = X43 )
      | ~ ( v4_relat_1 @ X44 @ X43 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('226',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v4_relat_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['68','69'])).

thf('228',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('230',plain,(
    v4_relat_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['226','227','230'])).

thf('232',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('233',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['231','232'])).

thf('234',plain,(
    ! [X63: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X63 ) )
      | ~ ( l1_struct_0 @ X63 )
      | ( v2_struct_0 @ X63 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('235',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('240',plain,(
    ! [X62: $i] :
      ( ( ( k2_struct_0 @ X62 )
        = ( u1_struct_0 @ X62 ) )
      | ~ ( l1_struct_0 @ X62 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('241',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d4_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( k2_tops_2 @ A @ B @ C )
          = ( k2_funct_1 @ C ) ) ) ) )).

thf('242',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ( ( k2_relset_1 @ X65 @ X64 @ X66 )
       != X64 )
      | ~ ( v2_funct_1 @ X66 )
      | ( ( k2_tops_2 @ X65 @ X64 @ X66 )
        = ( k2_funct_1 @ X66 ) )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X64 ) ) )
      | ~ ( v1_funct_2 @ X66 @ X65 @ X64 )
      | ~ ( v1_funct_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('243',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    v1_funct_2 @ sk_C_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('246',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('248',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['243','244','245','246','247'])).

thf('249',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['240','248'])).

thf('250',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
      = ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['249','250'])).

thf('252',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 )
    = ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['251'])).

thf('253',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['218','239','252'])).

thf('254',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['209','253'])).

thf('255',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['254','255'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('257',plain,(
    ! [X20: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X20 ) )
      | ~ ( v2_funct_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('258',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('259',plain,(
    ! [X61: $i] :
      ( ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X61 ) @ ( k2_relat_1 @ X61 ) ) ) )
      | ~ ( v1_funct_1 @ X61 )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('260',plain,(
    ! [X64: $i,X65: $i,X66: $i] :
      ( ( ( k2_relset_1 @ X65 @ X64 @ X66 )
       != X64 )
      | ~ ( v2_funct_1 @ X66 )
      | ( ( k2_tops_2 @ X65 @ X64 @ X66 )
        = ( k2_funct_1 @ X66 ) )
      | ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X65 @ X64 ) ) )
      | ~ ( v1_funct_2 @ X66 @ X65 @ X64 )
      | ~ ( v1_funct_1 @ X66 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('261',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['259','260'])).

thf('262',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['261'])).

thf('263',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ ( k2_funct_1 @ sk_C_1 ) )
     != ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['258','262'])).

thf('264',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('265',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C_1 ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['117'])).

thf('266',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('267',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('268',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('269',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('270',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('271',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('272',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('273',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_relset_1 @ X35 @ X36 @ X34 )
        = ( k2_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('274',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['272','273'])).

thf('275',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('276',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['274','275'])).

thf('277',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('278',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['263','264','265','266','267','268','269','270','271','276','277'])).

thf('279',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['278'])).

thf('280',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['257','279'])).

thf('281',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['68','69'])).

thf('282',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C_1 ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['280','281','282','283'])).

thf('285',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C_1 ) ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['256','284'])).

thf('286',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ sk_C_1 )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['208','285'])).

thf(rc1_funct_2,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ( v1_funct_2 @ C @ A @ B )
      & ( v1_funct_1 @ C )
      & ( v5_relat_1 @ C @ B )
      & ( v4_relat_1 @ C @ A )
      & ( v1_relat_1 @ C )
      & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) )).

thf('287',plain,(
    ! [X45: $i,X46: $i] :
      ( m1_subset_1 @ ( sk_C @ X45 @ X46 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('288',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('289',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( r2_funct_2 @ X48 @ X49 @ X50 @ X50 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ~ ( v1_funct_2 @ X50 @ X48 @ X49 )
      | ~ ( v1_funct_1 @ X50 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_funct_2 @ X51 @ X48 @ X49 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('290',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['288','289'])).

thf('291',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,(
    v1_funct_2 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['290','291','292'])).

thf('294',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('295',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('296',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['237','238'])).

thf('297',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['293','294','295','296'])).

thf('298',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( sk_C @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['287','297'])).

thf('299',plain,(
    ! [X45: $i,X46: $i] :
      ( v1_funct_1 @ ( sk_C @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('300',plain,(
    ! [X45: $i,X46: $i] :
      ( v1_funct_2 @ ( sk_C @ X45 @ X46 ) @ X46 @ X45 ) ),
    inference(cnf,[status(esa)],[rc1_funct_2])).

thf('301',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['298','299','300'])).

thf('302',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['286','301'])).

thf('303',plain,(
    ! [X62: $i] :
      ( ( ( k2_struct_0 @ X62 )
        = ( u1_struct_0 @ X62 ) )
      | ~ ( l1_struct_0 @ X62 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('304',plain,(
    ! [X63: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X63 ) )
      | ~ ( l1_struct_0 @ X63 )
      | ( v2_struct_0 @ X63 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('305',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['303','304'])).

thf('306',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['305'])).

thf('307',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['302','306'])).

thf('308',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('309',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('310',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['307','308','309'])).

thf('311',plain,(
    $false ),
    inference(demod,[status(thm)],['0','310'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.I4YKN7Zd2O
% 0.14/0.37  % Computer   : n001.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 15:58:00 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 8.73/8.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.73/8.99  % Solved by: fo/fo7.sh
% 8.73/8.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.73/8.99  % done 10286 iterations in 8.498s
% 8.73/8.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.73/8.99  % SZS output start Refutation
% 8.73/8.99  thf(sk_A_type, type, sk_A: $i).
% 8.73/8.99  thf(sk_B_type, type, sk_B: $i).
% 8.73/8.99  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 8.73/8.99  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 8.73/8.99  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 8.73/8.99  thf(sk_C_1_type, type, sk_C_1: $i).
% 8.73/8.99  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 8.73/8.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.73/8.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.73/8.99  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 8.73/8.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.73/8.99  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 8.73/8.99  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 8.73/8.99  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.73/8.99  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 8.73/8.99  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 8.73/8.99  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 8.73/8.99  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 8.73/8.99  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 8.73/8.99  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 8.73/8.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 8.73/8.99  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.73/8.99  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 8.73/8.99  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 8.73/8.99  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 8.73/8.99  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 8.73/8.99  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.73/8.99  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 8.73/8.99  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 8.73/8.99  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 8.73/8.99  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 8.73/8.99  thf(t64_tops_2, conjecture,
% 8.73/8.99    (![A:$i]:
% 8.73/8.99     ( ( l1_struct_0 @ A ) =>
% 8.73/8.99       ( ![B:$i]:
% 8.73/8.99         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 8.73/8.99           ( ![C:$i]:
% 8.73/8.99             ( ( ( v1_funct_1 @ C ) & 
% 8.73/8.99                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 8.73/8.99                 ( m1_subset_1 @
% 8.73/8.99                   C @ 
% 8.73/8.99                   ( k1_zfmisc_1 @
% 8.73/8.99                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 8.73/8.99               ( ( ( ( k2_relset_1 @
% 8.73/8.99                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 8.73/8.99                     ( k2_struct_0 @ B ) ) & 
% 8.73/8.99                   ( v2_funct_1 @ C ) ) =>
% 8.73/8.99                 ( r2_funct_2 @
% 8.73/8.99                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 8.73/8.99                   ( k2_tops_2 @
% 8.73/8.99                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 8.73/8.99                     ( k2_tops_2 @
% 8.73/8.99                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 8.73/8.99                   C ) ) ) ) ) ) ))).
% 8.73/8.99  thf(zf_stmt_0, negated_conjecture,
% 8.73/8.99    (~( ![A:$i]:
% 8.73/8.99        ( ( l1_struct_0 @ A ) =>
% 8.73/8.99          ( ![B:$i]:
% 8.73/8.99            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 8.73/8.99              ( ![C:$i]:
% 8.73/8.99                ( ( ( v1_funct_1 @ C ) & 
% 8.73/8.99                    ( v1_funct_2 @
% 8.73/8.99                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 8.73/8.99                    ( m1_subset_1 @
% 8.73/8.99                      C @ 
% 8.73/8.99                      ( k1_zfmisc_1 @
% 8.73/8.99                        ( k2_zfmisc_1 @
% 8.73/8.99                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 8.73/8.99                  ( ( ( ( k2_relset_1 @
% 8.73/8.99                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 8.73/8.99                        ( k2_struct_0 @ B ) ) & 
% 8.73/8.99                      ( v2_funct_1 @ C ) ) =>
% 8.73/8.99                    ( r2_funct_2 @
% 8.73/8.99                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 8.73/8.99                      ( k2_tops_2 @
% 8.73/8.99                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 8.73/8.99                        ( k2_tops_2 @
% 8.73/8.99                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 8.73/8.99                      C ) ) ) ) ) ) ) )),
% 8.73/8.99    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 8.73/8.99  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf(d3_struct_0, axiom,
% 8.73/8.99    (![A:$i]:
% 8.73/8.99     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 8.73/8.99  thf('1', plain,
% 8.73/8.99      (![X62 : $i]:
% 8.73/8.99         (((k2_struct_0 @ X62) = (u1_struct_0 @ X62)) | ~ (l1_struct_0 @ X62))),
% 8.73/8.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.73/8.99  thf('2', plain,
% 8.73/8.99      (![X62 : $i]:
% 8.73/8.99         (((k2_struct_0 @ X62) = (u1_struct_0 @ X62)) | ~ (l1_struct_0 @ X62))),
% 8.73/8.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.73/8.99  thf('3', plain,
% 8.73/8.99      ((m1_subset_1 @ sk_C_1 @ 
% 8.73/8.99        (k1_zfmisc_1 @ 
% 8.73/8.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf('4', plain,
% 8.73/8.99      (((m1_subset_1 @ sk_C_1 @ 
% 8.73/8.99         (k1_zfmisc_1 @ 
% 8.73/8.99          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 8.73/8.99        | ~ (l1_struct_0 @ sk_A))),
% 8.73/8.99      inference('sup+', [status(thm)], ['2', '3'])).
% 8.73/8.99  thf('5', plain, ((l1_struct_0 @ sk_A)),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf('6', plain,
% 8.73/8.99      ((m1_subset_1 @ sk_C_1 @ 
% 8.73/8.99        (k1_zfmisc_1 @ 
% 8.73/8.99         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.73/8.99      inference('demod', [status(thm)], ['4', '5'])).
% 8.73/8.99  thf('7', plain,
% 8.73/8.99      (((m1_subset_1 @ sk_C_1 @ 
% 8.73/8.99         (k1_zfmisc_1 @ 
% 8.73/8.99          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 8.73/8.99        | ~ (l1_struct_0 @ sk_B))),
% 8.73/8.99      inference('sup+', [status(thm)], ['1', '6'])).
% 8.73/8.99  thf('8', plain, ((l1_struct_0 @ sk_B)),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf('9', plain,
% 8.73/8.99      ((m1_subset_1 @ sk_C_1 @ 
% 8.73/8.99        (k1_zfmisc_1 @ 
% 8.73/8.99         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 8.73/8.99      inference('demod', [status(thm)], ['7', '8'])).
% 8.73/8.99  thf(t35_funct_2, axiom,
% 8.73/8.99    (![A:$i,B:$i,C:$i]:
% 8.73/8.99     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.73/8.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.73/8.99       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 8.73/8.99         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 8.73/8.99           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 8.73/8.99             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 8.73/8.99  thf('10', plain,
% 8.73/8.99      (![X58 : $i, X59 : $i, X60 : $i]:
% 8.73/8.99         (((X58) = (k1_xboole_0))
% 8.73/8.99          | ~ (v1_funct_1 @ X59)
% 8.73/8.99          | ~ (v1_funct_2 @ X59 @ X60 @ X58)
% 8.73/8.99          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X58)))
% 8.73/8.99          | ((k5_relat_1 @ (k2_funct_1 @ X59) @ X59) = (k6_partfun1 @ X58))
% 8.73/8.99          | ~ (v2_funct_1 @ X59)
% 8.73/8.99          | ((k2_relset_1 @ X60 @ X58 @ X59) != (X58)))),
% 8.73/8.99      inference('cnf', [status(esa)], [t35_funct_2])).
% 8.73/8.99  thf('11', plain,
% 8.73/8.99      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 8.73/8.99          != (k2_struct_0 @ sk_B))
% 8.73/8.99        | ~ (v2_funct_1 @ sk_C_1)
% 8.73/8.99        | ((k5_relat_1 @ (k2_funct_1 @ sk_C_1) @ sk_C_1)
% 8.73/8.99            = (k6_partfun1 @ (k2_struct_0 @ sk_B)))
% 8.73/8.99        | ~ (v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 8.73/8.99        | ~ (v1_funct_1 @ sk_C_1)
% 8.73/8.99        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 8.73/8.99      inference('sup-', [status(thm)], ['9', '10'])).
% 8.73/8.99  thf('12', plain,
% 8.73/8.99      (![X62 : $i]:
% 8.73/8.99         (((k2_struct_0 @ X62) = (u1_struct_0 @ X62)) | ~ (l1_struct_0 @ X62))),
% 8.73/8.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.73/8.99  thf('13', plain,
% 8.73/8.99      (![X62 : $i]:
% 8.73/8.99         (((k2_struct_0 @ X62) = (u1_struct_0 @ X62)) | ~ (l1_struct_0 @ X62))),
% 8.73/8.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.73/8.99  thf('14', plain,
% 8.73/8.99      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 8.73/8.99         = (k2_struct_0 @ sk_B))),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf('15', plain,
% 8.73/8.99      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 8.73/8.99          = (k2_struct_0 @ sk_B))
% 8.73/8.99        | ~ (l1_struct_0 @ sk_A))),
% 8.73/8.99      inference('sup+', [status(thm)], ['13', '14'])).
% 8.73/8.99  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf('17', plain,
% 8.73/8.99      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 8.73/8.99         = (k2_struct_0 @ sk_B))),
% 8.73/8.99      inference('demod', [status(thm)], ['15', '16'])).
% 8.73/8.99  thf('18', plain,
% 8.73/8.99      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 8.73/8.99          = (k2_struct_0 @ sk_B))
% 8.73/8.99        | ~ (l1_struct_0 @ sk_B))),
% 8.73/8.99      inference('sup+', [status(thm)], ['12', '17'])).
% 8.73/8.99  thf('19', plain, ((l1_struct_0 @ sk_B)),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf('20', plain,
% 8.73/8.99      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 8.73/8.99         = (k2_struct_0 @ sk_B))),
% 8.73/8.99      inference('demod', [status(thm)], ['18', '19'])).
% 8.73/8.99  thf('21', plain, ((v2_funct_1 @ sk_C_1)),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf('22', plain,
% 8.73/8.99      (![X62 : $i]:
% 8.73/8.99         (((k2_struct_0 @ X62) = (u1_struct_0 @ X62)) | ~ (l1_struct_0 @ X62))),
% 8.73/8.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.73/8.99  thf('23', plain,
% 8.73/8.99      (![X62 : $i]:
% 8.73/8.99         (((k2_struct_0 @ X62) = (u1_struct_0 @ X62)) | ~ (l1_struct_0 @ X62))),
% 8.73/8.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.73/8.99  thf('24', plain,
% 8.73/8.99      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf('25', plain,
% 8.73/8.99      (((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.73/8.99        | ~ (l1_struct_0 @ sk_A))),
% 8.73/8.99      inference('sup+', [status(thm)], ['23', '24'])).
% 8.73/8.99  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf('27', plain,
% 8.73/8.99      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 8.73/8.99      inference('demod', [status(thm)], ['25', '26'])).
% 8.73/8.99  thf('28', plain,
% 8.73/8.99      (((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 8.73/8.99        | ~ (l1_struct_0 @ sk_B))),
% 8.73/8.99      inference('sup+', [status(thm)], ['22', '27'])).
% 8.73/8.99  thf('29', plain, ((l1_struct_0 @ sk_B)),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf('30', plain,
% 8.73/8.99      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 8.73/8.99      inference('demod', [status(thm)], ['28', '29'])).
% 8.73/8.99  thf('31', plain, ((v1_funct_1 @ sk_C_1)),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf('32', plain,
% 8.73/8.99      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 8.73/8.99        | ((k5_relat_1 @ (k2_funct_1 @ sk_C_1) @ sk_C_1)
% 8.73/8.99            = (k6_partfun1 @ (k2_struct_0 @ sk_B)))
% 8.73/8.99        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 8.73/8.99      inference('demod', [status(thm)], ['11', '20', '21', '30', '31'])).
% 8.73/8.99  thf('33', plain,
% 8.73/8.99      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 8.73/8.99        | ((k5_relat_1 @ (k2_funct_1 @ sk_C_1) @ sk_C_1)
% 8.73/8.99            = (k6_partfun1 @ (k2_struct_0 @ sk_B))))),
% 8.73/8.99      inference('simplify', [status(thm)], ['32'])).
% 8.73/8.99  thf(t63_funct_1, axiom,
% 8.73/8.99    (![A:$i]:
% 8.73/8.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 8.73/8.99       ( ![B:$i]:
% 8.73/8.99         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 8.73/8.99           ( ( ( v2_funct_1 @ A ) & 
% 8.73/8.99               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 8.73/8.99               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 8.73/8.99             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 8.73/8.99  thf('34', plain,
% 8.73/8.99      (![X26 : $i, X27 : $i]:
% 8.73/8.99         (~ (v1_relat_1 @ X26)
% 8.73/8.99          | ~ (v1_funct_1 @ X26)
% 8.73/8.99          | ((X26) = (k2_funct_1 @ X27))
% 8.73/8.99          | ((k5_relat_1 @ X27 @ X26) != (k6_relat_1 @ (k1_relat_1 @ X27)))
% 8.73/8.99          | ((k2_relat_1 @ X27) != (k1_relat_1 @ X26))
% 8.73/8.99          | ~ (v2_funct_1 @ X27)
% 8.73/8.99          | ~ (v1_funct_1 @ X27)
% 8.73/8.99          | ~ (v1_relat_1 @ X27))),
% 8.73/8.99      inference('cnf', [status(esa)], [t63_funct_1])).
% 8.73/8.99  thf(redefinition_k6_partfun1, axiom,
% 8.73/8.99    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 8.73/8.99  thf('35', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 8.73/8.99      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.73/8.99  thf('36', plain,
% 8.73/8.99      (![X26 : $i, X27 : $i]:
% 8.73/8.99         (~ (v1_relat_1 @ X26)
% 8.73/8.99          | ~ (v1_funct_1 @ X26)
% 8.73/8.99          | ((X26) = (k2_funct_1 @ X27))
% 8.73/8.99          | ((k5_relat_1 @ X27 @ X26) != (k6_partfun1 @ (k1_relat_1 @ X27)))
% 8.73/8.99          | ((k2_relat_1 @ X27) != (k1_relat_1 @ X26))
% 8.73/8.99          | ~ (v2_funct_1 @ X27)
% 8.73/8.99          | ~ (v1_funct_1 @ X27)
% 8.73/8.99          | ~ (v1_relat_1 @ X27))),
% 8.73/8.99      inference('demod', [status(thm)], ['34', '35'])).
% 8.73/8.99  thf('37', plain,
% 8.73/8.99      ((((k6_partfun1 @ (k2_struct_0 @ sk_B))
% 8.73/8.99          != (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1))))
% 8.73/8.99        | ((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 8.73/8.99        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/8.99        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/8.99        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/8.99        | ((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) != (k1_relat_1 @ sk_C_1))
% 8.73/8.99        | ((sk_C_1) = (k2_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 8.73/8.99        | ~ (v1_funct_1 @ sk_C_1)
% 8.73/8.99        | ~ (v1_relat_1 @ sk_C_1))),
% 8.73/8.99      inference('sup-', [status(thm)], ['33', '36'])).
% 8.73/8.99  thf('38', plain,
% 8.73/8.99      ((m1_subset_1 @ sk_C_1 @ 
% 8.73/8.99        (k1_zfmisc_1 @ 
% 8.73/8.99         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 8.73/8.99      inference('demod', [status(thm)], ['7', '8'])).
% 8.73/8.99  thf(t31_funct_2, axiom,
% 8.73/8.99    (![A:$i,B:$i,C:$i]:
% 8.73/8.99     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.73/8.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.73/8.99       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 8.73/8.99         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 8.73/8.99           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 8.73/8.99           ( m1_subset_1 @
% 8.73/8.99             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 8.73/8.99  thf('39', plain,
% 8.73/8.99      (![X55 : $i, X56 : $i, X57 : $i]:
% 8.73/8.99         (~ (v2_funct_1 @ X55)
% 8.73/8.99          | ((k2_relset_1 @ X57 @ X56 @ X55) != (X56))
% 8.73/8.99          | (m1_subset_1 @ (k2_funct_1 @ X55) @ 
% 8.73/8.99             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X57)))
% 8.73/8.99          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X56)))
% 8.73/8.99          | ~ (v1_funct_2 @ X55 @ X57 @ X56)
% 8.73/8.99          | ~ (v1_funct_1 @ X55))),
% 8.73/8.99      inference('cnf', [status(esa)], [t31_funct_2])).
% 8.73/8.99  thf('40', plain,
% 8.73/8.99      ((~ (v1_funct_1 @ sk_C_1)
% 8.73/8.99        | ~ (v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 8.73/8.99        | (m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 8.73/8.99           (k1_zfmisc_1 @ 
% 8.73/8.99            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 8.73/8.99        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 8.73/8.99            != (k2_struct_0 @ sk_B))
% 8.73/8.99        | ~ (v2_funct_1 @ sk_C_1))),
% 8.73/8.99      inference('sup-', [status(thm)], ['38', '39'])).
% 8.73/8.99  thf('41', plain, ((v1_funct_1 @ sk_C_1)),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf('42', plain,
% 8.73/8.99      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 8.73/8.99      inference('demod', [status(thm)], ['28', '29'])).
% 8.73/8.99  thf('43', plain,
% 8.73/8.99      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 8.73/8.99         = (k2_struct_0 @ sk_B))),
% 8.73/8.99      inference('demod', [status(thm)], ['18', '19'])).
% 8.73/8.99  thf('44', plain, ((v2_funct_1 @ sk_C_1)),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf('45', plain,
% 8.73/8.99      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 8.73/8.99         (k1_zfmisc_1 @ 
% 8.73/8.99          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 8.73/8.99        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 8.73/8.99      inference('demod', [status(thm)], ['40', '41', '42', '43', '44'])).
% 8.73/8.99  thf('46', plain,
% 8.73/8.99      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 8.73/8.99        (k1_zfmisc_1 @ 
% 8.73/8.99         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 8.73/8.99      inference('simplify', [status(thm)], ['45'])).
% 8.73/8.99  thf(cc1_relset_1, axiom,
% 8.73/8.99    (![A:$i,B:$i,C:$i]:
% 8.73/8.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.73/8.99       ( v1_relat_1 @ C ) ))).
% 8.73/8.99  thf('47', plain,
% 8.73/8.99      (![X28 : $i, X29 : $i, X30 : $i]:
% 8.73/8.99         ((v1_relat_1 @ X28)
% 8.73/8.99          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 8.73/8.99      inference('cnf', [status(esa)], [cc1_relset_1])).
% 8.73/8.99  thf('48', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 8.73/8.99      inference('sup-', [status(thm)], ['46', '47'])).
% 8.73/8.99  thf('49', plain,
% 8.73/8.99      ((m1_subset_1 @ sk_C_1 @ 
% 8.73/8.99        (k1_zfmisc_1 @ 
% 8.73/8.99         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 8.73/8.99      inference('demod', [status(thm)], ['7', '8'])).
% 8.73/8.99  thf('50', plain,
% 8.73/8.99      (![X55 : $i, X56 : $i, X57 : $i]:
% 8.73/8.99         (~ (v2_funct_1 @ X55)
% 8.73/8.99          | ((k2_relset_1 @ X57 @ X56 @ X55) != (X56))
% 8.73/8.99          | (v1_funct_1 @ (k2_funct_1 @ X55))
% 8.73/8.99          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X56)))
% 8.73/8.99          | ~ (v1_funct_2 @ X55 @ X57 @ X56)
% 8.73/8.99          | ~ (v1_funct_1 @ X55))),
% 8.73/8.99      inference('cnf', [status(esa)], [t31_funct_2])).
% 8.73/8.99  thf('51', plain,
% 8.73/8.99      ((~ (v1_funct_1 @ sk_C_1)
% 8.73/8.99        | ~ (v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 8.73/8.99        | (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/8.99        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 8.73/8.99            != (k2_struct_0 @ sk_B))
% 8.73/8.99        | ~ (v2_funct_1 @ sk_C_1))),
% 8.73/8.99      inference('sup-', [status(thm)], ['49', '50'])).
% 8.73/8.99  thf('52', plain, ((v1_funct_1 @ sk_C_1)),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf('53', plain,
% 8.73/8.99      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 8.73/8.99      inference('demod', [status(thm)], ['28', '29'])).
% 8.73/8.99  thf('54', plain,
% 8.73/8.99      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 8.73/8.99         = (k2_struct_0 @ sk_B))),
% 8.73/8.99      inference('demod', [status(thm)], ['18', '19'])).
% 8.73/8.99  thf('55', plain, ((v2_funct_1 @ sk_C_1)),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf('56', plain,
% 8.73/8.99      (((v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/8.99        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 8.73/8.99      inference('demod', [status(thm)], ['51', '52', '53', '54', '55'])).
% 8.73/8.99  thf('57', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 8.73/8.99      inference('simplify', [status(thm)], ['56'])).
% 8.73/8.99  thf('58', plain,
% 8.73/8.99      ((m1_subset_1 @ sk_C_1 @ 
% 8.73/8.99        (k1_zfmisc_1 @ 
% 8.73/8.99         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.73/8.99      inference('demod', [status(thm)], ['4', '5'])).
% 8.73/8.99  thf(cc5_funct_2, axiom,
% 8.73/8.99    (![A:$i,B:$i]:
% 8.73/8.99     ( ( ~( v1_xboole_0 @ B ) ) =>
% 8.73/8.99       ( ![C:$i]:
% 8.73/8.99         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.73/8.99           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 8.73/8.99             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 8.73/8.99  thf('59', plain,
% 8.73/8.99      (![X37 : $i, X38 : $i, X39 : $i]:
% 8.73/8.99         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 8.73/8.99          | (v1_partfun1 @ X37 @ X38)
% 8.73/8.99          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 8.73/8.99          | ~ (v1_funct_1 @ X37)
% 8.73/8.99          | (v1_xboole_0 @ X39))),
% 8.73/8.99      inference('cnf', [status(esa)], [cc5_funct_2])).
% 8.73/8.99  thf('60', plain,
% 8.73/8.99      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 8.73/8.99        | ~ (v1_funct_1 @ sk_C_1)
% 8.73/8.99        | ~ (v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.73/8.99        | (v1_partfun1 @ sk_C_1 @ (k2_struct_0 @ sk_A)))),
% 8.73/8.99      inference('sup-', [status(thm)], ['58', '59'])).
% 8.73/8.99  thf('61', plain, ((v1_funct_1 @ sk_C_1)),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf('62', plain,
% 8.73/8.99      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 8.73/8.99      inference('demod', [status(thm)], ['25', '26'])).
% 8.73/8.99  thf('63', plain,
% 8.73/8.99      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 8.73/8.99        | (v1_partfun1 @ sk_C_1 @ (k2_struct_0 @ sk_A)))),
% 8.73/8.99      inference('demod', [status(thm)], ['60', '61', '62'])).
% 8.73/8.99  thf(d4_partfun1, axiom,
% 8.73/8.99    (![A:$i,B:$i]:
% 8.73/8.99     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 8.73/8.99       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 8.73/8.99  thf('64', plain,
% 8.73/8.99      (![X43 : $i, X44 : $i]:
% 8.73/8.99         (~ (v1_partfun1 @ X44 @ X43)
% 8.73/8.99          | ((k1_relat_1 @ X44) = (X43))
% 8.73/8.99          | ~ (v4_relat_1 @ X44 @ X43)
% 8.73/8.99          | ~ (v1_relat_1 @ X44))),
% 8.73/8.99      inference('cnf', [status(esa)], [d4_partfun1])).
% 8.73/8.99  thf('65', plain,
% 8.73/8.99      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 8.73/8.99        | ~ (v1_relat_1 @ sk_C_1)
% 8.73/8.99        | ~ (v4_relat_1 @ sk_C_1 @ (k2_struct_0 @ sk_A))
% 8.73/8.99        | ((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A)))),
% 8.73/8.99      inference('sup-', [status(thm)], ['63', '64'])).
% 8.73/8.99  thf('66', plain,
% 8.73/8.99      ((m1_subset_1 @ sk_C_1 @ 
% 8.73/8.99        (k1_zfmisc_1 @ 
% 8.73/8.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf(cc2_relat_1, axiom,
% 8.73/8.99    (![A:$i]:
% 8.73/8.99     ( ( v1_relat_1 @ A ) =>
% 8.73/8.99       ( ![B:$i]:
% 8.73/8.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 8.73/8.99  thf('67', plain,
% 8.73/8.99      (![X10 : $i, X11 : $i]:
% 8.73/8.99         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 8.73/8.99          | (v1_relat_1 @ X10)
% 8.73/8.99          | ~ (v1_relat_1 @ X11))),
% 8.73/8.99      inference('cnf', [status(esa)], [cc2_relat_1])).
% 8.73/8.99  thf('68', plain,
% 8.73/8.99      ((~ (v1_relat_1 @ 
% 8.73/8.99           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 8.73/8.99        | (v1_relat_1 @ sk_C_1))),
% 8.73/8.99      inference('sup-', [status(thm)], ['66', '67'])).
% 8.73/8.99  thf(fc6_relat_1, axiom,
% 8.73/8.99    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 8.73/8.99  thf('69', plain,
% 8.73/8.99      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 8.73/8.99      inference('cnf', [status(esa)], [fc6_relat_1])).
% 8.73/8.99  thf('70', plain, ((v1_relat_1 @ sk_C_1)),
% 8.73/8.99      inference('demod', [status(thm)], ['68', '69'])).
% 8.73/8.99  thf('71', plain,
% 8.73/8.99      ((m1_subset_1 @ sk_C_1 @ 
% 8.73/8.99        (k1_zfmisc_1 @ 
% 8.73/8.99         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.73/8.99      inference('demod', [status(thm)], ['4', '5'])).
% 8.73/8.99  thf(cc2_relset_1, axiom,
% 8.73/8.99    (![A:$i,B:$i,C:$i]:
% 8.73/8.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.73/8.99       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 8.73/8.99  thf('72', plain,
% 8.73/8.99      (![X31 : $i, X32 : $i, X33 : $i]:
% 8.73/8.99         ((v4_relat_1 @ X31 @ X32)
% 8.73/8.99          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 8.73/8.99      inference('cnf', [status(esa)], [cc2_relset_1])).
% 8.73/8.99  thf('73', plain, ((v4_relat_1 @ sk_C_1 @ (k2_struct_0 @ sk_A))),
% 8.73/8.99      inference('sup-', [status(thm)], ['71', '72'])).
% 8.73/8.99  thf('74', plain,
% 8.73/8.99      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 8.73/8.99        | ((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A)))),
% 8.73/8.99      inference('demod', [status(thm)], ['65', '70', '73'])).
% 8.73/8.99  thf(fc2_struct_0, axiom,
% 8.73/8.99    (![A:$i]:
% 8.73/8.99     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 8.73/8.99       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 8.73/8.99  thf('75', plain,
% 8.73/8.99      (![X63 : $i]:
% 8.73/8.99         (~ (v1_xboole_0 @ (u1_struct_0 @ X63))
% 8.73/8.99          | ~ (l1_struct_0 @ X63)
% 8.73/8.99          | (v2_struct_0 @ X63))),
% 8.73/8.99      inference('cnf', [status(esa)], [fc2_struct_0])).
% 8.73/8.99  thf('76', plain,
% 8.73/8.99      ((((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))
% 8.73/8.99        | (v2_struct_0 @ sk_B)
% 8.73/8.99        | ~ (l1_struct_0 @ sk_B))),
% 8.73/8.99      inference('sup-', [status(thm)], ['74', '75'])).
% 8.73/8.99  thf('77', plain, ((l1_struct_0 @ sk_B)),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf('78', plain,
% 8.73/8.99      ((((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 8.73/8.99      inference('demod', [status(thm)], ['76', '77'])).
% 8.73/8.99  thf('79', plain, (~ (v2_struct_0 @ sk_B)),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf('80', plain, (((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))),
% 8.73/8.99      inference('clc', [status(thm)], ['78', '79'])).
% 8.73/8.99  thf('81', plain, ((v1_funct_1 @ sk_C_1)),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf('82', plain, ((v1_relat_1 @ sk_C_1)),
% 8.73/8.99      inference('demod', [status(thm)], ['68', '69'])).
% 8.73/8.99  thf('83', plain,
% 8.73/8.99      ((((k6_partfun1 @ (k2_struct_0 @ sk_B))
% 8.73/8.99          != (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1))))
% 8.73/8.99        | ((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 8.73/8.99        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/8.99        | ((k2_relat_1 @ (k2_funct_1 @ sk_C_1)) != (k2_struct_0 @ sk_A))
% 8.73/8.99        | ((sk_C_1) = (k2_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 8.73/8.99      inference('demod', [status(thm)], ['37', '48', '57', '80', '81', '82'])).
% 8.73/8.99  thf(t55_funct_1, axiom,
% 8.73/8.99    (![A:$i]:
% 8.73/8.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 8.73/8.99       ( ( v2_funct_1 @ A ) =>
% 8.73/8.99         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 8.73/8.99           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 8.73/8.99  thf('84', plain,
% 8.73/8.99      (![X25 : $i]:
% 8.73/8.99         (~ (v2_funct_1 @ X25)
% 8.73/8.99          | ((k2_relat_1 @ X25) = (k1_relat_1 @ (k2_funct_1 @ X25)))
% 8.73/8.99          | ~ (v1_funct_1 @ X25)
% 8.73/8.99          | ~ (v1_relat_1 @ X25))),
% 8.73/8.99      inference('cnf', [status(esa)], [t55_funct_1])).
% 8.73/8.99  thf(d10_xboole_0, axiom,
% 8.73/8.99    (![A:$i,B:$i]:
% 8.73/8.99     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.73/8.99  thf('85', plain,
% 8.73/8.99      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 8.73/8.99      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.73/8.99  thf('86', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 8.73/8.99      inference('simplify', [status(thm)], ['85'])).
% 8.73/8.99  thf('87', plain, (((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))),
% 8.73/8.99      inference('clc', [status(thm)], ['78', '79'])).
% 8.73/8.99  thf(t177_funct_1, axiom,
% 8.73/8.99    (![A:$i]:
% 8.73/8.99     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 8.73/8.99       ( ![B:$i]:
% 8.73/8.99         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 8.73/8.99           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 8.73/8.99             ( B ) ) ) ) ))).
% 8.73/8.99  thf('88', plain,
% 8.73/8.99      (![X21 : $i, X22 : $i]:
% 8.73/8.99         (~ (r1_tarski @ X21 @ (k1_relat_1 @ X22))
% 8.73/8.99          | ((k9_relat_1 @ (k2_funct_1 @ X22) @ (k9_relat_1 @ X22 @ X21))
% 8.73/8.99              = (X21))
% 8.73/8.99          | ~ (v2_funct_1 @ X22)
% 8.73/8.99          | ~ (v1_funct_1 @ X22)
% 8.73/8.99          | ~ (v1_relat_1 @ X22))),
% 8.73/8.99      inference('cnf', [status(esa)], [t177_funct_1])).
% 8.73/8.99  thf('89', plain,
% 8.73/8.99      (![X0 : $i]:
% 8.73/8.99         (~ (r1_tarski @ X0 @ (k2_struct_0 @ sk_A))
% 8.73/8.99          | ~ (v1_relat_1 @ sk_C_1)
% 8.73/8.99          | ~ (v1_funct_1 @ sk_C_1)
% 8.73/8.99          | ~ (v2_funct_1 @ sk_C_1)
% 8.73/8.99          | ((k9_relat_1 @ (k2_funct_1 @ sk_C_1) @ (k9_relat_1 @ sk_C_1 @ X0))
% 8.73/8.99              = (X0)))),
% 8.73/8.99      inference('sup-', [status(thm)], ['87', '88'])).
% 8.73/8.99  thf('90', plain, ((v1_relat_1 @ sk_C_1)),
% 8.73/8.99      inference('demod', [status(thm)], ['68', '69'])).
% 8.73/8.99  thf('91', plain, ((v1_funct_1 @ sk_C_1)),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf('92', plain, ((v2_funct_1 @ sk_C_1)),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf('93', plain,
% 8.73/8.99      (![X0 : $i]:
% 8.73/8.99         (~ (r1_tarski @ X0 @ (k2_struct_0 @ sk_A))
% 8.73/8.99          | ((k9_relat_1 @ (k2_funct_1 @ sk_C_1) @ (k9_relat_1 @ sk_C_1 @ X0))
% 8.73/8.99              = (X0)))),
% 8.73/8.99      inference('demod', [status(thm)], ['89', '90', '91', '92'])).
% 8.73/8.99  thf('94', plain,
% 8.73/8.99      (((k9_relat_1 @ (k2_funct_1 @ sk_C_1) @ 
% 8.73/8.99         (k9_relat_1 @ sk_C_1 @ (k2_struct_0 @ sk_A))) = (k2_struct_0 @ sk_A))),
% 8.73/8.99      inference('sup-', [status(thm)], ['86', '93'])).
% 8.73/8.99  thf('95', plain, (((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))),
% 8.73/8.99      inference('clc', [status(thm)], ['78', '79'])).
% 8.73/8.99  thf(t146_relat_1, axiom,
% 8.73/8.99    (![A:$i]:
% 8.73/8.99     ( ( v1_relat_1 @ A ) =>
% 8.73/8.99       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 8.73/8.99  thf('96', plain,
% 8.73/8.99      (![X14 : $i]:
% 8.73/8.99         (((k9_relat_1 @ X14 @ (k1_relat_1 @ X14)) = (k2_relat_1 @ X14))
% 8.73/8.99          | ~ (v1_relat_1 @ X14))),
% 8.73/8.99      inference('cnf', [status(esa)], [t146_relat_1])).
% 8.73/8.99  thf('97', plain,
% 8.73/8.99      ((((k9_relat_1 @ sk_C_1 @ (k2_struct_0 @ sk_A)) = (k2_relat_1 @ sk_C_1))
% 8.73/8.99        | ~ (v1_relat_1 @ sk_C_1))),
% 8.73/8.99      inference('sup+', [status(thm)], ['95', '96'])).
% 8.73/8.99  thf('98', plain,
% 8.73/8.99      ((m1_subset_1 @ sk_C_1 @ 
% 8.73/8.99        (k1_zfmisc_1 @ 
% 8.73/8.99         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf(redefinition_k2_relset_1, axiom,
% 8.73/8.99    (![A:$i,B:$i,C:$i]:
% 8.73/8.99     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.73/8.99       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 8.73/8.99  thf('99', plain,
% 8.73/8.99      (![X34 : $i, X35 : $i, X36 : $i]:
% 8.73/8.99         (((k2_relset_1 @ X35 @ X36 @ X34) = (k2_relat_1 @ X34))
% 8.73/8.99          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 8.73/8.99      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 8.73/8.99  thf('100', plain,
% 8.73/8.99      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 8.73/8.99         = (k2_relat_1 @ sk_C_1))),
% 8.73/8.99      inference('sup-', [status(thm)], ['98', '99'])).
% 8.73/8.99  thf('101', plain,
% 8.73/8.99      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 8.73/8.99         = (k2_struct_0 @ sk_B))),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf('102', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B))),
% 8.73/8.99      inference('sup+', [status(thm)], ['100', '101'])).
% 8.73/8.99  thf('103', plain, ((v1_relat_1 @ sk_C_1)),
% 8.73/8.99      inference('demod', [status(thm)], ['68', '69'])).
% 8.73/8.99  thf('104', plain,
% 8.73/8.99      (((k9_relat_1 @ sk_C_1 @ (k2_struct_0 @ sk_A)) = (k2_struct_0 @ sk_B))),
% 8.73/8.99      inference('demod', [status(thm)], ['97', '102', '103'])).
% 8.73/8.99  thf('105', plain,
% 8.73/8.99      (((k9_relat_1 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B))
% 8.73/8.99         = (k2_struct_0 @ sk_A))),
% 8.73/8.99      inference('demod', [status(thm)], ['94', '104'])).
% 8.73/8.99  thf('106', plain,
% 8.73/8.99      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 8.73/8.99        (k1_zfmisc_1 @ 
% 8.73/8.99         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 8.73/8.99      inference('simplify', [status(thm)], ['45'])).
% 8.73/8.99  thf('107', plain,
% 8.73/8.99      (![X37 : $i, X38 : $i, X39 : $i]:
% 8.73/8.99         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 8.73/8.99          | (v1_partfun1 @ X37 @ X38)
% 8.73/8.99          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 8.73/8.99          | ~ (v1_funct_1 @ X37)
% 8.73/8.99          | (v1_xboole_0 @ X39))),
% 8.73/8.99      inference('cnf', [status(esa)], [cc5_funct_2])).
% 8.73/8.99  thf('108', plain,
% 8.73/8.99      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 8.73/8.99        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/8.99        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B) @ 
% 8.73/8.99             (k2_struct_0 @ sk_A))
% 8.73/8.99        | (v1_partfun1 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B)))),
% 8.73/8.99      inference('sup-', [status(thm)], ['106', '107'])).
% 8.73/8.99  thf('109', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 8.73/8.99      inference('simplify', [status(thm)], ['56'])).
% 8.73/8.99  thf('110', plain,
% 8.73/8.99      ((m1_subset_1 @ sk_C_1 @ 
% 8.73/8.99        (k1_zfmisc_1 @ 
% 8.73/8.99         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 8.73/8.99      inference('demod', [status(thm)], ['7', '8'])).
% 8.73/8.99  thf('111', plain,
% 8.73/8.99      (![X55 : $i, X56 : $i, X57 : $i]:
% 8.73/8.99         (~ (v2_funct_1 @ X55)
% 8.73/8.99          | ((k2_relset_1 @ X57 @ X56 @ X55) != (X56))
% 8.73/8.99          | (v1_funct_2 @ (k2_funct_1 @ X55) @ X56 @ X57)
% 8.73/8.99          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X56)))
% 8.73/8.99          | ~ (v1_funct_2 @ X55 @ X57 @ X56)
% 8.73/8.99          | ~ (v1_funct_1 @ X55))),
% 8.73/8.99      inference('cnf', [status(esa)], [t31_funct_2])).
% 8.73/8.99  thf('112', plain,
% 8.73/8.99      ((~ (v1_funct_1 @ sk_C_1)
% 8.73/8.99        | ~ (v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 8.73/8.99        | (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B) @ 
% 8.73/8.99           (k2_struct_0 @ sk_A))
% 8.73/8.99        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 8.73/8.99            != (k2_struct_0 @ sk_B))
% 8.73/8.99        | ~ (v2_funct_1 @ sk_C_1))),
% 8.73/8.99      inference('sup-', [status(thm)], ['110', '111'])).
% 8.73/8.99  thf('113', plain, ((v1_funct_1 @ sk_C_1)),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf('114', plain,
% 8.73/8.99      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 8.73/8.99      inference('demod', [status(thm)], ['28', '29'])).
% 8.73/8.99  thf('115', plain,
% 8.73/8.99      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 8.73/8.99         = (k2_struct_0 @ sk_B))),
% 8.73/8.99      inference('demod', [status(thm)], ['18', '19'])).
% 8.73/8.99  thf('116', plain, ((v2_funct_1 @ sk_C_1)),
% 8.73/8.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/8.99  thf('117', plain,
% 8.73/8.99      (((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B) @ 
% 8.73/8.99         (k2_struct_0 @ sk_A))
% 8.73/8.99        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 8.73/8.99      inference('demod', [status(thm)], ['112', '113', '114', '115', '116'])).
% 8.73/8.99  thf('118', plain,
% 8.73/8.99      ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B) @ 
% 8.73/8.99        (k2_struct_0 @ sk_A))),
% 8.73/8.99      inference('simplify', [status(thm)], ['117'])).
% 8.73/8.99  thf('119', plain,
% 8.73/8.99      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 8.73/8.99        | (v1_partfun1 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B)))),
% 8.73/8.99      inference('demod', [status(thm)], ['108', '109', '118'])).
% 8.73/8.99  thf('120', plain,
% 8.73/8.99      (![X43 : $i, X44 : $i]:
% 8.73/8.99         (~ (v1_partfun1 @ X44 @ X43)
% 8.73/8.99          | ((k1_relat_1 @ X44) = (X43))
% 8.73/8.99          | ~ (v4_relat_1 @ X44 @ X43)
% 8.73/8.99          | ~ (v1_relat_1 @ X44))),
% 8.73/8.99      inference('cnf', [status(esa)], [d4_partfun1])).
% 8.73/8.99  thf('121', plain,
% 8.73/8.99      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 8.73/8.99        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/8.99        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B))
% 8.73/8.99        | ((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k2_struct_0 @ sk_B)))),
% 8.73/9.00      inference('sup-', [status(thm)], ['119', '120'])).
% 8.73/9.00  thf('122', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 8.73/9.00      inference('sup-', [status(thm)], ['46', '47'])).
% 8.73/9.00  thf('123', plain,
% 8.73/9.00      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 8.73/9.00        (k1_zfmisc_1 @ 
% 8.73/9.00         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 8.73/9.00      inference('simplify', [status(thm)], ['45'])).
% 8.73/9.00  thf('124', plain,
% 8.73/9.00      (![X31 : $i, X32 : $i, X33 : $i]:
% 8.73/9.00         ((v4_relat_1 @ X31 @ X32)
% 8.73/9.00          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 8.73/9.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 8.73/9.00  thf('125', plain,
% 8.73/9.00      ((v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B))),
% 8.73/9.00      inference('sup-', [status(thm)], ['123', '124'])).
% 8.73/9.00  thf('126', plain,
% 8.73/9.00      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 8.73/9.00        | ((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k2_struct_0 @ sk_B)))),
% 8.73/9.00      inference('demod', [status(thm)], ['121', '122', '125'])).
% 8.73/9.00  thf('127', plain,
% 8.73/9.00      (![X14 : $i]:
% 8.73/9.00         (((k9_relat_1 @ X14 @ (k1_relat_1 @ X14)) = (k2_relat_1 @ X14))
% 8.73/9.00          | ~ (v1_relat_1 @ X14))),
% 8.73/9.00      inference('cnf', [status(esa)], [t146_relat_1])).
% 8.73/9.00  thf('128', plain,
% 8.73/9.00      ((((k9_relat_1 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B))
% 8.73/9.00          = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 8.73/9.00        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 8.73/9.00        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 8.73/9.00      inference('sup+', [status(thm)], ['126', '127'])).
% 8.73/9.00  thf('129', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 8.73/9.00      inference('sup-', [status(thm)], ['46', '47'])).
% 8.73/9.00  thf('130', plain,
% 8.73/9.00      ((((k9_relat_1 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B))
% 8.73/9.00          = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 8.73/9.00        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 8.73/9.00      inference('demod', [status(thm)], ['128', '129'])).
% 8.73/9.00  thf('131', plain,
% 8.73/9.00      ((((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 8.73/9.00        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 8.73/9.00      inference('sup+', [status(thm)], ['105', '130'])).
% 8.73/9.00  thf(t3_funct_2, axiom,
% 8.73/9.00    (![A:$i]:
% 8.73/9.00     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 8.73/9.00       ( ( v1_funct_1 @ A ) & 
% 8.73/9.00         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 8.73/9.00         ( m1_subset_1 @
% 8.73/9.00           A @ 
% 8.73/9.00           ( k1_zfmisc_1 @
% 8.73/9.00             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 8.73/9.00  thf('132', plain,
% 8.73/9.00      (![X61 : $i]:
% 8.73/9.00         ((m1_subset_1 @ X61 @ 
% 8.73/9.00           (k1_zfmisc_1 @ 
% 8.73/9.00            (k2_zfmisc_1 @ (k1_relat_1 @ X61) @ (k2_relat_1 @ X61))))
% 8.73/9.00          | ~ (v1_funct_1 @ X61)
% 8.73/9.00          | ~ (v1_relat_1 @ X61))),
% 8.73/9.00      inference('cnf', [status(esa)], [t3_funct_2])).
% 8.73/9.00  thf('133', plain,
% 8.73/9.00      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 8.73/9.00         (k1_zfmisc_1 @ 
% 8.73/9.00          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ 
% 8.73/9.00           (k2_struct_0 @ sk_A))))
% 8.73/9.00        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 8.73/9.00        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/9.00        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 8.73/9.00      inference('sup+', [status(thm)], ['131', '132'])).
% 8.73/9.00  thf('134', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 8.73/9.00      inference('sup-', [status(thm)], ['46', '47'])).
% 8.73/9.00  thf('135', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 8.73/9.00      inference('simplify', [status(thm)], ['56'])).
% 8.73/9.00  thf('136', plain,
% 8.73/9.00      (((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 8.73/9.00         (k1_zfmisc_1 @ 
% 8.73/9.00          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ 
% 8.73/9.00           (k2_struct_0 @ sk_A))))
% 8.73/9.00        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 8.73/9.00      inference('demod', [status(thm)], ['133', '134', '135'])).
% 8.73/9.00  thf('137', plain,
% 8.73/9.00      (![X31 : $i, X32 : $i, X33 : $i]:
% 8.73/9.00         ((v4_relat_1 @ X31 @ X32)
% 8.73/9.00          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 8.73/9.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 8.73/9.00  thf('138', plain,
% 8.73/9.00      (((v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 8.73/9.00        | (v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ 
% 8.73/9.00           (k1_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 8.73/9.00      inference('sup-', [status(thm)], ['136', '137'])).
% 8.73/9.00  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 8.73/9.00  thf('139', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 8.73/9.00      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 8.73/9.00  thf(t8_boole, axiom,
% 8.73/9.00    (![A:$i,B:$i]:
% 8.73/9.00     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 8.73/9.00  thf('140', plain,
% 8.73/9.00      (![X3 : $i, X4 : $i]:
% 8.73/9.00         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 8.73/9.00      inference('cnf', [status(esa)], [t8_boole])).
% 8.73/9.00  thf('141', plain,
% 8.73/9.00      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 8.73/9.00      inference('sup-', [status(thm)], ['139', '140'])).
% 8.73/9.00  thf(t113_zfmisc_1, axiom,
% 8.73/9.00    (![A:$i,B:$i]:
% 8.73/9.00     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 8.73/9.00       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 8.73/9.00  thf('142', plain,
% 8.73/9.00      (![X6 : $i, X7 : $i]:
% 8.73/9.00         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 8.73/9.00      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 8.73/9.00  thf('143', plain,
% 8.73/9.00      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 8.73/9.00      inference('simplify', [status(thm)], ['142'])).
% 8.73/9.00  thf('144', plain,
% 8.73/9.00      (![X0 : $i, X1 : $i]:
% 8.73/9.00         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 8.73/9.00      inference('sup+', [status(thm)], ['141', '143'])).
% 8.73/9.00  thf('145', plain,
% 8.73/9.00      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 8.73/9.00        (k1_zfmisc_1 @ 
% 8.73/9.00         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 8.73/9.00      inference('simplify', [status(thm)], ['45'])).
% 8.73/9.00  thf('146', plain,
% 8.73/9.00      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 8.73/9.00      inference('sup-', [status(thm)], ['139', '140'])).
% 8.73/9.00  thf('147', plain,
% 8.73/9.00      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 8.73/9.00      inference('simplify', [status(thm)], ['142'])).
% 8.73/9.00  thf('148', plain,
% 8.73/9.00      (![X31 : $i, X32 : $i, X33 : $i]:
% 8.73/9.00         ((v4_relat_1 @ X31 @ X32)
% 8.73/9.00          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 8.73/9.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 8.73/9.00  thf('149', plain,
% 8.73/9.00      (![X0 : $i, X1 : $i]:
% 8.73/9.00         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 8.73/9.00          | (v4_relat_1 @ X1 @ X0))),
% 8.73/9.00      inference('sup-', [status(thm)], ['147', '148'])).
% 8.73/9.00  thf('150', plain,
% 8.73/9.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.73/9.00         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 8.73/9.00          | ~ (v1_xboole_0 @ X0)
% 8.73/9.00          | (v4_relat_1 @ X1 @ X2))),
% 8.73/9.00      inference('sup-', [status(thm)], ['146', '149'])).
% 8.73/9.00  thf('151', plain,
% 8.73/9.00      (![X0 : $i]:
% 8.73/9.00         ((v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ X0)
% 8.73/9.00          | ~ (v1_xboole_0 @ 
% 8.73/9.00               (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 8.73/9.00      inference('sup-', [status(thm)], ['145', '150'])).
% 8.73/9.00  thf('152', plain,
% 8.73/9.00      (![X0 : $i]:
% 8.73/9.00         (~ (v1_xboole_0 @ k1_xboole_0)
% 8.73/9.00          | ~ (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 8.73/9.00          | (v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ X0))),
% 8.73/9.00      inference('sup-', [status(thm)], ['144', '151'])).
% 8.73/9.00  thf('153', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 8.73/9.00      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 8.73/9.00  thf('154', plain,
% 8.73/9.00      (![X0 : $i]:
% 8.73/9.00         (~ (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 8.73/9.00          | (v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ X0))),
% 8.73/9.00      inference('demod', [status(thm)], ['152', '153'])).
% 8.73/9.00  thf('155', plain,
% 8.73/9.00      ((v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ 
% 8.73/9.00        (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 8.73/9.00      inference('clc', [status(thm)], ['138', '154'])).
% 8.73/9.00  thf('156', plain,
% 8.73/9.00      (![X43 : $i, X44 : $i]:
% 8.73/9.00         (((k1_relat_1 @ X44) != (X43))
% 8.73/9.00          | (v1_partfun1 @ X44 @ X43)
% 8.73/9.00          | ~ (v4_relat_1 @ X44 @ X43)
% 8.73/9.00          | ~ (v1_relat_1 @ X44))),
% 8.73/9.00      inference('cnf', [status(esa)], [d4_partfun1])).
% 8.73/9.00  thf('157', plain,
% 8.73/9.00      (![X44 : $i]:
% 8.73/9.00         (~ (v1_relat_1 @ X44)
% 8.73/9.00          | ~ (v4_relat_1 @ X44 @ (k1_relat_1 @ X44))
% 8.73/9.00          | (v1_partfun1 @ X44 @ (k1_relat_1 @ X44)))),
% 8.73/9.00      inference('simplify', [status(thm)], ['156'])).
% 8.73/9.00  thf('158', plain,
% 8.73/9.00      (((v1_partfun1 @ (k2_funct_1 @ sk_C_1) @ 
% 8.73/9.00         (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 8.73/9.00        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 8.73/9.00      inference('sup-', [status(thm)], ['155', '157'])).
% 8.73/9.00  thf('159', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 8.73/9.00      inference('sup-', [status(thm)], ['46', '47'])).
% 8.73/9.00  thf('160', plain,
% 8.73/9.00      ((v1_partfun1 @ (k2_funct_1 @ sk_C_1) @ 
% 8.73/9.00        (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 8.73/9.00      inference('demod', [status(thm)], ['158', '159'])).
% 8.73/9.00  thf('161', plain,
% 8.73/9.00      (((v1_partfun1 @ (k2_funct_1 @ sk_C_1) @ (k2_relat_1 @ sk_C_1))
% 8.73/9.00        | ~ (v1_relat_1 @ sk_C_1)
% 8.73/9.00        | ~ (v1_funct_1 @ sk_C_1)
% 8.73/9.00        | ~ (v2_funct_1 @ sk_C_1))),
% 8.73/9.00      inference('sup+', [status(thm)], ['84', '160'])).
% 8.73/9.00  thf('162', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B))),
% 8.73/9.00      inference('sup+', [status(thm)], ['100', '101'])).
% 8.73/9.00  thf('163', plain, ((v1_relat_1 @ sk_C_1)),
% 8.73/9.00      inference('demod', [status(thm)], ['68', '69'])).
% 8.73/9.00  thf('164', plain, ((v1_funct_1 @ sk_C_1)),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('165', plain, ((v2_funct_1 @ sk_C_1)),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('166', plain,
% 8.73/9.00      ((v1_partfun1 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B))),
% 8.73/9.00      inference('demod', [status(thm)], ['161', '162', '163', '164', '165'])).
% 8.73/9.00  thf('167', plain,
% 8.73/9.00      (![X43 : $i, X44 : $i]:
% 8.73/9.00         (~ (v1_partfun1 @ X44 @ X43)
% 8.73/9.00          | ((k1_relat_1 @ X44) = (X43))
% 8.73/9.00          | ~ (v4_relat_1 @ X44 @ X43)
% 8.73/9.00          | ~ (v1_relat_1 @ X44))),
% 8.73/9.00      inference('cnf', [status(esa)], [d4_partfun1])).
% 8.73/9.00  thf('168', plain,
% 8.73/9.00      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/9.00        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B))
% 8.73/9.00        | ((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k2_struct_0 @ sk_B)))),
% 8.73/9.00      inference('sup-', [status(thm)], ['166', '167'])).
% 8.73/9.00  thf('169', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 8.73/9.00      inference('sup-', [status(thm)], ['46', '47'])).
% 8.73/9.00  thf('170', plain,
% 8.73/9.00      ((v4_relat_1 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B))),
% 8.73/9.00      inference('sup-', [status(thm)], ['123', '124'])).
% 8.73/9.00  thf('171', plain,
% 8.73/9.00      (((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k2_struct_0 @ sk_B))),
% 8.73/9.00      inference('demod', [status(thm)], ['168', '169', '170'])).
% 8.73/9.00  thf('172', plain,
% 8.73/9.00      (((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k2_struct_0 @ sk_B))),
% 8.73/9.00      inference('demod', [status(thm)], ['168', '169', '170'])).
% 8.73/9.00  thf('173', plain,
% 8.73/9.00      (![X14 : $i]:
% 8.73/9.00         (((k9_relat_1 @ X14 @ (k1_relat_1 @ X14)) = (k2_relat_1 @ X14))
% 8.73/9.00          | ~ (v1_relat_1 @ X14))),
% 8.73/9.00      inference('cnf', [status(esa)], [t146_relat_1])).
% 8.73/9.00  thf('174', plain,
% 8.73/9.00      ((((k9_relat_1 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B))
% 8.73/9.00          = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 8.73/9.00        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 8.73/9.00      inference('sup+', [status(thm)], ['172', '173'])).
% 8.73/9.00  thf('175', plain,
% 8.73/9.00      (((k9_relat_1 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B))
% 8.73/9.00         = (k2_struct_0 @ sk_A))),
% 8.73/9.00      inference('demod', [status(thm)], ['94', '104'])).
% 8.73/9.00  thf('176', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 8.73/9.00      inference('sup-', [status(thm)], ['46', '47'])).
% 8.73/9.00  thf('177', plain,
% 8.73/9.00      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 8.73/9.00      inference('demod', [status(thm)], ['174', '175', '176'])).
% 8.73/9.00  thf('178', plain,
% 8.73/9.00      ((((k6_partfun1 @ (k2_struct_0 @ sk_B))
% 8.73/9.00          != (k6_partfun1 @ (k2_struct_0 @ sk_B)))
% 8.73/9.00        | ((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 8.73/9.00        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/9.00        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 8.73/9.00        | ((sk_C_1) = (k2_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 8.73/9.00      inference('demod', [status(thm)], ['83', '171', '177'])).
% 8.73/9.00  thf('179', plain,
% 8.73/9.00      ((((sk_C_1) = (k2_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 8.73/9.00        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/9.00        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 8.73/9.00      inference('simplify', [status(thm)], ['178'])).
% 8.73/9.00  thf('180', plain,
% 8.73/9.00      (![X25 : $i]:
% 8.73/9.00         (~ (v2_funct_1 @ X25)
% 8.73/9.00          | ((k2_relat_1 @ X25) = (k1_relat_1 @ (k2_funct_1 @ X25)))
% 8.73/9.00          | ~ (v1_funct_1 @ X25)
% 8.73/9.00          | ~ (v1_relat_1 @ X25))),
% 8.73/9.00      inference('cnf', [status(esa)], [t55_funct_1])).
% 8.73/9.00  thf('181', plain,
% 8.73/9.00      ((m1_subset_1 @ sk_C_1 @ 
% 8.73/9.00        (k1_zfmisc_1 @ 
% 8.73/9.00         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 8.73/9.00      inference('demod', [status(thm)], ['7', '8'])).
% 8.73/9.00  thf('182', plain,
% 8.73/9.00      (![X58 : $i, X59 : $i, X60 : $i]:
% 8.73/9.00         (((X58) = (k1_xboole_0))
% 8.73/9.00          | ~ (v1_funct_1 @ X59)
% 8.73/9.00          | ~ (v1_funct_2 @ X59 @ X60 @ X58)
% 8.73/9.00          | ~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X58)))
% 8.73/9.00          | ((k5_relat_1 @ X59 @ (k2_funct_1 @ X59)) = (k6_partfun1 @ X60))
% 8.73/9.00          | ~ (v2_funct_1 @ X59)
% 8.73/9.00          | ((k2_relset_1 @ X60 @ X58 @ X59) != (X58)))),
% 8.73/9.00      inference('cnf', [status(esa)], [t35_funct_2])).
% 8.73/9.00  thf('183', plain,
% 8.73/9.00      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 8.73/9.00          != (k2_struct_0 @ sk_B))
% 8.73/9.00        | ~ (v2_funct_1 @ sk_C_1)
% 8.73/9.00        | ((k5_relat_1 @ sk_C_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/9.00            = (k6_partfun1 @ (k2_struct_0 @ sk_A)))
% 8.73/9.00        | ~ (v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 8.73/9.00        | ~ (v1_funct_1 @ sk_C_1)
% 8.73/9.00        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 8.73/9.00      inference('sup-', [status(thm)], ['181', '182'])).
% 8.73/9.00  thf('184', plain,
% 8.73/9.00      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C_1)
% 8.73/9.00         = (k2_struct_0 @ sk_B))),
% 8.73/9.00      inference('demod', [status(thm)], ['18', '19'])).
% 8.73/9.00  thf('185', plain, ((v2_funct_1 @ sk_C_1)),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('186', plain,
% 8.73/9.00      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 8.73/9.00      inference('demod', [status(thm)], ['28', '29'])).
% 8.73/9.00  thf('187', plain, ((v1_funct_1 @ sk_C_1)),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('188', plain,
% 8.73/9.00      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 8.73/9.00        | ((k5_relat_1 @ sk_C_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/9.00            = (k6_partfun1 @ (k2_struct_0 @ sk_A)))
% 8.73/9.00        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 8.73/9.00      inference('demod', [status(thm)], ['183', '184', '185', '186', '187'])).
% 8.73/9.00  thf('189', plain,
% 8.73/9.00      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 8.73/9.00        | ((k5_relat_1 @ sk_C_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/9.00            = (k6_partfun1 @ (k2_struct_0 @ sk_A))))),
% 8.73/9.00      inference('simplify', [status(thm)], ['188'])).
% 8.73/9.00  thf(t48_funct_1, axiom,
% 8.73/9.00    (![A:$i]:
% 8.73/9.00     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 8.73/9.00       ( ![B:$i]:
% 8.73/9.00         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 8.73/9.00           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 8.73/9.00               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 8.73/9.00             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 8.73/9.00  thf('190', plain,
% 8.73/9.00      (![X23 : $i, X24 : $i]:
% 8.73/9.00         (~ (v1_relat_1 @ X23)
% 8.73/9.00          | ~ (v1_funct_1 @ X23)
% 8.73/9.00          | (v2_funct_1 @ X24)
% 8.73/9.00          | ((k2_relat_1 @ X23) != (k1_relat_1 @ X24))
% 8.73/9.00          | ~ (v2_funct_1 @ (k5_relat_1 @ X23 @ X24))
% 8.73/9.00          | ~ (v1_funct_1 @ X24)
% 8.73/9.00          | ~ (v1_relat_1 @ X24))),
% 8.73/9.00      inference('cnf', [status(esa)], [t48_funct_1])).
% 8.73/9.00  thf('191', plain,
% 8.73/9.00      ((~ (v2_funct_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)))
% 8.73/9.00        | ((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 8.73/9.00        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/9.00        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/9.00        | ((k2_relat_1 @ sk_C_1) != (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 8.73/9.00        | (v2_funct_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/9.00        | ~ (v1_funct_1 @ sk_C_1)
% 8.73/9.00        | ~ (v1_relat_1 @ sk_C_1))),
% 8.73/9.00      inference('sup-', [status(thm)], ['189', '190'])).
% 8.73/9.00  thf(fc4_funct_1, axiom,
% 8.73/9.00    (![A:$i]:
% 8.73/9.00     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 8.73/9.00       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 8.73/9.00  thf('192', plain, (![X19 : $i]: (v2_funct_1 @ (k6_relat_1 @ X19))),
% 8.73/9.00      inference('cnf', [status(esa)], [fc4_funct_1])).
% 8.73/9.00  thf('193', plain, (![X47 : $i]: ((k6_partfun1 @ X47) = (k6_relat_1 @ X47))),
% 8.73/9.00      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.73/9.00  thf('194', plain, (![X19 : $i]: (v2_funct_1 @ (k6_partfun1 @ X19))),
% 8.73/9.00      inference('demod', [status(thm)], ['192', '193'])).
% 8.73/9.00  thf('195', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 8.73/9.00      inference('sup-', [status(thm)], ['46', '47'])).
% 8.73/9.00  thf('196', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 8.73/9.00      inference('simplify', [status(thm)], ['56'])).
% 8.73/9.00  thf('197', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B))),
% 8.73/9.00      inference('sup+', [status(thm)], ['100', '101'])).
% 8.73/9.00  thf('198', plain, ((v1_funct_1 @ sk_C_1)),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('199', plain, ((v1_relat_1 @ sk_C_1)),
% 8.73/9.00      inference('demod', [status(thm)], ['68', '69'])).
% 8.73/9.00  thf('200', plain,
% 8.73/9.00      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 8.73/9.00        | ((k2_struct_0 @ sk_B) != (k1_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 8.73/9.00        | (v2_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 8.73/9.00      inference('demod', [status(thm)],
% 8.73/9.00                ['191', '194', '195', '196', '197', '198', '199'])).
% 8.73/9.00  thf('201', plain,
% 8.73/9.00      ((((k2_struct_0 @ sk_B) != (k2_relat_1 @ sk_C_1))
% 8.73/9.00        | ~ (v1_relat_1 @ sk_C_1)
% 8.73/9.00        | ~ (v1_funct_1 @ sk_C_1)
% 8.73/9.00        | ~ (v2_funct_1 @ sk_C_1)
% 8.73/9.00        | (v2_funct_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/9.00        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 8.73/9.00      inference('sup-', [status(thm)], ['180', '200'])).
% 8.73/9.00  thf('202', plain, (((k2_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_B))),
% 8.73/9.00      inference('sup+', [status(thm)], ['100', '101'])).
% 8.73/9.00  thf('203', plain, ((v1_relat_1 @ sk_C_1)),
% 8.73/9.00      inference('demod', [status(thm)], ['68', '69'])).
% 8.73/9.00  thf('204', plain, ((v1_funct_1 @ sk_C_1)),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('205', plain, ((v2_funct_1 @ sk_C_1)),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('206', plain,
% 8.73/9.00      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 8.73/9.00        | (v2_funct_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/9.00        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 8.73/9.00      inference('demod', [status(thm)], ['201', '202', '203', '204', '205'])).
% 8.73/9.00  thf('207', plain,
% 8.73/9.00      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 8.73/9.00        | (v2_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 8.73/9.00      inference('simplify', [status(thm)], ['206'])).
% 8.73/9.00  thf('208', plain,
% 8.73/9.00      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 8.73/9.00        | ((sk_C_1) = (k2_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 8.73/9.00      inference('clc', [status(thm)], ['179', '207'])).
% 8.73/9.00  thf('209', plain,
% 8.73/9.00      (![X62 : $i]:
% 8.73/9.00         (((k2_struct_0 @ X62) = (u1_struct_0 @ X62)) | ~ (l1_struct_0 @ X62))),
% 8.73/9.00      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.73/9.00  thf('210', plain,
% 8.73/9.00      (![X62 : $i]:
% 8.73/9.00         (((k2_struct_0 @ X62) = (u1_struct_0 @ X62)) | ~ (l1_struct_0 @ X62))),
% 8.73/9.00      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.73/9.00  thf('211', plain,
% 8.73/9.00      (![X62 : $i]:
% 8.73/9.00         (((k2_struct_0 @ X62) = (u1_struct_0 @ X62)) | ~ (l1_struct_0 @ X62))),
% 8.73/9.00      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.73/9.00  thf('212', plain,
% 8.73/9.00      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 8.73/9.00          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 8.73/9.00           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)) @ 
% 8.73/9.00          sk_C_1)),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('213', plain,
% 8.73/9.00      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 8.73/9.00           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 8.73/9.00            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)) @ 
% 8.73/9.00           sk_C_1)
% 8.73/9.00        | ~ (l1_struct_0 @ sk_A))),
% 8.73/9.00      inference('sup-', [status(thm)], ['211', '212'])).
% 8.73/9.00  thf('214', plain, ((l1_struct_0 @ sk_A)),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('215', plain,
% 8.73/9.00      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 8.73/9.00          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 8.73/9.00           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)) @ 
% 8.73/9.00          sk_C_1)),
% 8.73/9.00      inference('demod', [status(thm)], ['213', '214'])).
% 8.73/9.00  thf('216', plain,
% 8.73/9.00      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 8.73/9.00           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 8.73/9.00            (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)) @ 
% 8.73/9.00           sk_C_1)
% 8.73/9.00        | ~ (l1_struct_0 @ sk_A))),
% 8.73/9.00      inference('sup-', [status(thm)], ['210', '215'])).
% 8.73/9.00  thf('217', plain, ((l1_struct_0 @ sk_A)),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('218', plain,
% 8.73/9.00      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 8.73/9.00          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 8.73/9.00           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)) @ 
% 8.73/9.00          sk_C_1)),
% 8.73/9.00      inference('demod', [status(thm)], ['216', '217'])).
% 8.73/9.00  thf('219', plain,
% 8.73/9.00      ((m1_subset_1 @ sk_C_1 @ 
% 8.73/9.00        (k1_zfmisc_1 @ 
% 8.73/9.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('220', plain,
% 8.73/9.00      (![X37 : $i, X38 : $i, X39 : $i]:
% 8.73/9.00         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 8.73/9.00          | (v1_partfun1 @ X37 @ X38)
% 8.73/9.00          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 8.73/9.00          | ~ (v1_funct_1 @ X37)
% 8.73/9.00          | (v1_xboole_0 @ X39))),
% 8.73/9.00      inference('cnf', [status(esa)], [cc5_funct_2])).
% 8.73/9.00  thf('221', plain,
% 8.73/9.00      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 8.73/9.00        | ~ (v1_funct_1 @ sk_C_1)
% 8.73/9.00        | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.73/9.00        | (v1_partfun1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 8.73/9.00      inference('sup-', [status(thm)], ['219', '220'])).
% 8.73/9.00  thf('222', plain, ((v1_funct_1 @ sk_C_1)),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('223', plain,
% 8.73/9.00      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('224', plain,
% 8.73/9.00      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 8.73/9.00        | (v1_partfun1 @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 8.73/9.00      inference('demod', [status(thm)], ['221', '222', '223'])).
% 8.73/9.00  thf('225', plain,
% 8.73/9.00      (![X43 : $i, X44 : $i]:
% 8.73/9.00         (~ (v1_partfun1 @ X44 @ X43)
% 8.73/9.00          | ((k1_relat_1 @ X44) = (X43))
% 8.73/9.00          | ~ (v4_relat_1 @ X44 @ X43)
% 8.73/9.00          | ~ (v1_relat_1 @ X44))),
% 8.73/9.00      inference('cnf', [status(esa)], [d4_partfun1])).
% 8.73/9.00  thf('226', plain,
% 8.73/9.00      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 8.73/9.00        | ~ (v1_relat_1 @ sk_C_1)
% 8.73/9.00        | ~ (v4_relat_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 8.73/9.00        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 8.73/9.00      inference('sup-', [status(thm)], ['224', '225'])).
% 8.73/9.00  thf('227', plain, ((v1_relat_1 @ sk_C_1)),
% 8.73/9.00      inference('demod', [status(thm)], ['68', '69'])).
% 8.73/9.00  thf('228', plain,
% 8.73/9.00      ((m1_subset_1 @ sk_C_1 @ 
% 8.73/9.00        (k1_zfmisc_1 @ 
% 8.73/9.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('229', plain,
% 8.73/9.00      (![X31 : $i, X32 : $i, X33 : $i]:
% 8.73/9.00         ((v4_relat_1 @ X31 @ X32)
% 8.73/9.00          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 8.73/9.00      inference('cnf', [status(esa)], [cc2_relset_1])).
% 8.73/9.00  thf('230', plain, ((v4_relat_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 8.73/9.00      inference('sup-', [status(thm)], ['228', '229'])).
% 8.73/9.00  thf('231', plain,
% 8.73/9.00      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 8.73/9.00        | ((k1_relat_1 @ sk_C_1) = (u1_struct_0 @ sk_A)))),
% 8.73/9.00      inference('demod', [status(thm)], ['226', '227', '230'])).
% 8.73/9.00  thf('232', plain, (((k1_relat_1 @ sk_C_1) = (k2_struct_0 @ sk_A))),
% 8.73/9.00      inference('clc', [status(thm)], ['78', '79'])).
% 8.73/9.00  thf('233', plain,
% 8.73/9.00      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 8.73/9.00        | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 8.73/9.00      inference('demod', [status(thm)], ['231', '232'])).
% 8.73/9.00  thf('234', plain,
% 8.73/9.00      (![X63 : $i]:
% 8.73/9.00         (~ (v1_xboole_0 @ (u1_struct_0 @ X63))
% 8.73/9.00          | ~ (l1_struct_0 @ X63)
% 8.73/9.00          | (v2_struct_0 @ X63))),
% 8.73/9.00      inference('cnf', [status(esa)], [fc2_struct_0])).
% 8.73/9.00  thf('235', plain,
% 8.73/9.00      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 8.73/9.00        | (v2_struct_0 @ sk_B)
% 8.73/9.00        | ~ (l1_struct_0 @ sk_B))),
% 8.73/9.00      inference('sup-', [status(thm)], ['233', '234'])).
% 8.73/9.00  thf('236', plain, ((l1_struct_0 @ sk_B)),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('237', plain,
% 8.73/9.00      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 8.73/9.00      inference('demod', [status(thm)], ['235', '236'])).
% 8.73/9.00  thf('238', plain, (~ (v2_struct_0 @ sk_B)),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('239', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 8.73/9.00      inference('clc', [status(thm)], ['237', '238'])).
% 8.73/9.00  thf('240', plain,
% 8.73/9.00      (![X62 : $i]:
% 8.73/9.00         (((k2_struct_0 @ X62) = (u1_struct_0 @ X62)) | ~ (l1_struct_0 @ X62))),
% 8.73/9.00      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.73/9.00  thf('241', plain,
% 8.73/9.00      ((m1_subset_1 @ sk_C_1 @ 
% 8.73/9.00        (k1_zfmisc_1 @ 
% 8.73/9.00         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.73/9.00      inference('demod', [status(thm)], ['4', '5'])).
% 8.73/9.00  thf(d4_tops_2, axiom,
% 8.73/9.00    (![A:$i,B:$i,C:$i]:
% 8.73/9.00     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.73/9.00         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.73/9.00       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 8.73/9.00         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 8.73/9.00  thf('242', plain,
% 8.73/9.00      (![X64 : $i, X65 : $i, X66 : $i]:
% 8.73/9.00         (((k2_relset_1 @ X65 @ X64 @ X66) != (X64))
% 8.73/9.00          | ~ (v2_funct_1 @ X66)
% 8.73/9.00          | ((k2_tops_2 @ X65 @ X64 @ X66) = (k2_funct_1 @ X66))
% 8.73/9.00          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X64)))
% 8.73/9.00          | ~ (v1_funct_2 @ X66 @ X65 @ X64)
% 8.73/9.00          | ~ (v1_funct_1 @ X66))),
% 8.73/9.00      inference('cnf', [status(esa)], [d4_tops_2])).
% 8.73/9.00  thf('243', plain,
% 8.73/9.00      ((~ (v1_funct_1 @ sk_C_1)
% 8.73/9.00        | ~ (v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.73/9.00        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 8.73/9.00            = (k2_funct_1 @ sk_C_1))
% 8.73/9.00        | ~ (v2_funct_1 @ sk_C_1)
% 8.73/9.00        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 8.73/9.00            != (u1_struct_0 @ sk_B)))),
% 8.73/9.00      inference('sup-', [status(thm)], ['241', '242'])).
% 8.73/9.00  thf('244', plain, ((v1_funct_1 @ sk_C_1)),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('245', plain,
% 8.73/9.00      ((v1_funct_2 @ sk_C_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 8.73/9.00      inference('demod', [status(thm)], ['25', '26'])).
% 8.73/9.00  thf('246', plain, ((v2_funct_1 @ sk_C_1)),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('247', plain,
% 8.73/9.00      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 8.73/9.00         = (k2_struct_0 @ sk_B))),
% 8.73/9.00      inference('demod', [status(thm)], ['15', '16'])).
% 8.73/9.00  thf('248', plain,
% 8.73/9.00      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 8.73/9.00          = (k2_funct_1 @ sk_C_1))
% 8.73/9.00        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 8.73/9.00      inference('demod', [status(thm)], ['243', '244', '245', '246', '247'])).
% 8.73/9.00  thf('249', plain,
% 8.73/9.00      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 8.73/9.00        | ~ (l1_struct_0 @ sk_B)
% 8.73/9.00        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 8.73/9.00            = (k2_funct_1 @ sk_C_1)))),
% 8.73/9.00      inference('sup-', [status(thm)], ['240', '248'])).
% 8.73/9.00  thf('250', plain, ((l1_struct_0 @ sk_B)),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('251', plain,
% 8.73/9.00      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 8.73/9.00        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 8.73/9.00            = (k2_funct_1 @ sk_C_1)))),
% 8.73/9.00      inference('demod', [status(thm)], ['249', '250'])).
% 8.73/9.00  thf('252', plain,
% 8.73/9.00      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1)
% 8.73/9.00         = (k2_funct_1 @ sk_C_1))),
% 8.73/9.00      inference('simplify', [status(thm)], ['251'])).
% 8.73/9.00  thf('253', plain,
% 8.73/9.00      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 8.73/9.00          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 8.73/9.00           (k2_funct_1 @ sk_C_1)) @ 
% 8.73/9.00          sk_C_1)),
% 8.73/9.00      inference('demod', [status(thm)], ['218', '239', '252'])).
% 8.73/9.00  thf('254', plain,
% 8.73/9.00      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 8.73/9.00           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 8.73/9.00            (k2_funct_1 @ sk_C_1)) @ 
% 8.73/9.00           sk_C_1)
% 8.73/9.00        | ~ (l1_struct_0 @ sk_B))),
% 8.73/9.00      inference('sup-', [status(thm)], ['209', '253'])).
% 8.73/9.00  thf('255', plain, ((l1_struct_0 @ sk_B)),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('256', plain,
% 8.73/9.00      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 8.73/9.00          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 8.73/9.00           (k2_funct_1 @ sk_C_1)) @ 
% 8.73/9.00          sk_C_1)),
% 8.73/9.00      inference('demod', [status(thm)], ['254', '255'])).
% 8.73/9.00  thf(fc6_funct_1, axiom,
% 8.73/9.00    (![A:$i]:
% 8.73/9.00     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 8.73/9.00       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 8.73/9.00         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 8.73/9.00         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 8.73/9.00  thf('257', plain,
% 8.73/9.00      (![X20 : $i]:
% 8.73/9.00         ((v2_funct_1 @ (k2_funct_1 @ X20))
% 8.73/9.00          | ~ (v2_funct_1 @ X20)
% 8.73/9.00          | ~ (v1_funct_1 @ X20)
% 8.73/9.00          | ~ (v1_relat_1 @ X20))),
% 8.73/9.00      inference('cnf', [status(esa)], [fc6_funct_1])).
% 8.73/9.00  thf('258', plain,
% 8.73/9.00      (((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k2_struct_0 @ sk_B))),
% 8.73/9.00      inference('demod', [status(thm)], ['168', '169', '170'])).
% 8.73/9.00  thf('259', plain,
% 8.73/9.00      (![X61 : $i]:
% 8.73/9.00         ((m1_subset_1 @ X61 @ 
% 8.73/9.00           (k1_zfmisc_1 @ 
% 8.73/9.00            (k2_zfmisc_1 @ (k1_relat_1 @ X61) @ (k2_relat_1 @ X61))))
% 8.73/9.00          | ~ (v1_funct_1 @ X61)
% 8.73/9.00          | ~ (v1_relat_1 @ X61))),
% 8.73/9.00      inference('cnf', [status(esa)], [t3_funct_2])).
% 8.73/9.00  thf('260', plain,
% 8.73/9.00      (![X64 : $i, X65 : $i, X66 : $i]:
% 8.73/9.00         (((k2_relset_1 @ X65 @ X64 @ X66) != (X64))
% 8.73/9.00          | ~ (v2_funct_1 @ X66)
% 8.73/9.00          | ((k2_tops_2 @ X65 @ X64 @ X66) = (k2_funct_1 @ X66))
% 8.73/9.00          | ~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X65 @ X64)))
% 8.73/9.00          | ~ (v1_funct_2 @ X66 @ X65 @ X64)
% 8.73/9.00          | ~ (v1_funct_1 @ X66))),
% 8.73/9.00      inference('cnf', [status(esa)], [d4_tops_2])).
% 8.73/9.00  thf('261', plain,
% 8.73/9.00      (![X0 : $i]:
% 8.73/9.00         (~ (v1_relat_1 @ X0)
% 8.73/9.00          | ~ (v1_funct_1 @ X0)
% 8.73/9.00          | ~ (v1_funct_1 @ X0)
% 8.73/9.00          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 8.73/9.00          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 8.73/9.00              = (k2_funct_1 @ X0))
% 8.73/9.00          | ~ (v2_funct_1 @ X0)
% 8.73/9.00          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 8.73/9.00              != (k2_relat_1 @ X0)))),
% 8.73/9.00      inference('sup-', [status(thm)], ['259', '260'])).
% 8.73/9.00  thf('262', plain,
% 8.73/9.00      (![X0 : $i]:
% 8.73/9.00         (((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 8.73/9.00            != (k2_relat_1 @ X0))
% 8.73/9.00          | ~ (v2_funct_1 @ X0)
% 8.73/9.00          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 8.73/9.00              = (k2_funct_1 @ X0))
% 8.73/9.00          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 8.73/9.00          | ~ (v1_funct_1 @ X0)
% 8.73/9.00          | ~ (v1_relat_1 @ X0))),
% 8.73/9.00      inference('simplify', [status(thm)], ['261'])).
% 8.73/9.00  thf('263', plain,
% 8.73/9.00      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B) @ 
% 8.73/9.00           (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))
% 8.73/9.00        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/9.00        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/9.00        | ((k2_tops_2 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ 
% 8.73/9.00            (k2_relat_1 @ (k2_funct_1 @ sk_C_1)) @ (k2_funct_1 @ sk_C_1))
% 8.73/9.00            = (k2_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 8.73/9.00        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/9.00        | ((k2_relset_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C_1)) @ 
% 8.73/9.00            (k2_relat_1 @ (k2_funct_1 @ sk_C_1)) @ (k2_funct_1 @ sk_C_1))
% 8.73/9.00            != (k2_relat_1 @ (k2_funct_1 @ sk_C_1))))),
% 8.73/9.00      inference('sup-', [status(thm)], ['258', '262'])).
% 8.73/9.00  thf('264', plain,
% 8.73/9.00      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 8.73/9.00      inference('demod', [status(thm)], ['174', '175', '176'])).
% 8.73/9.00  thf('265', plain,
% 8.73/9.00      ((v1_funct_2 @ (k2_funct_1 @ sk_C_1) @ (k2_struct_0 @ sk_B) @ 
% 8.73/9.00        (k2_struct_0 @ sk_A))),
% 8.73/9.00      inference('simplify', [status(thm)], ['117'])).
% 8.73/9.00  thf('266', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C_1))),
% 8.73/9.00      inference('sup-', [status(thm)], ['46', '47'])).
% 8.73/9.00  thf('267', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C_1))),
% 8.73/9.00      inference('simplify', [status(thm)], ['56'])).
% 8.73/9.00  thf('268', plain,
% 8.73/9.00      (((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k2_struct_0 @ sk_B))),
% 8.73/9.00      inference('demod', [status(thm)], ['168', '169', '170'])).
% 8.73/9.00  thf('269', plain,
% 8.73/9.00      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 8.73/9.00      inference('demod', [status(thm)], ['174', '175', '176'])).
% 8.73/9.00  thf('270', plain,
% 8.73/9.00      (((k1_relat_1 @ (k2_funct_1 @ sk_C_1)) = (k2_struct_0 @ sk_B))),
% 8.73/9.00      inference('demod', [status(thm)], ['168', '169', '170'])).
% 8.73/9.00  thf('271', plain,
% 8.73/9.00      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 8.73/9.00      inference('demod', [status(thm)], ['174', '175', '176'])).
% 8.73/9.00  thf('272', plain,
% 8.73/9.00      ((m1_subset_1 @ (k2_funct_1 @ sk_C_1) @ 
% 8.73/9.00        (k1_zfmisc_1 @ 
% 8.73/9.00         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 8.73/9.00      inference('simplify', [status(thm)], ['45'])).
% 8.73/9.00  thf('273', plain,
% 8.73/9.00      (![X34 : $i, X35 : $i, X36 : $i]:
% 8.73/9.00         (((k2_relset_1 @ X35 @ X36 @ X34) = (k2_relat_1 @ X34))
% 8.73/9.00          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 8.73/9.00      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 8.73/9.00  thf('274', plain,
% 8.73/9.00      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 8.73/9.00         (k2_funct_1 @ sk_C_1)) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 8.73/9.00      inference('sup-', [status(thm)], ['272', '273'])).
% 8.73/9.00  thf('275', plain,
% 8.73/9.00      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 8.73/9.00      inference('demod', [status(thm)], ['174', '175', '176'])).
% 8.73/9.00  thf('276', plain,
% 8.73/9.00      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 8.73/9.00         (k2_funct_1 @ sk_C_1)) = (k2_struct_0 @ sk_A))),
% 8.73/9.00      inference('demod', [status(thm)], ['274', '275'])).
% 8.73/9.00  thf('277', plain,
% 8.73/9.00      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C_1)))),
% 8.73/9.00      inference('demod', [status(thm)], ['174', '175', '176'])).
% 8.73/9.00  thf('278', plain,
% 8.73/9.00      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 8.73/9.00          (k2_funct_1 @ sk_C_1)) = (k2_funct_1 @ (k2_funct_1 @ sk_C_1)))
% 8.73/9.00        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/9.00        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 8.73/9.00      inference('demod', [status(thm)],
% 8.73/9.00                ['263', '264', '265', '266', '267', '268', '269', '270', 
% 8.73/9.00                 '271', '276', '277'])).
% 8.73/9.00  thf('279', plain,
% 8.73/9.00      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C_1))
% 8.73/9.00        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 8.73/9.00            (k2_funct_1 @ sk_C_1)) = (k2_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 8.73/9.00      inference('simplify', [status(thm)], ['278'])).
% 8.73/9.00  thf('280', plain,
% 8.73/9.00      ((~ (v1_relat_1 @ sk_C_1)
% 8.73/9.00        | ~ (v1_funct_1 @ sk_C_1)
% 8.73/9.00        | ~ (v2_funct_1 @ sk_C_1)
% 8.73/9.00        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 8.73/9.00            (k2_funct_1 @ sk_C_1)) = (k2_funct_1 @ (k2_funct_1 @ sk_C_1))))),
% 8.73/9.00      inference('sup-', [status(thm)], ['257', '279'])).
% 8.73/9.00  thf('281', plain, ((v1_relat_1 @ sk_C_1)),
% 8.73/9.00      inference('demod', [status(thm)], ['68', '69'])).
% 8.73/9.00  thf('282', plain, ((v1_funct_1 @ sk_C_1)),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('283', plain, ((v2_funct_1 @ sk_C_1)),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('284', plain,
% 8.73/9.00      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 8.73/9.00         (k2_funct_1 @ sk_C_1)) = (k2_funct_1 @ (k2_funct_1 @ sk_C_1)))),
% 8.73/9.00      inference('demod', [status(thm)], ['280', '281', '282', '283'])).
% 8.73/9.00  thf('285', plain,
% 8.73/9.00      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 8.73/9.00          (k2_funct_1 @ (k2_funct_1 @ sk_C_1)) @ sk_C_1)),
% 8.73/9.00      inference('demod', [status(thm)], ['256', '284'])).
% 8.73/9.00  thf('286', plain,
% 8.73/9.00      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 8.73/9.00           sk_C_1)
% 8.73/9.00        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 8.73/9.00      inference('sup-', [status(thm)], ['208', '285'])).
% 8.73/9.00  thf(rc1_funct_2, axiom,
% 8.73/9.00    (![A:$i,B:$i]:
% 8.73/9.00     ( ?[C:$i]:
% 8.73/9.00       ( ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) & 
% 8.73/9.00         ( v5_relat_1 @ C @ B ) & ( v4_relat_1 @ C @ A ) & 
% 8.73/9.00         ( v1_relat_1 @ C ) & 
% 8.73/9.00         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 8.73/9.00  thf('287', plain,
% 8.73/9.00      (![X45 : $i, X46 : $i]:
% 8.73/9.00         (m1_subset_1 @ (sk_C @ X45 @ X46) @ 
% 8.73/9.00          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))),
% 8.73/9.00      inference('cnf', [status(esa)], [rc1_funct_2])).
% 8.73/9.00  thf('288', plain,
% 8.73/9.00      ((m1_subset_1 @ sk_C_1 @ 
% 8.73/9.00        (k1_zfmisc_1 @ 
% 8.73/9.00         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf(reflexivity_r2_funct_2, axiom,
% 8.73/9.00    (![A:$i,B:$i,C:$i,D:$i]:
% 8.73/9.00     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.73/9.00         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 8.73/9.00         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 8.73/9.00         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.73/9.00       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 8.73/9.00  thf('289', plain,
% 8.73/9.00      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 8.73/9.00         ((r2_funct_2 @ X48 @ X49 @ X50 @ X50)
% 8.73/9.00          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 8.73/9.00          | ~ (v1_funct_2 @ X50 @ X48 @ X49)
% 8.73/9.00          | ~ (v1_funct_1 @ X50)
% 8.73/9.00          | ~ (v1_funct_1 @ X51)
% 8.73/9.00          | ~ (v1_funct_2 @ X51 @ X48 @ X49)
% 8.73/9.00          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49))))),
% 8.73/9.00      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 8.73/9.00  thf('290', plain,
% 8.73/9.00      (![X0 : $i]:
% 8.73/9.00         (~ (m1_subset_1 @ X0 @ 
% 8.73/9.00             (k1_zfmisc_1 @ 
% 8.73/9.00              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 8.73/9.00          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.73/9.00          | ~ (v1_funct_1 @ X0)
% 8.73/9.00          | ~ (v1_funct_1 @ sk_C_1)
% 8.73/9.00          | ~ (v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ 
% 8.73/9.00               (u1_struct_0 @ sk_B))
% 8.73/9.00          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 8.73/9.00             sk_C_1 @ sk_C_1))),
% 8.73/9.00      inference('sup-', [status(thm)], ['288', '289'])).
% 8.73/9.00  thf('291', plain, ((v1_funct_1 @ sk_C_1)),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('292', plain,
% 8.73/9.00      ((v1_funct_2 @ sk_C_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('293', plain,
% 8.73/9.00      (![X0 : $i]:
% 8.73/9.00         (~ (m1_subset_1 @ X0 @ 
% 8.73/9.00             (k1_zfmisc_1 @ 
% 8.73/9.00              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 8.73/9.00          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.73/9.00          | ~ (v1_funct_1 @ X0)
% 8.73/9.00          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 8.73/9.00             sk_C_1 @ sk_C_1))),
% 8.73/9.00      inference('demod', [status(thm)], ['290', '291', '292'])).
% 8.73/9.00  thf('294', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 8.73/9.00      inference('clc', [status(thm)], ['237', '238'])).
% 8.73/9.00  thf('295', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 8.73/9.00      inference('clc', [status(thm)], ['237', '238'])).
% 8.73/9.00  thf('296', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 8.73/9.00      inference('clc', [status(thm)], ['237', '238'])).
% 8.73/9.00  thf('297', plain,
% 8.73/9.00      (![X0 : $i]:
% 8.73/9.00         (~ (m1_subset_1 @ X0 @ 
% 8.73/9.00             (k1_zfmisc_1 @ 
% 8.73/9.00              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 8.73/9.00          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 8.73/9.00          | ~ (v1_funct_1 @ X0)
% 8.73/9.00          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 8.73/9.00             sk_C_1 @ sk_C_1))),
% 8.73/9.00      inference('demod', [status(thm)], ['293', '294', '295', '296'])).
% 8.73/9.00  thf('298', plain,
% 8.73/9.00      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 8.73/9.00         sk_C_1)
% 8.73/9.00        | ~ (v1_funct_1 @ (sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))
% 8.73/9.00        | ~ (v1_funct_2 @ 
% 8.73/9.00             (sk_C @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)) @ 
% 8.73/9.00             (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 8.73/9.00      inference('sup-', [status(thm)], ['287', '297'])).
% 8.73/9.00  thf('299', plain, (![X45 : $i, X46 : $i]: (v1_funct_1 @ (sk_C @ X45 @ X46))),
% 8.73/9.00      inference('cnf', [status(esa)], [rc1_funct_2])).
% 8.73/9.00  thf('300', plain,
% 8.73/9.00      (![X45 : $i, X46 : $i]: (v1_funct_2 @ (sk_C @ X45 @ X46) @ X46 @ X45)),
% 8.73/9.00      inference('cnf', [status(esa)], [rc1_funct_2])).
% 8.73/9.00  thf('301', plain,
% 8.73/9.00      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C_1 @ 
% 8.73/9.00        sk_C_1)),
% 8.73/9.00      inference('demod', [status(thm)], ['298', '299', '300'])).
% 8.73/9.00  thf('302', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 8.73/9.00      inference('demod', [status(thm)], ['286', '301'])).
% 8.73/9.00  thf('303', plain,
% 8.73/9.00      (![X62 : $i]:
% 8.73/9.00         (((k2_struct_0 @ X62) = (u1_struct_0 @ X62)) | ~ (l1_struct_0 @ X62))),
% 8.73/9.00      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.73/9.00  thf('304', plain,
% 8.73/9.00      (![X63 : $i]:
% 8.73/9.00         (~ (v1_xboole_0 @ (u1_struct_0 @ X63))
% 8.73/9.00          | ~ (l1_struct_0 @ X63)
% 8.73/9.00          | (v2_struct_0 @ X63))),
% 8.73/9.00      inference('cnf', [status(esa)], [fc2_struct_0])).
% 8.73/9.00  thf('305', plain,
% 8.73/9.00      (![X0 : $i]:
% 8.73/9.00         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 8.73/9.00          | ~ (l1_struct_0 @ X0)
% 8.73/9.00          | (v2_struct_0 @ X0)
% 8.73/9.00          | ~ (l1_struct_0 @ X0))),
% 8.73/9.00      inference('sup-', [status(thm)], ['303', '304'])).
% 8.73/9.00  thf('306', plain,
% 8.73/9.00      (![X0 : $i]:
% 8.73/9.00         ((v2_struct_0 @ X0)
% 8.73/9.00          | ~ (l1_struct_0 @ X0)
% 8.73/9.00          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 8.73/9.00      inference('simplify', [status(thm)], ['305'])).
% 8.73/9.00  thf('307', plain,
% 8.73/9.00      ((~ (v1_xboole_0 @ k1_xboole_0)
% 8.73/9.00        | ~ (l1_struct_0 @ sk_B)
% 8.73/9.00        | (v2_struct_0 @ sk_B))),
% 8.73/9.00      inference('sup-', [status(thm)], ['302', '306'])).
% 8.73/9.00  thf('308', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 8.73/9.00      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 8.73/9.00  thf('309', plain, ((l1_struct_0 @ sk_B)),
% 8.73/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.73/9.00  thf('310', plain, ((v2_struct_0 @ sk_B)),
% 8.73/9.00      inference('demod', [status(thm)], ['307', '308', '309'])).
% 8.73/9.00  thf('311', plain, ($false), inference('demod', [status(thm)], ['0', '310'])).
% 8.73/9.00  
% 8.73/9.00  % SZS output end Refutation
% 8.73/9.00  
% 8.86/9.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
