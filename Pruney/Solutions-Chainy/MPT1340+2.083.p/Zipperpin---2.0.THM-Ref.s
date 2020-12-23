%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SBwmWlHvFV

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:21 EST 2020

% Result     : Theorem 21.54s
% Output     : Refutation 21.54s
% Verified   : 
% Statistics : Number of formulae       :  544 (1635537 expanded)
%              Number of leaves         :   57 (478863 expanded)
%              Depth                    :   61
%              Number of atoms          : 5231 (34921955 expanded)
%              Number of equality atoms :  239 (1016430 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('4',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

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

thf('16',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( ( k2_relset_1 @ X44 @ X43 @ X45 )
       != X43 )
      | ~ ( v2_funct_1 @ X45 )
      | ( ( k2_tops_2 @ X44 @ X43 @ X45 )
        = ( k2_funct_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('20',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('26',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','18','23','24','29'])).

thf('31',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['10','31'])).

thf('33',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('37',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ C @ A ) ) ) ) )).

thf('39',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X33 ) ) )
      | ( v1_partfun1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X33 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('40',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X35 @ X33 )
      | ( v1_partfun1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('45',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_partfun1 @ X28 @ X27 )
      | ( ( k1_relat_1 @ X28 )
        = X27 )
      | ~ ( v4_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('46',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('48',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('50',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('53',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('54',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','51','54'])).

thf('56',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['37','55'])).

thf('57',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('60',plain,(
    ! [X42: $i] :
      ( ( ( k2_struct_0 @ X42 )
        = ( u1_struct_0 @ X42 ) )
      | ~ ( l1_struct_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['59','64'])).

thf('66',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['30'])).

thf('69',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','69'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('71',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('72',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('73',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

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

thf('75',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v2_funct_1 @ X36 )
      | ( ( k2_relset_1 @ X38 @ X37 @ X36 )
       != X37 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('76',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('79',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('80',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('86',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('88',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('89',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('90',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
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

thf('91',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X11 ) @ X11 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

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

thf('92',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X8 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
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
    inference('sup-',[status(thm)],['91','92'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('94',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('95',plain,(
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
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
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
    inference('sup-',[status(thm)],['90','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['89','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
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
    inference('sup-',[status(thm)],['88','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('104',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('105',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('107',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('108',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('109',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('110',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('111',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('112',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('113',plain,(
    ! [X39: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X39 ) @ ( k2_relat_1 @ X39 ) ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('114',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k1_relat_1 @ X28 )
       != X27 )
      | ( v1_partfun1 @ X28 @ X27 )
      | ~ ( v4_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('117',plain,(
    ! [X28: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v4_relat_1 @ X28 @ ( k1_relat_1 @ X28 ) )
      | ( v1_partfun1 @ X28 @ ( k1_relat_1 @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['112','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['111','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['110','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['109','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['108','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['106','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['105','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['104','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['103','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['102','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','138'])).

thf('140',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['86','139'])).

thf('141',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('143',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('144',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v2_funct_1 @ X36 )
      | ( ( k2_relset_1 @ X38 @ X37 @ X36 )
       != X37 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('145',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('148',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('149',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['145','146','147','148','149'])).

thf('151',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('154',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('155',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('156',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('157',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X11 ) @ X11 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['156','157'])).

thf('159',plain,(
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
    inference('sup-',[status(thm)],['155','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['154','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['153','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['152','166'])).

thf('168',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( v2_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['151','167'])).

thf('169',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('170',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('173',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['168','169','170','171','172'])).

thf('174',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['142','173'])).

thf('175',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('176',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v2_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['174','175','176','177'])).

thf('179',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( v2_funct_1 @ X8 )
      | ( ( k2_relat_1 @ X8 )
       != ( k1_relat_1 @ X9 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('180',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('182',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['150'])).

thf('184',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('185',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['180','181','182','183','184'])).

thf('186',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['141','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('188',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['186','187','188','189'])).

thf('191',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['150'])).

thf('193',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('196',plain,(
    v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['140','191','192','193','194','195'])).

thf('197',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['73','196'])).

thf('198',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('199',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['150'])).

thf('200',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['190'])).

thf('201',plain,(
    v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['197','198','199','200'])).

thf('202',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_partfun1 @ X28 @ X27 )
      | ( ( k1_relat_1 @ X28 )
        = X27 )
      | ~ ( v4_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('203',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('205',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('206',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('208',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('209',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('210',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('212',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('213',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('214',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('215',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('216',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('217',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('218',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['216','219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['220'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['215','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['222'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['214','223'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['213','224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['212','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['227'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['211','228'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['210','230'])).

thf('232',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['209','231'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['208','233'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['207','235'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['206','237'])).

thf('239',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['205','238'])).

thf('240',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['190'])).

thf('241',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['150'])).

thf('242',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('245',plain,(
    v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['239','240','241','242','243','244'])).

thf('246',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['204','245'])).

thf('247',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('248',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['150'])).

thf('249',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['190'])).

thf('250',plain,(
    v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['246','247','248','249'])).

thf('251',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['203','250'])).

thf('252',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['72','251'])).

thf('253',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('254',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['150'])).

thf('255',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['252','253','254'])).

thf('256',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['71','255'])).

thf('257',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('258',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['150'])).

thf('259',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['190'])).

thf('260',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['256','257','258','259'])).

thf('261',plain,(
    ! [X39: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X39 ) @ ( k2_relat_1 @ X39 ) ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('262',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('263',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['261','262'])).

thf('264',plain,(
    ! [X39: $i] :
      ( ( v1_funct_2 @ X39 @ ( k1_relat_1 @ X39 ) @ ( k2_relat_1 @ X39 ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('265',plain,(
    ! [X39: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X39 ) @ ( k2_relat_1 @ X39 ) ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('266',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( ( k2_relset_1 @ X44 @ X43 @ X45 )
       != X43 )
      | ~ ( v2_funct_1 @ X45 )
      | ( ( k2_tops_2 @ X44 @ X43 @ X45 )
        = ( k2_funct_1 @ X45 ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X43 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('267',plain,(
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
    inference('sup-',[status(thm)],['265','266'])).

thf('268',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['267'])).

thf('269',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['264','268'])).

thf('270',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['269'])).

thf('271',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['263','270'])).

thf('272',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['271'])).

thf('273',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['260','272'])).

thf('274',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('275',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('277',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['275','276'])).

thf('278',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['277','278'])).

thf('280',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('281',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['279','280'])).

thf('282',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('283',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['281','282','283','284'])).

thf('286',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_partfun1 @ X28 @ X27 )
      | ( ( k1_relat_1 @ X28 )
        = X27 )
      | ~ ( v4_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('287',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['285','286'])).

thf('288',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['277','278'])).

thf('289',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['222'])).

thf('290',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['288','289'])).

thf('291',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('292',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('293',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['290','291','292','293'])).

thf('295',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['287','294'])).

thf('296',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['274','295'])).

thf('297',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('298',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['296','297','298'])).

thf('300',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['150'])).

thf('301',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('302',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['190'])).

thf('303',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['273','299','300','301','302'])).

thf('304',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','303'])).

thf('305',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','304'])).

thf('306',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('307',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( r2_funct_2 @ X30 @ X31 @ X29 @ X32 )
      | ( X29 != X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('308',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_funct_2 @ X30 @ X31 @ X32 @ X32 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(simplify,[status(thm)],['307'])).

thf('309',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['306','308'])).

thf('310',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('312',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['309','310','311'])).

thf('313',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('314',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('316',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['305','312','313','314','315'])).

thf('317',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['305','312','313','314','315'])).

thf('318',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ ( k2_tops_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['35','316','317'])).

thf('319',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X12 ) )
        = X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('320',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['277','278'])).

thf('321',plain,(
    ! [X39: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X39 ) @ ( k2_relat_1 @ X39 ) ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('322',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['320','321'])).

thf('323',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('324',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['322','323','324'])).

thf('326',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['305','312','313','314','315'])).

thf('327',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['325','326'])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('328',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24 != k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X26 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('329',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X25 @ k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['328'])).

thf('330',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['327','329'])).

thf('331',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['277','278'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('332',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X40 ) @ X41 )
      | ( v1_funct_2 @ X40 @ ( k1_relat_1 @ X40 ) @ X41 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('333',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['331','332'])).

thf('334',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('335',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('336',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ X0 )
      | ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['333','334','335'])).

thf('337',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['305','312','313','314','315'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('338',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('339',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ X0 ) ),
    inference(demod,[status(thm)],['336','337','338'])).

thf('340',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['330','339'])).

thf('341',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['273','299','300','301','302'])).

thf('342',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['305','312','313','314','315'])).

thf('343',plain,
    ( ( k2_tops_2 @ k1_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['341','342'])).

thf('344',plain,
    ( ( ( k2_tops_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['340','343'])).

thf('345',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('346',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['305','312','313','314','315'])).

thf('347',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['345','346'])).

thf('348',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X25 @ k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['328'])).

thf('349',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['347','348'])).

thf('350',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('351',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['305','312','313','314','315'])).

thf('352',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['350','351'])).

thf('353',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['349','352'])).

thf('354',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('355',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['305','312','313','314','315'])).

thf('356',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['354','355'])).

thf('357',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['353','356'])).

thf('358',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ( sk_C = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['344','357'])).

thf('359',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(simplify,[status(thm)],['358'])).

thf('360',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['319','359'])).

thf('361',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['309','310','311'])).

thf('362',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('363',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('364',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('365',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['360','361','362','363','364'])).

thf('366',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['360','361','362','363','364'])).

thf('367',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ ( k2_tops_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['318','365','366'])).

thf('368',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf(dt_k2_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A )
        & ( m1_subset_1 @ ( k2_tops_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) )).

thf('369',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( m1_subset_1 @ ( k2_tops_2 @ X46 @ X47 @ X48 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X46 @ X47 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('370',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['368','369'])).

thf('371',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['150'])).

thf('372',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('373',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v2_funct_1 @ X36 )
      | ( ( k2_relset_1 @ X38 @ X37 @ X36 )
       != X37 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X36 ) @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('374',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['372','373'])).

thf('375',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('376',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('377',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('378',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('379',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['374','375','376','377','378'])).

thf('380',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['379'])).

thf('381',plain,(
    m1_subset_1 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['370','371','380'])).

thf('382',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['305','312','313','314','315'])).

thf('383',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['360','361','362','363','364'])).

thf('384',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['305','312','313','314','315'])).

thf('385',plain,(
    m1_subset_1 @ ( k2_tops_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ k1_xboole_0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['381','382','383','384'])).

thf('386',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X25 @ k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['328'])).

thf('387',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_tops_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ k1_xboole_0 ) )
      = k1_xboole_0 )
    | ~ ( v1_funct_2 @ ( k2_tops_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ k1_xboole_0 ) ) @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['385','386'])).

thf('388',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('389',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( v1_funct_2 @ ( k2_tops_2 @ X46 @ X47 @ X48 ) @ X47 @ X46 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X46 @ X47 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_2])).

thf('390',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_funct_2 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['388','389'])).

thf('391',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['150'])).

thf('392',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['379'])).

thf('393',plain,(
    v1_funct_2 @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['390','391','392'])).

thf('394',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['305','312','313','314','315'])).

thf('395',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['360','361','362','363','364'])).

thf('396',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['305','312','313','314','315'])).

thf('397',plain,(
    v1_funct_2 @ ( k2_tops_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ k1_xboole_0 ) ) @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['393','394','395','396'])).

thf('398',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_tops_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['387','397'])).

thf('399',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ ( k2_tops_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['318','365','366'])).

thf('400',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['398','399'])).

thf('401',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('402',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_funct_2 @ X30 @ X31 @ X32 @ X32 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(simplify,[status(thm)],['307'])).

thf('403',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['401','402'])).

thf('404',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('405',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('406',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['403','404','405'])).

thf('407',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['305','312','313','314','315'])).

thf('408',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['406','407'])).

thf('409',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['360','361','362','363','364'])).

thf('410',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['360','361','362','363','364'])).

thf('411',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['408','409','410'])).

thf('412',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['400','411'])).

thf('413',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['400','411'])).

thf('414',plain,(
    ~ ( r2_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_tops_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_funct_1 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['367','412','413'])).

thf('415',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['296','297','298'])).

thf('416',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['305','312','313','314','315'])).

thf('417',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['415','416'])).

thf('418',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['271'])).

thf('419',plain,
    ( ( ( k2_tops_2 @ k1_xboole_0 @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['417','418'])).

thf('420',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['256','257','258','259'])).

thf('421',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['150'])).

thf('422',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('423',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['190'])).

thf('424',plain,
    ( ( k2_tops_2 @ k1_xboole_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['419','420','421','422','423'])).

thf('425',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['360','361','362','363','364'])).

thf('426',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['360','361','362','363','364'])).

thf('427',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['360','361','362','363','364'])).

thf('428',plain,
    ( ( k2_tops_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k2_funct_1 @ k1_xboole_0 ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['424','425','426','427'])).

thf('429',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['345','346'])).

thf('430',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['360','361','362','363','364'])).

thf('431',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['429','430'])).

thf('432',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['400','411'])).

thf('433',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['431','432'])).

thf('434',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X35 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X33 ) ) )
      | ( v1_partfun1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X33 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('435',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ k1_xboole_0 @ X33 )
      | ( v1_partfun1 @ X34 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(simplify,[status(thm)],['434'])).

thf('436',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['433','435'])).

thf('437',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('438',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['360','361','362','363','364'])).

thf('439',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['437','438'])).

thf('440',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['350','351'])).

thf('441',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['360','361','362','363','364'])).

thf('442',plain,(
    v1_funct_2 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['440','441'])).

thf('443',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['400','411'])).

thf('444',plain,(
    v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['442','443'])).

thf('445',plain,(
    v1_partfun1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['436','439','444'])).

thf('446',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_partfun1 @ X28 @ X27 )
      | ( ( k1_relat_1 @ X28 )
        = X27 )
      | ~ ( v4_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('447',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['445','446'])).

thf('448',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('449',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['360','361','362','363','364'])).

thf('450',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['448','449'])).

thf('451',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('452',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['360','361','362','363','364'])).

thf('453',plain,(
    v4_relat_1 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['451','452'])).

thf('454',plain,
    ( ( u1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['400','411'])).

thf('455',plain,(
    v4_relat_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['453','454'])).

thf('456',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['447','450','455'])).

thf('457',plain,
    ( ( k2_tops_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_funct_1 @ k1_xboole_0 ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['428','456'])).

thf('458',plain,(
    ~ ( r2_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ ( k2_funct_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['414','457'])).

thf('459',plain,
    ( ~ ( r2_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v2_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','458'])).

thf('460',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['277','278'])).

thf('461',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X40 ) @ X41 )
      | ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X40 ) @ X41 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('462',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['460','461'])).

thf('463',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('464',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('465',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_B ) @ X0 )
      | ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['462','463','464'])).

thf('466',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['305','312','313','314','315'])).

thf('467',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('468',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['465','466','467'])).

thf('469',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_funct_2 @ X30 @ X31 @ X32 @ X32 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(simplify,[status(thm)],['307'])).

thf('470',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ X0 @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['468','469'])).

thf('471',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ X0 ) ),
    inference(demod,[status(thm)],['336','337','338'])).

thf('472',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('473',plain,(
    ! [X0: $i] :
      ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ X0 @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['470','471','472'])).

thf('474',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['360','361','362','363','364'])).

thf('475',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['360','361','362','363','364'])).

thf('476',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['360','361','362','363','364'])).

thf('477',plain,(
    ! [X0: $i] :
      ( r2_funct_2 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['473','474','475','476'])).

thf('478',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['447','450','455'])).

thf('479',plain,(
    ! [X0: $i] :
      ( r2_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['477','478'])).

thf('480',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['448','449'])).

thf('481',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['437','438'])).

thf('482',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('483',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['360','361','362','363','364'])).

thf('484',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['482','483'])).

thf('485',plain,(
    $false ),
    inference(demod,[status(thm)],['459','479','480','481','484'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SBwmWlHvFV
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:43:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 21.54/21.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 21.54/21.75  % Solved by: fo/fo7.sh
% 21.54/21.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 21.54/21.75  % done 8543 iterations in 21.281s
% 21.54/21.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 21.54/21.75  % SZS output start Refutation
% 21.54/21.75  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 21.54/21.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 21.54/21.75  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 21.54/21.75  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 21.54/21.75  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 21.54/21.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 21.54/21.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 21.54/21.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 21.54/21.75  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 21.54/21.75  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 21.54/21.75  thf(sk_B_type, type, sk_B: $i).
% 21.54/21.75  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 21.54/21.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 21.54/21.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 21.54/21.75  thf(sk_A_type, type, sk_A: $i).
% 21.54/21.75  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 21.54/21.75  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 21.54/21.75  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 21.54/21.75  thf(sk_C_type, type, sk_C: $i).
% 21.54/21.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 21.54/21.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 21.54/21.75  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 21.54/21.75  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 21.54/21.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 21.54/21.75  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 21.54/21.75  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 21.54/21.75  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 21.54/21.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 21.54/21.75  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 21.54/21.75  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 21.54/21.75  thf(t65_funct_1, axiom,
% 21.54/21.75    (![A:$i]:
% 21.54/21.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 21.54/21.75       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 21.54/21.75  thf('0', plain,
% 21.54/21.75      (![X12 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X12)
% 21.54/21.75          | ((k2_funct_1 @ (k2_funct_1 @ X12)) = (X12))
% 21.54/21.75          | ~ (v1_funct_1 @ X12)
% 21.54/21.75          | ~ (v1_relat_1 @ X12))),
% 21.54/21.75      inference('cnf', [status(esa)], [t65_funct_1])).
% 21.54/21.75  thf(d3_struct_0, axiom,
% 21.54/21.75    (![A:$i]:
% 21.54/21.75     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 21.54/21.75  thf('1', plain,
% 21.54/21.75      (![X42 : $i]:
% 21.54/21.75         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 21.54/21.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 21.54/21.75  thf('2', plain,
% 21.54/21.75      (![X42 : $i]:
% 21.54/21.75         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 21.54/21.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 21.54/21.75  thf('3', plain,
% 21.54/21.75      (![X42 : $i]:
% 21.54/21.75         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 21.54/21.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 21.54/21.75  thf(t64_tops_2, conjecture,
% 21.54/21.75    (![A:$i]:
% 21.54/21.75     ( ( l1_struct_0 @ A ) =>
% 21.54/21.75       ( ![B:$i]:
% 21.54/21.75         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 21.54/21.75           ( ![C:$i]:
% 21.54/21.75             ( ( ( v1_funct_1 @ C ) & 
% 21.54/21.75                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 21.54/21.75                 ( m1_subset_1 @
% 21.54/21.75                   C @ 
% 21.54/21.75                   ( k1_zfmisc_1 @
% 21.54/21.75                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 21.54/21.75               ( ( ( ( k2_relset_1 @
% 21.54/21.75                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 21.54/21.75                     ( k2_struct_0 @ B ) ) & 
% 21.54/21.75                   ( v2_funct_1 @ C ) ) =>
% 21.54/21.75                 ( r2_funct_2 @
% 21.54/21.75                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 21.54/21.75                   ( k2_tops_2 @
% 21.54/21.75                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 21.54/21.75                     ( k2_tops_2 @
% 21.54/21.75                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 21.54/21.75                   C ) ) ) ) ) ) ))).
% 21.54/21.75  thf(zf_stmt_0, negated_conjecture,
% 21.54/21.75    (~( ![A:$i]:
% 21.54/21.75        ( ( l1_struct_0 @ A ) =>
% 21.54/21.75          ( ![B:$i]:
% 21.54/21.75            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 21.54/21.75              ( ![C:$i]:
% 21.54/21.75                ( ( ( v1_funct_1 @ C ) & 
% 21.54/21.75                    ( v1_funct_2 @
% 21.54/21.75                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 21.54/21.75                    ( m1_subset_1 @
% 21.54/21.75                      C @ 
% 21.54/21.75                      ( k1_zfmisc_1 @
% 21.54/21.75                        ( k2_zfmisc_1 @
% 21.54/21.75                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 21.54/21.75                  ( ( ( ( k2_relset_1 @
% 21.54/21.75                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 21.54/21.75                        ( k2_struct_0 @ B ) ) & 
% 21.54/21.75                      ( v2_funct_1 @ C ) ) =>
% 21.54/21.75                    ( r2_funct_2 @
% 21.54/21.75                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 21.54/21.75                      ( k2_tops_2 @
% 21.54/21.75                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 21.54/21.75                        ( k2_tops_2 @
% 21.54/21.75                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 21.54/21.75                      C ) ) ) ) ) ) ) )),
% 21.54/21.75    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 21.54/21.75  thf('4', plain,
% 21.54/21.75      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 21.54/21.75          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 21.54/21.75          sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('5', plain,
% 21.54/21.75      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 21.54/21.75           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 21.54/21.75           sk_C)
% 21.54/21.75        | ~ (l1_struct_0 @ sk_B))),
% 21.54/21.75      inference('sup-', [status(thm)], ['3', '4'])).
% 21.54/21.75  thf('6', plain, ((l1_struct_0 @ sk_B)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('7', plain,
% 21.54/21.75      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 21.54/21.75          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 21.54/21.75          sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['5', '6'])).
% 21.54/21.75  thf('8', plain,
% 21.54/21.75      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 21.54/21.75           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 21.54/21.75           sk_C)
% 21.54/21.75        | ~ (l1_struct_0 @ sk_B))),
% 21.54/21.75      inference('sup-', [status(thm)], ['2', '7'])).
% 21.54/21.75  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('10', plain,
% 21.54/21.75      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 21.54/21.75          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 21.54/21.75          sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['8', '9'])).
% 21.54/21.75  thf('11', plain,
% 21.54/21.75      (![X42 : $i]:
% 21.54/21.75         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 21.54/21.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 21.54/21.75  thf('12', plain,
% 21.54/21.75      ((m1_subset_1 @ sk_C @ 
% 21.54/21.75        (k1_zfmisc_1 @ 
% 21.54/21.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('13', plain,
% 21.54/21.75      (((m1_subset_1 @ sk_C @ 
% 21.54/21.75         (k1_zfmisc_1 @ 
% 21.54/21.75          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 21.54/21.75        | ~ (l1_struct_0 @ sk_B))),
% 21.54/21.75      inference('sup+', [status(thm)], ['11', '12'])).
% 21.54/21.75  thf('14', plain, ((l1_struct_0 @ sk_B)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('15', plain,
% 21.54/21.75      ((m1_subset_1 @ sk_C @ 
% 21.54/21.75        (k1_zfmisc_1 @ 
% 21.54/21.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 21.54/21.75      inference('demod', [status(thm)], ['13', '14'])).
% 21.54/21.75  thf(d4_tops_2, axiom,
% 21.54/21.75    (![A:$i,B:$i,C:$i]:
% 21.54/21.75     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 21.54/21.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.54/21.75       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 21.54/21.75         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 21.54/21.75  thf('16', plain,
% 21.54/21.75      (![X43 : $i, X44 : $i, X45 : $i]:
% 21.54/21.75         (((k2_relset_1 @ X44 @ X43 @ X45) != (X43))
% 21.54/21.75          | ~ (v2_funct_1 @ X45)
% 21.54/21.75          | ((k2_tops_2 @ X44 @ X43 @ X45) = (k2_funct_1 @ X45))
% 21.54/21.75          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 21.54/21.75          | ~ (v1_funct_2 @ X45 @ X44 @ X43)
% 21.54/21.75          | ~ (v1_funct_1 @ X45))),
% 21.54/21.75      inference('cnf', [status(esa)], [d4_tops_2])).
% 21.54/21.75  thf('17', plain,
% 21.54/21.75      ((~ (v1_funct_1 @ sk_C)
% 21.54/21.75        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 21.54/21.75        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 21.54/21.75            = (k2_funct_1 @ sk_C))
% 21.54/21.75        | ~ (v2_funct_1 @ sk_C)
% 21.54/21.75        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 21.54/21.75            != (k2_struct_0 @ sk_B)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['15', '16'])).
% 21.54/21.75  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('19', plain,
% 21.54/21.75      (![X42 : $i]:
% 21.54/21.75         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 21.54/21.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 21.54/21.75  thf('20', plain,
% 21.54/21.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('21', plain,
% 21.54/21.75      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 21.54/21.75        | ~ (l1_struct_0 @ sk_B))),
% 21.54/21.75      inference('sup+', [status(thm)], ['19', '20'])).
% 21.54/21.75  thf('22', plain, ((l1_struct_0 @ sk_B)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('23', plain,
% 21.54/21.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 21.54/21.75      inference('demod', [status(thm)], ['21', '22'])).
% 21.54/21.75  thf('24', plain, ((v2_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('25', plain,
% 21.54/21.75      (![X42 : $i]:
% 21.54/21.75         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 21.54/21.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 21.54/21.75  thf('26', plain,
% 21.54/21.75      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 21.54/21.75         = (k2_struct_0 @ sk_B))),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('27', plain,
% 21.54/21.75      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 21.54/21.75          = (k2_struct_0 @ sk_B))
% 21.54/21.75        | ~ (l1_struct_0 @ sk_B))),
% 21.54/21.75      inference('sup+', [status(thm)], ['25', '26'])).
% 21.54/21.75  thf('28', plain, ((l1_struct_0 @ sk_B)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('29', plain,
% 21.54/21.75      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 21.54/21.75         = (k2_struct_0 @ sk_B))),
% 21.54/21.75      inference('demod', [status(thm)], ['27', '28'])).
% 21.54/21.75  thf('30', plain,
% 21.54/21.75      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 21.54/21.75          = (k2_funct_1 @ sk_C))
% 21.54/21.75        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 21.54/21.75      inference('demod', [status(thm)], ['17', '18', '23', '24', '29'])).
% 21.54/21.75  thf('31', plain,
% 21.54/21.75      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 21.54/21.75         = (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('simplify', [status(thm)], ['30'])).
% 21.54/21.75  thf('32', plain,
% 21.54/21.75      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 21.54/21.75          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75           (k2_funct_1 @ sk_C)) @ 
% 21.54/21.75          sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['10', '31'])).
% 21.54/21.75  thf('33', plain,
% 21.54/21.75      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 21.54/21.75           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75            (k2_funct_1 @ sk_C)) @ 
% 21.54/21.75           sk_C)
% 21.54/21.75        | ~ (l1_struct_0 @ sk_B))),
% 21.54/21.75      inference('sup-', [status(thm)], ['1', '32'])).
% 21.54/21.75  thf('34', plain, ((l1_struct_0 @ sk_B)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('35', plain,
% 21.54/21.75      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 21.54/21.75          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75           (k2_funct_1 @ sk_C)) @ 
% 21.54/21.75          sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['33', '34'])).
% 21.54/21.75  thf('36', plain,
% 21.54/21.75      (![X12 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X12)
% 21.54/21.75          | ((k2_funct_1 @ (k2_funct_1 @ X12)) = (X12))
% 21.54/21.75          | ~ (v1_funct_1 @ X12)
% 21.54/21.75          | ~ (v1_relat_1 @ X12))),
% 21.54/21.75      inference('cnf', [status(esa)], [t65_funct_1])).
% 21.54/21.75  thf('37', plain,
% 21.54/21.75      (![X42 : $i]:
% 21.54/21.75         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 21.54/21.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 21.54/21.75  thf('38', plain,
% 21.54/21.75      ((m1_subset_1 @ sk_C @ 
% 21.54/21.75        (k1_zfmisc_1 @ 
% 21.54/21.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf(t132_funct_2, axiom,
% 21.54/21.75    (![A:$i,B:$i,C:$i]:
% 21.54/21.75     ( ( ( v1_funct_1 @ C ) & 
% 21.54/21.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.54/21.75       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 21.54/21.75           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.54/21.75         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 21.54/21.75           ( v1_partfun1 @ C @ A ) ) ) ))).
% 21.54/21.75  thf('39', plain,
% 21.54/21.75      (![X33 : $i, X34 : $i, X35 : $i]:
% 21.54/21.75         (((X33) = (k1_xboole_0))
% 21.54/21.75          | ~ (v1_funct_1 @ X34)
% 21.54/21.75          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X33)))
% 21.54/21.75          | (v1_partfun1 @ X34 @ X35)
% 21.54/21.75          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X33)))
% 21.54/21.75          | ~ (v1_funct_2 @ X34 @ X35 @ X33)
% 21.54/21.75          | ~ (v1_funct_1 @ X34))),
% 21.54/21.75      inference('cnf', [status(esa)], [t132_funct_2])).
% 21.54/21.75  thf('40', plain,
% 21.54/21.75      (![X33 : $i, X34 : $i, X35 : $i]:
% 21.54/21.75         (~ (v1_funct_2 @ X34 @ X35 @ X33)
% 21.54/21.75          | (v1_partfun1 @ X34 @ X35)
% 21.54/21.75          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X33)))
% 21.54/21.75          | ~ (v1_funct_1 @ X34)
% 21.54/21.75          | ((X33) = (k1_xboole_0)))),
% 21.54/21.75      inference('simplify', [status(thm)], ['39'])).
% 21.54/21.75  thf('41', plain,
% 21.54/21.75      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 21.54/21.75        | ~ (v1_funct_1 @ sk_C)
% 21.54/21.75        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 21.54/21.75        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['38', '40'])).
% 21.54/21.75  thf('42', plain, ((v1_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('43', plain,
% 21.54/21.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('44', plain,
% 21.54/21.75      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 21.54/21.75        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 21.54/21.75      inference('demod', [status(thm)], ['41', '42', '43'])).
% 21.54/21.75  thf(d4_partfun1, axiom,
% 21.54/21.75    (![A:$i,B:$i]:
% 21.54/21.75     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 21.54/21.75       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 21.54/21.75  thf('45', plain,
% 21.54/21.75      (![X27 : $i, X28 : $i]:
% 21.54/21.75         (~ (v1_partfun1 @ X28 @ X27)
% 21.54/21.75          | ((k1_relat_1 @ X28) = (X27))
% 21.54/21.75          | ~ (v4_relat_1 @ X28 @ X27)
% 21.54/21.75          | ~ (v1_relat_1 @ X28))),
% 21.54/21.75      inference('cnf', [status(esa)], [d4_partfun1])).
% 21.54/21.75  thf('46', plain,
% 21.54/21.75      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 21.54/21.75        | ~ (v1_relat_1 @ sk_C)
% 21.54/21.75        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 21.54/21.75        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['44', '45'])).
% 21.54/21.75  thf('47', plain,
% 21.54/21.75      ((m1_subset_1 @ sk_C @ 
% 21.54/21.75        (k1_zfmisc_1 @ 
% 21.54/21.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf(cc2_relat_1, axiom,
% 21.54/21.75    (![A:$i]:
% 21.54/21.75     ( ( v1_relat_1 @ A ) =>
% 21.54/21.75       ( ![B:$i]:
% 21.54/21.75         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 21.54/21.75  thf('48', plain,
% 21.54/21.75      (![X1 : $i, X2 : $i]:
% 21.54/21.75         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 21.54/21.75          | (v1_relat_1 @ X1)
% 21.54/21.75          | ~ (v1_relat_1 @ X2))),
% 21.54/21.75      inference('cnf', [status(esa)], [cc2_relat_1])).
% 21.54/21.75  thf('49', plain,
% 21.54/21.75      ((~ (v1_relat_1 @ 
% 21.54/21.75           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 21.54/21.75        | (v1_relat_1 @ sk_C))),
% 21.54/21.75      inference('sup-', [status(thm)], ['47', '48'])).
% 21.54/21.75  thf(fc6_relat_1, axiom,
% 21.54/21.75    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 21.54/21.75  thf('50', plain,
% 21.54/21.75      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 21.54/21.75      inference('cnf', [status(esa)], [fc6_relat_1])).
% 21.54/21.75  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['49', '50'])).
% 21.54/21.75  thf('52', plain,
% 21.54/21.75      ((m1_subset_1 @ sk_C @ 
% 21.54/21.75        (k1_zfmisc_1 @ 
% 21.54/21.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf(cc2_relset_1, axiom,
% 21.54/21.75    (![A:$i,B:$i,C:$i]:
% 21.54/21.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.54/21.75       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 21.54/21.75  thf('53', plain,
% 21.54/21.75      (![X13 : $i, X14 : $i, X15 : $i]:
% 21.54/21.75         ((v4_relat_1 @ X13 @ X14)
% 21.54/21.75          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 21.54/21.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 21.54/21.75  thf('54', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 21.54/21.75      inference('sup-', [status(thm)], ['52', '53'])).
% 21.54/21.75  thf('55', plain,
% 21.54/21.75      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 21.54/21.75        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 21.54/21.75      inference('demod', [status(thm)], ['46', '51', '54'])).
% 21.54/21.75  thf('56', plain,
% 21.54/21.75      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 21.54/21.75        | ~ (l1_struct_0 @ sk_B)
% 21.54/21.75        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 21.54/21.75      inference('sup+', [status(thm)], ['37', '55'])).
% 21.54/21.75  thf('57', plain, ((l1_struct_0 @ sk_B)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('58', plain,
% 21.54/21.75      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 21.54/21.75        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 21.54/21.75      inference('demod', [status(thm)], ['56', '57'])).
% 21.54/21.75  thf('59', plain,
% 21.54/21.75      (![X42 : $i]:
% 21.54/21.75         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 21.54/21.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 21.54/21.75  thf('60', plain,
% 21.54/21.75      (![X42 : $i]:
% 21.54/21.75         (((k2_struct_0 @ X42) = (u1_struct_0 @ X42)) | ~ (l1_struct_0 @ X42))),
% 21.54/21.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 21.54/21.75  thf('61', plain,
% 21.54/21.75      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 21.54/21.75          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 21.54/21.75          sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('62', plain,
% 21.54/21.75      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 21.54/21.75           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 21.54/21.75           sk_C)
% 21.54/21.75        | ~ (l1_struct_0 @ sk_B))),
% 21.54/21.75      inference('sup-', [status(thm)], ['60', '61'])).
% 21.54/21.75  thf('63', plain, ((l1_struct_0 @ sk_B)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('64', plain,
% 21.54/21.75      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 21.54/21.75          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 21.54/21.75          sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['62', '63'])).
% 21.54/21.75  thf('65', plain,
% 21.54/21.75      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 21.54/21.75           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 21.54/21.75           sk_C)
% 21.54/21.75        | ~ (l1_struct_0 @ sk_B))),
% 21.54/21.75      inference('sup-', [status(thm)], ['59', '64'])).
% 21.54/21.75  thf('66', plain, ((l1_struct_0 @ sk_B)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('67', plain,
% 21.54/21.75      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 21.54/21.75          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 21.54/21.75          sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['65', '66'])).
% 21.54/21.75  thf('68', plain,
% 21.54/21.75      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 21.54/21.75         = (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('simplify', [status(thm)], ['30'])).
% 21.54/21.75  thf('69', plain,
% 21.54/21.75      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 21.54/21.75          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75           (k2_funct_1 @ sk_C)) @ 
% 21.54/21.75          sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['67', '68'])).
% 21.54/21.75  thf('70', plain,
% 21.54/21.75      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 21.54/21.75           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 21.54/21.75            (k2_funct_1 @ sk_C)) @ 
% 21.54/21.75           sk_C)
% 21.54/21.75        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['58', '69'])).
% 21.54/21.75  thf(t55_funct_1, axiom,
% 21.54/21.75    (![A:$i]:
% 21.54/21.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 21.54/21.75       ( ( v2_funct_1 @ A ) =>
% 21.54/21.75         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 21.54/21.75           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 21.54/21.75  thf('71', plain,
% 21.54/21.75      (![X10 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X10)
% 21.54/21.75          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 21.54/21.75          | ~ (v1_funct_1 @ X10)
% 21.54/21.75          | ~ (v1_relat_1 @ X10))),
% 21.54/21.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 21.54/21.75  thf(dt_k2_funct_1, axiom,
% 21.54/21.75    (![A:$i]:
% 21.54/21.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 21.54/21.75       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 21.54/21.75         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 21.54/21.75  thf('72', plain,
% 21.54/21.75      (![X5 : $i]:
% 21.54/21.75         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 21.54/21.75          | ~ (v1_funct_1 @ X5)
% 21.54/21.75          | ~ (v1_relat_1 @ X5))),
% 21.54/21.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 21.54/21.75  thf('73', plain,
% 21.54/21.75      (![X12 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X12)
% 21.54/21.75          | ((k2_funct_1 @ (k2_funct_1 @ X12)) = (X12))
% 21.54/21.75          | ~ (v1_funct_1 @ X12)
% 21.54/21.75          | ~ (v1_relat_1 @ X12))),
% 21.54/21.75      inference('cnf', [status(esa)], [t65_funct_1])).
% 21.54/21.75  thf('74', plain,
% 21.54/21.75      ((m1_subset_1 @ sk_C @ 
% 21.54/21.75        (k1_zfmisc_1 @ 
% 21.54/21.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 21.54/21.75      inference('demod', [status(thm)], ['13', '14'])).
% 21.54/21.75  thf(t31_funct_2, axiom,
% 21.54/21.75    (![A:$i,B:$i,C:$i]:
% 21.54/21.75     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 21.54/21.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.54/21.75       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 21.54/21.75         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 21.54/21.75           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 21.54/21.75           ( m1_subset_1 @
% 21.54/21.75             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 21.54/21.75  thf('75', plain,
% 21.54/21.75      (![X36 : $i, X37 : $i, X38 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X36)
% 21.54/21.75          | ((k2_relset_1 @ X38 @ X37 @ X36) != (X37))
% 21.54/21.75          | (m1_subset_1 @ (k2_funct_1 @ X36) @ 
% 21.54/21.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 21.54/21.75          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 21.54/21.75          | ~ (v1_funct_2 @ X36 @ X38 @ X37)
% 21.54/21.75          | ~ (v1_funct_1 @ X36))),
% 21.54/21.75      inference('cnf', [status(esa)], [t31_funct_2])).
% 21.54/21.75  thf('76', plain,
% 21.54/21.75      ((~ (v1_funct_1 @ sk_C)
% 21.54/21.75        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 21.54/21.75        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 21.54/21.75           (k1_zfmisc_1 @ 
% 21.54/21.75            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 21.54/21.75        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 21.54/21.75            != (k2_struct_0 @ sk_B))
% 21.54/21.75        | ~ (v2_funct_1 @ sk_C))),
% 21.54/21.75      inference('sup-', [status(thm)], ['74', '75'])).
% 21.54/21.75  thf('77', plain, ((v1_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('78', plain,
% 21.54/21.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 21.54/21.75      inference('demod', [status(thm)], ['21', '22'])).
% 21.54/21.75  thf('79', plain,
% 21.54/21.75      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 21.54/21.75         = (k2_struct_0 @ sk_B))),
% 21.54/21.75      inference('demod', [status(thm)], ['27', '28'])).
% 21.54/21.75  thf('80', plain, ((v2_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('81', plain,
% 21.54/21.75      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 21.54/21.75         (k1_zfmisc_1 @ 
% 21.54/21.75          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 21.54/21.75        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 21.54/21.75      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 21.54/21.75  thf('82', plain,
% 21.54/21.75      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 21.54/21.75        (k1_zfmisc_1 @ 
% 21.54/21.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 21.54/21.75      inference('simplify', [status(thm)], ['81'])).
% 21.54/21.75  thf('83', plain,
% 21.54/21.75      (![X1 : $i, X2 : $i]:
% 21.54/21.75         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 21.54/21.75          | (v1_relat_1 @ X1)
% 21.54/21.75          | ~ (v1_relat_1 @ X2))),
% 21.54/21.75      inference('cnf', [status(esa)], [cc2_relat_1])).
% 21.54/21.75  thf('84', plain,
% 21.54/21.75      ((~ (v1_relat_1 @ 
% 21.54/21.75           (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))
% 21.54/21.75        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['82', '83'])).
% 21.54/21.75  thf('85', plain,
% 21.54/21.75      (![X3 : $i, X4 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X3 @ X4))),
% 21.54/21.75      inference('cnf', [status(esa)], [fc6_relat_1])).
% 21.54/21.75  thf('86', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('demod', [status(thm)], ['84', '85'])).
% 21.54/21.75  thf('87', plain,
% 21.54/21.75      (![X10 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X10)
% 21.54/21.75          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 21.54/21.75          | ~ (v1_funct_1 @ X10)
% 21.54/21.75          | ~ (v1_relat_1 @ X10))),
% 21.54/21.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 21.54/21.75  thf('88', plain,
% 21.54/21.75      (![X10 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X10)
% 21.54/21.75          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 21.54/21.75          | ~ (v1_funct_1 @ X10)
% 21.54/21.75          | ~ (v1_relat_1 @ X10))),
% 21.54/21.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 21.54/21.75  thf('89', plain,
% 21.54/21.75      (![X5 : $i]:
% 21.54/21.75         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 21.54/21.75          | ~ (v1_funct_1 @ X5)
% 21.54/21.75          | ~ (v1_relat_1 @ X5))),
% 21.54/21.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 21.54/21.75  thf('90', plain,
% 21.54/21.75      (![X5 : $i]:
% 21.54/21.75         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 21.54/21.75          | ~ (v1_funct_1 @ X5)
% 21.54/21.75          | ~ (v1_relat_1 @ X5))),
% 21.54/21.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 21.54/21.75  thf(t61_funct_1, axiom,
% 21.54/21.75    (![A:$i]:
% 21.54/21.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 21.54/21.75       ( ( v2_funct_1 @ A ) =>
% 21.54/21.75         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 21.54/21.75             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 21.54/21.75           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 21.54/21.75             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 21.54/21.75  thf('91', plain,
% 21.54/21.75      (![X11 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X11)
% 21.54/21.75          | ((k5_relat_1 @ (k2_funct_1 @ X11) @ X11)
% 21.54/21.75              = (k6_relat_1 @ (k2_relat_1 @ X11)))
% 21.54/21.75          | ~ (v1_funct_1 @ X11)
% 21.54/21.75          | ~ (v1_relat_1 @ X11))),
% 21.54/21.75      inference('cnf', [status(esa)], [t61_funct_1])).
% 21.54/21.75  thf(t48_funct_1, axiom,
% 21.54/21.75    (![A:$i]:
% 21.54/21.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 21.54/21.75       ( ![B:$i]:
% 21.54/21.75         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 21.54/21.75           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 21.54/21.75               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 21.54/21.75             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 21.54/21.75  thf('92', plain,
% 21.54/21.75      (![X8 : $i, X9 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X8)
% 21.54/21.75          | ~ (v1_funct_1 @ X8)
% 21.54/21.75          | (v2_funct_1 @ X8)
% 21.54/21.75          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X9))
% 21.54/21.75          | ~ (v2_funct_1 @ (k5_relat_1 @ X8 @ X9))
% 21.54/21.75          | ~ (v1_funct_1 @ X9)
% 21.54/21.75          | ~ (v1_relat_1 @ X9))),
% 21.54/21.75      inference('cnf', [status(esa)], [t48_funct_1])).
% 21.54/21.75  thf('93', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 21.54/21.75          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['91', '92'])).
% 21.54/21.75  thf(fc4_funct_1, axiom,
% 21.54/21.75    (![A:$i]:
% 21.54/21.75     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 21.54/21.75       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 21.54/21.75  thf('94', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 21.54/21.75      inference('cnf', [status(esa)], [fc4_funct_1])).
% 21.54/21.75  thf('95', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 21.54/21.75          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 21.54/21.75      inference('demod', [status(thm)], ['93', '94'])).
% 21.54/21.75  thf('96', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['95'])).
% 21.54/21.75  thf('97', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 21.54/21.75          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['90', '96'])).
% 21.54/21.75  thf('98', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['97'])).
% 21.54/21.75  thf('99', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 21.54/21.75          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['89', '98'])).
% 21.54/21.75  thf('100', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['99'])).
% 21.54/21.75  thf('101', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['88', '100'])).
% 21.54/21.75  thf('102', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['101'])).
% 21.54/21.75  thf('103', plain,
% 21.54/21.75      (![X5 : $i]:
% 21.54/21.75         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 21.54/21.75          | ~ (v1_funct_1 @ X5)
% 21.54/21.75          | ~ (v1_relat_1 @ X5))),
% 21.54/21.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 21.54/21.75  thf('104', plain,
% 21.54/21.75      (![X5 : $i]:
% 21.54/21.75         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 21.54/21.75          | ~ (v1_funct_1 @ X5)
% 21.54/21.75          | ~ (v1_relat_1 @ X5))),
% 21.54/21.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 21.54/21.75  thf('105', plain,
% 21.54/21.75      (![X10 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X10)
% 21.54/21.75          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 21.54/21.75          | ~ (v1_funct_1 @ X10)
% 21.54/21.75          | ~ (v1_relat_1 @ X10))),
% 21.54/21.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 21.54/21.75  thf('106', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['101'])).
% 21.54/21.75  thf('107', plain,
% 21.54/21.75      (![X5 : $i]:
% 21.54/21.75         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 21.54/21.75          | ~ (v1_funct_1 @ X5)
% 21.54/21.75          | ~ (v1_relat_1 @ X5))),
% 21.54/21.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 21.54/21.75  thf('108', plain,
% 21.54/21.75      (![X5 : $i]:
% 21.54/21.75         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 21.54/21.75          | ~ (v1_funct_1 @ X5)
% 21.54/21.75          | ~ (v1_relat_1 @ X5))),
% 21.54/21.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 21.54/21.75  thf('109', plain,
% 21.54/21.75      (![X10 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X10)
% 21.54/21.75          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 21.54/21.75          | ~ (v1_funct_1 @ X10)
% 21.54/21.75          | ~ (v1_relat_1 @ X10))),
% 21.54/21.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 21.54/21.75  thf('110', plain,
% 21.54/21.75      (![X5 : $i]:
% 21.54/21.75         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 21.54/21.75          | ~ (v1_funct_1 @ X5)
% 21.54/21.75          | ~ (v1_relat_1 @ X5))),
% 21.54/21.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 21.54/21.75  thf('111', plain,
% 21.54/21.75      (![X5 : $i]:
% 21.54/21.75         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 21.54/21.75          | ~ (v1_funct_1 @ X5)
% 21.54/21.75          | ~ (v1_relat_1 @ X5))),
% 21.54/21.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 21.54/21.75  thf('112', plain,
% 21.54/21.75      (![X10 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X10)
% 21.54/21.75          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 21.54/21.75          | ~ (v1_funct_1 @ X10)
% 21.54/21.75          | ~ (v1_relat_1 @ X10))),
% 21.54/21.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 21.54/21.75  thf(t3_funct_2, axiom,
% 21.54/21.75    (![A:$i]:
% 21.54/21.75     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 21.54/21.75       ( ( v1_funct_1 @ A ) & 
% 21.54/21.75         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 21.54/21.75         ( m1_subset_1 @
% 21.54/21.75           A @ 
% 21.54/21.75           ( k1_zfmisc_1 @
% 21.54/21.75             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 21.54/21.75  thf('113', plain,
% 21.54/21.75      (![X39 : $i]:
% 21.54/21.75         ((m1_subset_1 @ X39 @ 
% 21.54/21.75           (k1_zfmisc_1 @ 
% 21.54/21.75            (k2_zfmisc_1 @ (k1_relat_1 @ X39) @ (k2_relat_1 @ X39))))
% 21.54/21.75          | ~ (v1_funct_1 @ X39)
% 21.54/21.75          | ~ (v1_relat_1 @ X39))),
% 21.54/21.75      inference('cnf', [status(esa)], [t3_funct_2])).
% 21.54/21.75  thf('114', plain,
% 21.54/21.75      (![X13 : $i, X14 : $i, X15 : $i]:
% 21.54/21.75         ((v4_relat_1 @ X13 @ X14)
% 21.54/21.75          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 21.54/21.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 21.54/21.75  thf('115', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['113', '114'])).
% 21.54/21.75  thf('116', plain,
% 21.54/21.75      (![X27 : $i, X28 : $i]:
% 21.54/21.75         (((k1_relat_1 @ X28) != (X27))
% 21.54/21.75          | (v1_partfun1 @ X28 @ X27)
% 21.54/21.75          | ~ (v4_relat_1 @ X28 @ X27)
% 21.54/21.75          | ~ (v1_relat_1 @ X28))),
% 21.54/21.75      inference('cnf', [status(esa)], [d4_partfun1])).
% 21.54/21.75  thf('117', plain,
% 21.54/21.75      (![X28 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X28)
% 21.54/21.75          | ~ (v4_relat_1 @ X28 @ (k1_relat_1 @ X28))
% 21.54/21.75          | (v1_partfun1 @ X28 @ (k1_relat_1 @ X28)))),
% 21.54/21.75      inference('simplify', [status(thm)], ['116'])).
% 21.54/21.75  thf('118', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | (v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('sup-', [status(thm)], ['115', '117'])).
% 21.54/21.75  thf('119', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['118'])).
% 21.54/21.75  thf('120', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 21.54/21.75      inference('sup+', [status(thm)], ['112', '119'])).
% 21.54/21.75  thf('121', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['111', '120'])).
% 21.54/21.75  thf('122', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['121'])).
% 21.54/21.75  thf('123', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['110', '122'])).
% 21.54/21.75  thf('124', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['123'])).
% 21.54/21.75  thf('125', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 21.54/21.75      inference('sup+', [status(thm)], ['109', '124'])).
% 21.54/21.75  thf('126', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['108', '125'])).
% 21.54/21.75  thf('127', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['126'])).
% 21.54/21.75  thf('128', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['107', '127'])).
% 21.54/21.75  thf('129', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['128'])).
% 21.54/21.75  thf('130', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['106', '129'])).
% 21.54/21.75  thf('131', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['130'])).
% 21.54/21.75  thf('132', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 21.54/21.75           (k2_relat_1 @ X0))
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 21.54/21.75      inference('sup+', [status(thm)], ['105', '131'])).
% 21.54/21.75  thf('133', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 21.54/21.75             (k2_relat_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['104', '132'])).
% 21.54/21.75  thf('134', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 21.54/21.75           (k2_relat_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['133'])).
% 21.54/21.75  thf('135', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 21.54/21.75             (k2_relat_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['103', '134'])).
% 21.54/21.75  thf('136', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 21.54/21.75           (k2_relat_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['135'])).
% 21.54/21.75  thf('137', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 21.54/21.75             (k2_relat_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['102', '136'])).
% 21.54/21.75  thf('138', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 21.54/21.75           (k2_relat_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['137'])).
% 21.54/21.75  thf('139', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v1_partfun1 @ 
% 21.54/21.75           (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))) @ 
% 21.54/21.75           (k1_relat_1 @ X0))
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 21.54/21.75      inference('sup+', [status(thm)], ['87', '138'])).
% 21.54/21.75  thf('140', plain,
% 21.54/21.75      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ~ (v2_funct_1 @ sk_C)
% 21.54/21.75        | ~ (v1_funct_1 @ sk_C)
% 21.54/21.75        | ~ (v1_relat_1 @ sk_C)
% 21.54/21.75        | (v1_partfun1 @ 
% 21.54/21.75           (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))) @ 
% 21.54/21.75           (k1_relat_1 @ sk_C)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['86', '139'])).
% 21.54/21.75  thf('141', plain,
% 21.54/21.75      (![X10 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X10)
% 21.54/21.75          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 21.54/21.75          | ~ (v1_funct_1 @ X10)
% 21.54/21.75          | ~ (v1_relat_1 @ X10))),
% 21.54/21.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 21.54/21.75  thf('142', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['101'])).
% 21.54/21.75  thf('143', plain,
% 21.54/21.75      ((m1_subset_1 @ sk_C @ 
% 21.54/21.75        (k1_zfmisc_1 @ 
% 21.54/21.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 21.54/21.75      inference('demod', [status(thm)], ['13', '14'])).
% 21.54/21.75  thf('144', plain,
% 21.54/21.75      (![X36 : $i, X37 : $i, X38 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X36)
% 21.54/21.75          | ((k2_relset_1 @ X38 @ X37 @ X36) != (X37))
% 21.54/21.75          | (v1_funct_1 @ (k2_funct_1 @ X36))
% 21.54/21.75          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 21.54/21.75          | ~ (v1_funct_2 @ X36 @ X38 @ X37)
% 21.54/21.75          | ~ (v1_funct_1 @ X36))),
% 21.54/21.75      inference('cnf', [status(esa)], [t31_funct_2])).
% 21.54/21.75  thf('145', plain,
% 21.54/21.75      ((~ (v1_funct_1 @ sk_C)
% 21.54/21.75        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 21.54/21.75        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 21.54/21.75            != (k2_struct_0 @ sk_B))
% 21.54/21.75        | ~ (v2_funct_1 @ sk_C))),
% 21.54/21.75      inference('sup-', [status(thm)], ['143', '144'])).
% 21.54/21.75  thf('146', plain, ((v1_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('147', plain,
% 21.54/21.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 21.54/21.75      inference('demod', [status(thm)], ['21', '22'])).
% 21.54/21.75  thf('148', plain,
% 21.54/21.75      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 21.54/21.75         = (k2_struct_0 @ sk_B))),
% 21.54/21.75      inference('demod', [status(thm)], ['27', '28'])).
% 21.54/21.75  thf('149', plain, ((v2_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('150', plain,
% 21.54/21.75      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 21.54/21.75      inference('demod', [status(thm)], ['145', '146', '147', '148', '149'])).
% 21.54/21.75  thf('151', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('simplify', [status(thm)], ['150'])).
% 21.54/21.75  thf('152', plain,
% 21.54/21.75      (![X12 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X12)
% 21.54/21.75          | ((k2_funct_1 @ (k2_funct_1 @ X12)) = (X12))
% 21.54/21.75          | ~ (v1_funct_1 @ X12)
% 21.54/21.75          | ~ (v1_relat_1 @ X12))),
% 21.54/21.75      inference('cnf', [status(esa)], [t65_funct_1])).
% 21.54/21.75  thf('153', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['101'])).
% 21.54/21.75  thf('154', plain,
% 21.54/21.75      (![X5 : $i]:
% 21.54/21.75         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 21.54/21.75          | ~ (v1_funct_1 @ X5)
% 21.54/21.75          | ~ (v1_relat_1 @ X5))),
% 21.54/21.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 21.54/21.75  thf('155', plain,
% 21.54/21.75      (![X5 : $i]:
% 21.54/21.75         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 21.54/21.75          | ~ (v1_funct_1 @ X5)
% 21.54/21.75          | ~ (v1_relat_1 @ X5))),
% 21.54/21.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 21.54/21.75  thf('156', plain,
% 21.54/21.75      (![X12 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X12)
% 21.54/21.75          | ((k2_funct_1 @ (k2_funct_1 @ X12)) = (X12))
% 21.54/21.75          | ~ (v1_funct_1 @ X12)
% 21.54/21.75          | ~ (v1_relat_1 @ X12))),
% 21.54/21.75      inference('cnf', [status(esa)], [t65_funct_1])).
% 21.54/21.75  thf('157', plain,
% 21.54/21.75      (![X11 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X11)
% 21.54/21.75          | ((k5_relat_1 @ (k2_funct_1 @ X11) @ X11)
% 21.54/21.75              = (k6_relat_1 @ (k2_relat_1 @ X11)))
% 21.54/21.75          | ~ (v1_funct_1 @ X11)
% 21.54/21.75          | ~ (v1_relat_1 @ X11))),
% 21.54/21.75      inference('cnf', [status(esa)], [t61_funct_1])).
% 21.54/21.75  thf('158', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 21.54/21.75            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 21.54/21.75      inference('sup+', [status(thm)], ['156', '157'])).
% 21.54/21.75  thf('159', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 21.54/21.75              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 21.54/21.75      inference('sup-', [status(thm)], ['155', '158'])).
% 21.54/21.75  thf('160', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 21.54/21.75            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['159'])).
% 21.54/21.75  thf('161', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 21.54/21.75              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 21.54/21.75      inference('sup-', [status(thm)], ['154', '160'])).
% 21.54/21.75  thf('162', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 21.54/21.75            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['161'])).
% 21.54/21.75  thf('163', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 21.54/21.75              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 21.54/21.75      inference('sup-', [status(thm)], ['153', '162'])).
% 21.54/21.75  thf('164', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 21.54/21.75            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['163'])).
% 21.54/21.75  thf('165', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 21.54/21.75      inference('cnf', [status(esa)], [fc4_funct_1])).
% 21.54/21.75  thf('166', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v2_funct_1 @ (k5_relat_1 @ X0 @ (k2_funct_1 @ X0)))
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0))),
% 21.54/21.75      inference('sup+', [status(thm)], ['164', '165'])).
% 21.54/21.75  thf('167', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v2_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X0))
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 21.54/21.75      inference('sup+', [status(thm)], ['152', '166'])).
% 21.54/21.75  thf('168', plain,
% 21.54/21.75      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ~ (v2_funct_1 @ sk_C)
% 21.54/21.75        | ~ (v1_funct_1 @ sk_C)
% 21.54/21.75        | ~ (v1_relat_1 @ sk_C)
% 21.54/21.75        | (v2_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['151', '167'])).
% 21.54/21.75  thf('169', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('demod', [status(thm)], ['84', '85'])).
% 21.54/21.75  thf('170', plain, ((v2_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('171', plain, ((v1_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('172', plain, ((v1_relat_1 @ sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['49', '50'])).
% 21.54/21.75  thf('173', plain,
% 21.54/21.75      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | (v2_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 21.54/21.75      inference('demod', [status(thm)], ['168', '169', '170', '171', '172'])).
% 21.54/21.75  thf('174', plain,
% 21.54/21.75      ((~ (v1_relat_1 @ sk_C)
% 21.54/21.75        | ~ (v1_funct_1 @ sk_C)
% 21.54/21.75        | ~ (v2_funct_1 @ sk_C)
% 21.54/21.75        | (v2_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['142', '173'])).
% 21.54/21.75  thf('175', plain, ((v1_relat_1 @ sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['49', '50'])).
% 21.54/21.75  thf('176', plain, ((v1_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('177', plain, ((v2_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('178', plain, ((v2_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))),
% 21.54/21.75      inference('demod', [status(thm)], ['174', '175', '176', '177'])).
% 21.54/21.75  thf('179', plain,
% 21.54/21.75      (![X8 : $i, X9 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X8)
% 21.54/21.75          | ~ (v1_funct_1 @ X8)
% 21.54/21.75          | (v2_funct_1 @ X8)
% 21.54/21.75          | ((k2_relat_1 @ X8) != (k1_relat_1 @ X9))
% 21.54/21.75          | ~ (v2_funct_1 @ (k5_relat_1 @ X8 @ X9))
% 21.54/21.75          | ~ (v1_funct_1 @ X9)
% 21.54/21.75          | ~ (v1_relat_1 @ X9))),
% 21.54/21.75      inference('cnf', [status(esa)], [t48_funct_1])).
% 21.54/21.75  thf('180', plain,
% 21.54/21.75      ((~ (v1_relat_1 @ sk_C)
% 21.54/21.75        | ~ (v1_funct_1 @ sk_C)
% 21.54/21.75        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 21.54/21.75        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['178', '179'])).
% 21.54/21.75  thf('181', plain, ((v1_relat_1 @ sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['49', '50'])).
% 21.54/21.75  thf('182', plain, ((v1_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('183', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('simplify', [status(thm)], ['150'])).
% 21.54/21.75  thf('184', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('demod', [status(thm)], ['84', '85'])).
% 21.54/21.75  thf('185', plain,
% 21.54/21.75      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 21.54/21.75        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 21.54/21.75      inference('demod', [status(thm)], ['180', '181', '182', '183', '184'])).
% 21.54/21.75  thf('186', plain,
% 21.54/21.75      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 21.54/21.75        | ~ (v1_relat_1 @ sk_C)
% 21.54/21.75        | ~ (v1_funct_1 @ sk_C)
% 21.54/21.75        | ~ (v2_funct_1 @ sk_C)
% 21.54/21.75        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['141', '185'])).
% 21.54/21.75  thf('187', plain, ((v1_relat_1 @ sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['49', '50'])).
% 21.54/21.75  thf('188', plain, ((v1_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('189', plain, ((v2_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('190', plain,
% 21.54/21.75      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 21.54/21.75        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 21.54/21.75      inference('demod', [status(thm)], ['186', '187', '188', '189'])).
% 21.54/21.75  thf('191', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('simplify', [status(thm)], ['190'])).
% 21.54/21.75  thf('192', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('simplify', [status(thm)], ['150'])).
% 21.54/21.75  thf('193', plain, ((v2_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('194', plain, ((v1_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('195', plain, ((v1_relat_1 @ sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['49', '50'])).
% 21.54/21.75  thf('196', plain,
% 21.54/21.75      ((v1_partfun1 @ 
% 21.54/21.75        (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))) @ 
% 21.54/21.75        (k1_relat_1 @ sk_C))),
% 21.54/21.75      inference('demod', [status(thm)],
% 21.54/21.75                ['140', '191', '192', '193', '194', '195'])).
% 21.54/21.75  thf('197', plain,
% 21.54/21.75      (((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k1_relat_1 @ sk_C))
% 21.54/21.75        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 21.54/21.75      inference('sup+', [status(thm)], ['73', '196'])).
% 21.54/21.75  thf('198', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('demod', [status(thm)], ['84', '85'])).
% 21.54/21.75  thf('199', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('simplify', [status(thm)], ['150'])).
% 21.54/21.75  thf('200', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('simplify', [status(thm)], ['190'])).
% 21.54/21.75  thf('201', plain,
% 21.54/21.75      ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k1_relat_1 @ sk_C))),
% 21.54/21.75      inference('demod', [status(thm)], ['197', '198', '199', '200'])).
% 21.54/21.75  thf('202', plain,
% 21.54/21.75      (![X27 : $i, X28 : $i]:
% 21.54/21.75         (~ (v1_partfun1 @ X28 @ X27)
% 21.54/21.75          | ((k1_relat_1 @ X28) = (X27))
% 21.54/21.75          | ~ (v4_relat_1 @ X28 @ X27)
% 21.54/21.75          | ~ (v1_relat_1 @ X28))),
% 21.54/21.75      inference('cnf', [status(esa)], [d4_partfun1])).
% 21.54/21.75  thf('203', plain,
% 21.54/21.75      ((~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 21.54/21.75        | ~ (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 21.54/21.75             (k1_relat_1 @ sk_C))
% 21.54/21.75        | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 21.54/21.75            = (k1_relat_1 @ sk_C)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['201', '202'])).
% 21.54/21.75  thf('204', plain,
% 21.54/21.75      (![X12 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X12)
% 21.54/21.75          | ((k2_funct_1 @ (k2_funct_1 @ X12)) = (X12))
% 21.54/21.75          | ~ (v1_funct_1 @ X12)
% 21.54/21.75          | ~ (v1_relat_1 @ X12))),
% 21.54/21.75      inference('cnf', [status(esa)], [t65_funct_1])).
% 21.54/21.75  thf('205', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('demod', [status(thm)], ['84', '85'])).
% 21.54/21.75  thf('206', plain,
% 21.54/21.75      (![X10 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X10)
% 21.54/21.75          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 21.54/21.75          | ~ (v1_funct_1 @ X10)
% 21.54/21.75          | ~ (v1_relat_1 @ X10))),
% 21.54/21.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 21.54/21.75  thf('207', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['101'])).
% 21.54/21.75  thf('208', plain,
% 21.54/21.75      (![X5 : $i]:
% 21.54/21.75         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 21.54/21.75          | ~ (v1_funct_1 @ X5)
% 21.54/21.75          | ~ (v1_relat_1 @ X5))),
% 21.54/21.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 21.54/21.75  thf('209', plain,
% 21.54/21.75      (![X5 : $i]:
% 21.54/21.75         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 21.54/21.75          | ~ (v1_funct_1 @ X5)
% 21.54/21.75          | ~ (v1_relat_1 @ X5))),
% 21.54/21.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 21.54/21.75  thf('210', plain,
% 21.54/21.75      (![X10 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X10)
% 21.54/21.75          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 21.54/21.75          | ~ (v1_funct_1 @ X10)
% 21.54/21.75          | ~ (v1_relat_1 @ X10))),
% 21.54/21.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 21.54/21.75  thf('211', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['101'])).
% 21.54/21.75  thf('212', plain,
% 21.54/21.75      (![X5 : $i]:
% 21.54/21.75         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 21.54/21.75          | ~ (v1_funct_1 @ X5)
% 21.54/21.75          | ~ (v1_relat_1 @ X5))),
% 21.54/21.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 21.54/21.75  thf('213', plain,
% 21.54/21.75      (![X5 : $i]:
% 21.54/21.75         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 21.54/21.75          | ~ (v1_funct_1 @ X5)
% 21.54/21.75          | ~ (v1_relat_1 @ X5))),
% 21.54/21.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 21.54/21.75  thf('214', plain,
% 21.54/21.75      (![X10 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X10)
% 21.54/21.75          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 21.54/21.75          | ~ (v1_funct_1 @ X10)
% 21.54/21.75          | ~ (v1_relat_1 @ X10))),
% 21.54/21.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 21.54/21.75  thf('215', plain,
% 21.54/21.75      (![X5 : $i]:
% 21.54/21.75         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 21.54/21.75          | ~ (v1_funct_1 @ X5)
% 21.54/21.75          | ~ (v1_relat_1 @ X5))),
% 21.54/21.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 21.54/21.75  thf('216', plain,
% 21.54/21.75      (![X5 : $i]:
% 21.54/21.75         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 21.54/21.75          | ~ (v1_funct_1 @ X5)
% 21.54/21.75          | ~ (v1_relat_1 @ X5))),
% 21.54/21.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 21.54/21.75  thf('217', plain,
% 21.54/21.75      (![X10 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X10)
% 21.54/21.75          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 21.54/21.75          | ~ (v1_funct_1 @ X10)
% 21.54/21.75          | ~ (v1_relat_1 @ X10))),
% 21.54/21.75      inference('cnf', [status(esa)], [t55_funct_1])).
% 21.54/21.75  thf('218', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['113', '114'])).
% 21.54/21.75  thf('219', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 21.54/21.75      inference('sup+', [status(thm)], ['217', '218'])).
% 21.54/21.75  thf('220', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['216', '219'])).
% 21.54/21.75  thf('221', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['220'])).
% 21.54/21.75  thf('222', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['215', '221'])).
% 21.54/21.75  thf('223', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['222'])).
% 21.54/21.75  thf('224', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 21.54/21.75      inference('sup+', [status(thm)], ['214', '223'])).
% 21.54/21.75  thf('225', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['213', '224'])).
% 21.54/21.75  thf('226', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['225'])).
% 21.54/21.75  thf('227', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['212', '226'])).
% 21.54/21.75  thf('228', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['227'])).
% 21.54/21.75  thf('229', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['211', '228'])).
% 21.54/21.75  thf('230', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['229'])).
% 21.54/21.75  thf('231', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 21.54/21.75           (k2_relat_1 @ X0))
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 21.54/21.75      inference('sup+', [status(thm)], ['210', '230'])).
% 21.54/21.75  thf('232', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 21.54/21.75             (k2_relat_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['209', '231'])).
% 21.54/21.75  thf('233', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 21.54/21.75           (k2_relat_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['232'])).
% 21.54/21.75  thf('234', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 21.54/21.75             (k2_relat_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['208', '233'])).
% 21.54/21.75  thf('235', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 21.54/21.75           (k2_relat_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['234'])).
% 21.54/21.75  thf('236', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 21.54/21.75             (k2_relat_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['207', '235'])).
% 21.54/21.75  thf('237', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ 
% 21.54/21.75           (k2_relat_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['236'])).
% 21.54/21.75  thf('238', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v4_relat_1 @ 
% 21.54/21.75           (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))) @ 
% 21.54/21.75           (k1_relat_1 @ X0))
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 21.54/21.75      inference('sup+', [status(thm)], ['206', '237'])).
% 21.54/21.75  thf('239', plain,
% 21.54/21.75      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ~ (v2_funct_1 @ sk_C)
% 21.54/21.75        | ~ (v1_funct_1 @ sk_C)
% 21.54/21.75        | ~ (v1_relat_1 @ sk_C)
% 21.54/21.75        | (v4_relat_1 @ 
% 21.54/21.75           (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))) @ 
% 21.54/21.75           (k1_relat_1 @ sk_C)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['205', '238'])).
% 21.54/21.75  thf('240', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('simplify', [status(thm)], ['190'])).
% 21.54/21.75  thf('241', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('simplify', [status(thm)], ['150'])).
% 21.54/21.75  thf('242', plain, ((v2_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('243', plain, ((v1_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('244', plain, ((v1_relat_1 @ sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['49', '50'])).
% 21.54/21.75  thf('245', plain,
% 21.54/21.75      ((v4_relat_1 @ 
% 21.54/21.75        (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))) @ 
% 21.54/21.75        (k1_relat_1 @ sk_C))),
% 21.54/21.75      inference('demod', [status(thm)],
% 21.54/21.75                ['239', '240', '241', '242', '243', '244'])).
% 21.54/21.75  thf('246', plain,
% 21.54/21.75      (((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k1_relat_1 @ sk_C))
% 21.54/21.75        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 21.54/21.75      inference('sup+', [status(thm)], ['204', '245'])).
% 21.54/21.75  thf('247', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('demod', [status(thm)], ['84', '85'])).
% 21.54/21.75  thf('248', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('simplify', [status(thm)], ['150'])).
% 21.54/21.75  thf('249', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('simplify', [status(thm)], ['190'])).
% 21.54/21.75  thf('250', plain,
% 21.54/21.75      ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k1_relat_1 @ sk_C))),
% 21.54/21.75      inference('demod', [status(thm)], ['246', '247', '248', '249'])).
% 21.54/21.75  thf('251', plain,
% 21.54/21.75      ((~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 21.54/21.75        | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 21.54/21.75            = (k1_relat_1 @ sk_C)))),
% 21.54/21.75      inference('demod', [status(thm)], ['203', '250'])).
% 21.54/21.75  thf('252', plain,
% 21.54/21.75      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 21.54/21.75            = (k1_relat_1 @ sk_C)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['72', '251'])).
% 21.54/21.75  thf('253', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('demod', [status(thm)], ['84', '85'])).
% 21.54/21.75  thf('254', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('simplify', [status(thm)], ['150'])).
% 21.54/21.75  thf('255', plain,
% 21.54/21.75      (((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))) = (k1_relat_1 @ sk_C))),
% 21.54/21.75      inference('demod', [status(thm)], ['252', '253', '254'])).
% 21.54/21.75  thf('256', plain,
% 21.54/21.75      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 21.54/21.75        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 21.54/21.75      inference('sup+', [status(thm)], ['71', '255'])).
% 21.54/21.75  thf('257', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('demod', [status(thm)], ['84', '85'])).
% 21.54/21.75  thf('258', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('simplify', [status(thm)], ['150'])).
% 21.54/21.75  thf('259', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('simplify', [status(thm)], ['190'])).
% 21.54/21.75  thf('260', plain,
% 21.54/21.75      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 21.54/21.75      inference('demod', [status(thm)], ['256', '257', '258', '259'])).
% 21.54/21.75  thf('261', plain,
% 21.54/21.75      (![X39 : $i]:
% 21.54/21.75         ((m1_subset_1 @ X39 @ 
% 21.54/21.75           (k1_zfmisc_1 @ 
% 21.54/21.75            (k2_zfmisc_1 @ (k1_relat_1 @ X39) @ (k2_relat_1 @ X39))))
% 21.54/21.75          | ~ (v1_funct_1 @ X39)
% 21.54/21.75          | ~ (v1_relat_1 @ X39))),
% 21.54/21.75      inference('cnf', [status(esa)], [t3_funct_2])).
% 21.54/21.75  thf(redefinition_k2_relset_1, axiom,
% 21.54/21.75    (![A:$i,B:$i,C:$i]:
% 21.54/21.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.54/21.75       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 21.54/21.75  thf('262', plain,
% 21.54/21.75      (![X16 : $i, X17 : $i, X18 : $i]:
% 21.54/21.75         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 21.54/21.75          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 21.54/21.75      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 21.54/21.75  thf('263', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 21.54/21.75              = (k2_relat_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['261', '262'])).
% 21.54/21.75  thf('264', plain,
% 21.54/21.75      (![X39 : $i]:
% 21.54/21.75         ((v1_funct_2 @ X39 @ (k1_relat_1 @ X39) @ (k2_relat_1 @ X39))
% 21.54/21.75          | ~ (v1_funct_1 @ X39)
% 21.54/21.75          | ~ (v1_relat_1 @ X39))),
% 21.54/21.75      inference('cnf', [status(esa)], [t3_funct_2])).
% 21.54/21.75  thf('265', plain,
% 21.54/21.75      (![X39 : $i]:
% 21.54/21.75         ((m1_subset_1 @ X39 @ 
% 21.54/21.75           (k1_zfmisc_1 @ 
% 21.54/21.75            (k2_zfmisc_1 @ (k1_relat_1 @ X39) @ (k2_relat_1 @ X39))))
% 21.54/21.75          | ~ (v1_funct_1 @ X39)
% 21.54/21.75          | ~ (v1_relat_1 @ X39))),
% 21.54/21.75      inference('cnf', [status(esa)], [t3_funct_2])).
% 21.54/21.75  thf('266', plain,
% 21.54/21.75      (![X43 : $i, X44 : $i, X45 : $i]:
% 21.54/21.75         (((k2_relset_1 @ X44 @ X43 @ X45) != (X43))
% 21.54/21.75          | ~ (v2_funct_1 @ X45)
% 21.54/21.75          | ((k2_tops_2 @ X44 @ X43 @ X45) = (k2_funct_1 @ X45))
% 21.54/21.75          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 21.54/21.75          | ~ (v1_funct_2 @ X45 @ X44 @ X43)
% 21.54/21.75          | ~ (v1_funct_1 @ X45))),
% 21.54/21.75      inference('cnf', [status(esa)], [d4_tops_2])).
% 21.54/21.75  thf('267', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 21.54/21.75          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 21.54/21.75              = (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 21.54/21.75              != (k2_relat_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['265', '266'])).
% 21.54/21.75  thf('268', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 21.54/21.75            != (k2_relat_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 21.54/21.75              = (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['267'])).
% 21.54/21.75  thf('269', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 21.54/21.75              = (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 21.54/21.75              != (k2_relat_1 @ X0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['264', '268'])).
% 21.54/21.75  thf('270', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 21.54/21.75            != (k2_relat_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 21.54/21.75              = (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['269'])).
% 21.54/21.75  thf('271', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 21.54/21.75              = (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0))),
% 21.54/21.75      inference('sup-', [status(thm)], ['263', '270'])).
% 21.54/21.75  thf('272', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X0)
% 21.54/21.75          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 21.54/21.75              = (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['271'])).
% 21.54/21.75  thf('273', plain,
% 21.54/21.75      ((((k2_tops_2 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 21.54/21.75          (k1_relat_1 @ sk_C) @ (k2_funct_1 @ sk_C))
% 21.54/21.75          = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 21.54/21.75        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 21.54/21.75      inference('sup+', [status(thm)], ['260', '272'])).
% 21.54/21.75  thf('274', plain,
% 21.54/21.75      (![X5 : $i]:
% 21.54/21.75         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 21.54/21.75          | ~ (v1_funct_1 @ X5)
% 21.54/21.75          | ~ (v1_relat_1 @ X5))),
% 21.54/21.75      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 21.54/21.75  thf('275', plain,
% 21.54/21.75      ((m1_subset_1 @ sk_C @ 
% 21.54/21.75        (k1_zfmisc_1 @ 
% 21.54/21.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('276', plain,
% 21.54/21.75      (![X16 : $i, X17 : $i, X18 : $i]:
% 21.54/21.75         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 21.54/21.75          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 21.54/21.75      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 21.54/21.75  thf('277', plain,
% 21.54/21.75      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 21.54/21.75         = (k2_relat_1 @ sk_C))),
% 21.54/21.75      inference('sup-', [status(thm)], ['275', '276'])).
% 21.54/21.75  thf('278', plain,
% 21.54/21.75      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 21.54/21.75         = (k2_struct_0 @ sk_B))),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('279', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 21.54/21.75      inference('sup+', [status(thm)], ['277', '278'])).
% 21.54/21.75  thf('280', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['123'])).
% 21.54/21.75  thf('281', plain,
% 21.54/21.75      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 21.54/21.75        | ~ (v1_relat_1 @ sk_C)
% 21.54/21.75        | ~ (v1_funct_1 @ sk_C)
% 21.54/21.75        | ~ (v2_funct_1 @ sk_C))),
% 21.54/21.75      inference('sup+', [status(thm)], ['279', '280'])).
% 21.54/21.75  thf('282', plain, ((v1_relat_1 @ sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['49', '50'])).
% 21.54/21.75  thf('283', plain, ((v1_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('284', plain, ((v2_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('285', plain,
% 21.54/21.75      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 21.54/21.75      inference('demod', [status(thm)], ['281', '282', '283', '284'])).
% 21.54/21.75  thf('286', plain,
% 21.54/21.75      (![X27 : $i, X28 : $i]:
% 21.54/21.75         (~ (v1_partfun1 @ X28 @ X27)
% 21.54/21.75          | ((k1_relat_1 @ X28) = (X27))
% 21.54/21.75          | ~ (v4_relat_1 @ X28 @ X27)
% 21.54/21.75          | ~ (v1_relat_1 @ X28))),
% 21.54/21.75      inference('cnf', [status(esa)], [d4_partfun1])).
% 21.54/21.75  thf('287', plain,
% 21.54/21.75      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 21.54/21.75        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['285', '286'])).
% 21.54/21.75  thf('288', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 21.54/21.75      inference('sup+', [status(thm)], ['277', '278'])).
% 21.54/21.75  thf('289', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 21.54/21.75          | ~ (v2_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['222'])).
% 21.54/21.75  thf('290', plain,
% 21.54/21.75      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 21.54/21.75        | ~ (v1_relat_1 @ sk_C)
% 21.54/21.75        | ~ (v1_funct_1 @ sk_C)
% 21.54/21.75        | ~ (v2_funct_1 @ sk_C))),
% 21.54/21.75      inference('sup+', [status(thm)], ['288', '289'])).
% 21.54/21.75  thf('291', plain, ((v1_relat_1 @ sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['49', '50'])).
% 21.54/21.75  thf('292', plain, ((v1_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('293', plain, ((v2_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('294', plain,
% 21.54/21.75      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 21.54/21.75      inference('demod', [status(thm)], ['290', '291', '292', '293'])).
% 21.54/21.75  thf('295', plain,
% 21.54/21.75      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 21.54/21.75      inference('demod', [status(thm)], ['287', '294'])).
% 21.54/21.75  thf('296', plain,
% 21.54/21.75      ((~ (v1_relat_1 @ sk_C)
% 21.54/21.75        | ~ (v1_funct_1 @ sk_C)
% 21.54/21.75        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['274', '295'])).
% 21.54/21.75  thf('297', plain, ((v1_relat_1 @ sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['49', '50'])).
% 21.54/21.75  thf('298', plain, ((v1_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('299', plain,
% 21.54/21.75      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 21.54/21.75      inference('demod', [status(thm)], ['296', '297', '298'])).
% 21.54/21.75  thf('300', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('simplify', [status(thm)], ['150'])).
% 21.54/21.75  thf('301', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('demod', [status(thm)], ['84', '85'])).
% 21.54/21.75  thf('302', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('simplify', [status(thm)], ['190'])).
% 21.54/21.75  thf('303', plain,
% 21.54/21.75      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 21.54/21.75         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 21.54/21.75      inference('demod', [status(thm)], ['273', '299', '300', '301', '302'])).
% 21.54/21.75  thf('304', plain,
% 21.54/21.75      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 21.54/21.75           (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)
% 21.54/21.75        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 21.54/21.75      inference('demod', [status(thm)], ['70', '303'])).
% 21.54/21.75  thf('305', plain,
% 21.54/21.75      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 21.54/21.75           sk_C)
% 21.54/21.75        | ~ (v1_relat_1 @ sk_C)
% 21.54/21.75        | ~ (v1_funct_1 @ sk_C)
% 21.54/21.75        | ~ (v2_funct_1 @ sk_C)
% 21.54/21.75        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['36', '304'])).
% 21.54/21.75  thf('306', plain,
% 21.54/21.75      ((m1_subset_1 @ sk_C @ 
% 21.54/21.75        (k1_zfmisc_1 @ 
% 21.54/21.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf(redefinition_r2_funct_2, axiom,
% 21.54/21.75    (![A:$i,B:$i,C:$i,D:$i]:
% 21.54/21.75     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 21.54/21.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 21.54/21.75         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 21.54/21.75         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.54/21.75       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 21.54/21.75  thf('307', plain,
% 21.54/21.75      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 21.54/21.75         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 21.54/21.75          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 21.54/21.75          | ~ (v1_funct_1 @ X29)
% 21.54/21.75          | ~ (v1_funct_1 @ X32)
% 21.54/21.75          | ~ (v1_funct_2 @ X32 @ X30 @ X31)
% 21.54/21.75          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 21.54/21.75          | (r2_funct_2 @ X30 @ X31 @ X29 @ X32)
% 21.54/21.75          | ((X29) != (X32)))),
% 21.54/21.75      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 21.54/21.75  thf('308', plain,
% 21.54/21.75      (![X30 : $i, X31 : $i, X32 : $i]:
% 21.54/21.75         ((r2_funct_2 @ X30 @ X31 @ X32 @ X32)
% 21.54/21.75          | ~ (v1_funct_1 @ X32)
% 21.54/21.75          | ~ (v1_funct_2 @ X32 @ X30 @ X31)
% 21.54/21.75          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 21.54/21.75      inference('simplify', [status(thm)], ['307'])).
% 21.54/21.75  thf('309', plain,
% 21.54/21.75      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 21.54/21.75        | ~ (v1_funct_1 @ sk_C)
% 21.54/21.75        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 21.54/21.75           sk_C))),
% 21.54/21.75      inference('sup-', [status(thm)], ['306', '308'])).
% 21.54/21.75  thf('310', plain,
% 21.54/21.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('311', plain, ((v1_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('312', plain,
% 21.54/21.75      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['309', '310', '311'])).
% 21.54/21.75  thf('313', plain, ((v1_relat_1 @ sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['49', '50'])).
% 21.54/21.75  thf('314', plain, ((v1_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('315', plain, ((v2_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('316', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['305', '312', '313', '314', '315'])).
% 21.54/21.75  thf('317', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['305', '312', '313', '314', '315'])).
% 21.54/21.75  thf('318', plain,
% 21.54/21.75      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ 
% 21.54/21.75          (k2_tops_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_funct_1 @ sk_C)) @ 
% 21.54/21.75          sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['35', '316', '317'])).
% 21.54/21.75  thf('319', plain,
% 21.54/21.75      (![X12 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X12)
% 21.54/21.75          | ((k2_funct_1 @ (k2_funct_1 @ X12)) = (X12))
% 21.54/21.75          | ~ (v1_funct_1 @ X12)
% 21.54/21.75          | ~ (v1_relat_1 @ X12))),
% 21.54/21.75      inference('cnf', [status(esa)], [t65_funct_1])).
% 21.54/21.75  thf('320', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 21.54/21.75      inference('sup+', [status(thm)], ['277', '278'])).
% 21.54/21.75  thf('321', plain,
% 21.54/21.75      (![X39 : $i]:
% 21.54/21.75         ((m1_subset_1 @ X39 @ 
% 21.54/21.75           (k1_zfmisc_1 @ 
% 21.54/21.75            (k2_zfmisc_1 @ (k1_relat_1 @ X39) @ (k2_relat_1 @ X39))))
% 21.54/21.75          | ~ (v1_funct_1 @ X39)
% 21.54/21.75          | ~ (v1_relat_1 @ X39))),
% 21.54/21.75      inference('cnf', [status(esa)], [t3_funct_2])).
% 21.54/21.75  thf('322', plain,
% 21.54/21.75      (((m1_subset_1 @ sk_C @ 
% 21.54/21.75         (k1_zfmisc_1 @ 
% 21.54/21.75          (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))
% 21.54/21.75        | ~ (v1_relat_1 @ sk_C)
% 21.54/21.75        | ~ (v1_funct_1 @ sk_C))),
% 21.54/21.75      inference('sup+', [status(thm)], ['320', '321'])).
% 21.54/21.75  thf('323', plain, ((v1_relat_1 @ sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['49', '50'])).
% 21.54/21.75  thf('324', plain, ((v1_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('325', plain,
% 21.54/21.75      ((m1_subset_1 @ sk_C @ 
% 21.54/21.75        (k1_zfmisc_1 @ 
% 21.54/21.75         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B))))),
% 21.54/21.75      inference('demod', [status(thm)], ['322', '323', '324'])).
% 21.54/21.75  thf('326', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['305', '312', '313', '314', '315'])).
% 21.54/21.75  thf('327', plain,
% 21.54/21.75      ((m1_subset_1 @ sk_C @ 
% 21.54/21.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ k1_xboole_0)))),
% 21.54/21.75      inference('demod', [status(thm)], ['325', '326'])).
% 21.54/21.75  thf(d1_funct_2, axiom,
% 21.54/21.75    (![A:$i,B:$i,C:$i]:
% 21.54/21.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.54/21.75       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 21.54/21.75           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 21.54/21.75             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 21.54/21.75         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 21.54/21.75           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 21.54/21.75             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 21.54/21.75  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 21.54/21.75  thf(zf_stmt_2, axiom,
% 21.54/21.75    (![C:$i,B:$i,A:$i]:
% 21.54/21.75     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 21.54/21.75       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 21.54/21.75  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 21.54/21.75  thf(zf_stmt_4, axiom,
% 21.54/21.75    (![B:$i,A:$i]:
% 21.54/21.75     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 21.54/21.75       ( zip_tseitin_0 @ B @ A ) ))).
% 21.54/21.75  thf(zf_stmt_5, axiom,
% 21.54/21.75    (![A:$i,B:$i,C:$i]:
% 21.54/21.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 21.54/21.75       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 21.54/21.75         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 21.54/21.75           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 21.54/21.75             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 21.54/21.75  thf('328', plain,
% 21.54/21.75      (![X24 : $i, X25 : $i, X26 : $i]:
% 21.54/21.75         (((X24) != (k1_xboole_0))
% 21.54/21.75          | ((X25) = (k1_xboole_0))
% 21.54/21.75          | ((X26) = (k1_xboole_0))
% 21.54/21.75          | ~ (v1_funct_2 @ X26 @ X25 @ X24)
% 21.54/21.75          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_5])).
% 21.54/21.75  thf('329', plain,
% 21.54/21.75      (![X25 : $i, X26 : $i]:
% 21.54/21.75         (~ (m1_subset_1 @ X26 @ 
% 21.54/21.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ k1_xboole_0)))
% 21.54/21.75          | ~ (v1_funct_2 @ X26 @ X25 @ k1_xboole_0)
% 21.54/21.75          | ((X26) = (k1_xboole_0))
% 21.54/21.75          | ((X25) = (k1_xboole_0)))),
% 21.54/21.75      inference('simplify', [status(thm)], ['328'])).
% 21.54/21.75  thf('330', plain,
% 21.54/21.75      ((((k1_relat_1 @ sk_C) = (k1_xboole_0))
% 21.54/21.75        | ((sk_C) = (k1_xboole_0))
% 21.54/21.75        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ k1_xboole_0))),
% 21.54/21.75      inference('sup-', [status(thm)], ['327', '329'])).
% 21.54/21.75  thf('331', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 21.54/21.75      inference('sup+', [status(thm)], ['277', '278'])).
% 21.54/21.75  thf(t4_funct_2, axiom,
% 21.54/21.75    (![A:$i,B:$i]:
% 21.54/21.75     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 21.54/21.75       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 21.54/21.75         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 21.54/21.75           ( m1_subset_1 @
% 21.54/21.75             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 21.54/21.75  thf('332', plain,
% 21.54/21.75      (![X40 : $i, X41 : $i]:
% 21.54/21.75         (~ (r1_tarski @ (k2_relat_1 @ X40) @ X41)
% 21.54/21.75          | (v1_funct_2 @ X40 @ (k1_relat_1 @ X40) @ X41)
% 21.54/21.75          | ~ (v1_funct_1 @ X40)
% 21.54/21.75          | ~ (v1_relat_1 @ X40))),
% 21.54/21.75      inference('cnf', [status(esa)], [t4_funct_2])).
% 21.54/21.75  thf('333', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (r1_tarski @ (k2_struct_0 @ sk_B) @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ sk_C)
% 21.54/21.75          | ~ (v1_funct_1 @ sk_C)
% 21.54/21.75          | (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ X0))),
% 21.54/21.75      inference('sup-', [status(thm)], ['331', '332'])).
% 21.54/21.75  thf('334', plain, ((v1_relat_1 @ sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['49', '50'])).
% 21.54/21.75  thf('335', plain, ((v1_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('336', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (r1_tarski @ (k2_struct_0 @ sk_B) @ X0)
% 21.54/21.75          | (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ X0))),
% 21.54/21.75      inference('demod', [status(thm)], ['333', '334', '335'])).
% 21.54/21.75  thf('337', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['305', '312', '313', '314', '315'])).
% 21.54/21.75  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 21.54/21.75  thf('338', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 21.54/21.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 21.54/21.75  thf('339', plain,
% 21.54/21.75      (![X0 : $i]: (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ X0)),
% 21.54/21.75      inference('demod', [status(thm)], ['336', '337', '338'])).
% 21.54/21.75  thf('340', plain,
% 21.54/21.75      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 21.54/21.75      inference('demod', [status(thm)], ['330', '339'])).
% 21.54/21.75  thf('341', plain,
% 21.54/21.75      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 21.54/21.75         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 21.54/21.75      inference('demod', [status(thm)], ['273', '299', '300', '301', '302'])).
% 21.54/21.75  thf('342', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['305', '312', '313', '314', '315'])).
% 21.54/21.75  thf('343', plain,
% 21.54/21.75      (((k2_tops_2 @ k1_xboole_0 @ (k1_relat_1 @ sk_C) @ (k2_funct_1 @ sk_C))
% 21.54/21.75         = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 21.54/21.75      inference('demod', [status(thm)], ['341', '342'])).
% 21.54/21.75  thf('344', plain,
% 21.54/21.75      ((((k2_tops_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_funct_1 @ sk_C))
% 21.54/21.75          = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 21.54/21.75        | ((sk_C) = (k1_xboole_0)))),
% 21.54/21.75      inference('sup+', [status(thm)], ['340', '343'])).
% 21.54/21.75  thf('345', plain,
% 21.54/21.75      ((m1_subset_1 @ sk_C @ 
% 21.54/21.75        (k1_zfmisc_1 @ 
% 21.54/21.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 21.54/21.75      inference('demod', [status(thm)], ['13', '14'])).
% 21.54/21.75  thf('346', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['305', '312', '313', '314', '315'])).
% 21.54/21.75  thf('347', plain,
% 21.54/21.75      ((m1_subset_1 @ sk_C @ 
% 21.54/21.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)))),
% 21.54/21.75      inference('demod', [status(thm)], ['345', '346'])).
% 21.54/21.75  thf('348', plain,
% 21.54/21.75      (![X25 : $i, X26 : $i]:
% 21.54/21.75         (~ (m1_subset_1 @ X26 @ 
% 21.54/21.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ k1_xboole_0)))
% 21.54/21.75          | ~ (v1_funct_2 @ X26 @ X25 @ k1_xboole_0)
% 21.54/21.75          | ((X26) = (k1_xboole_0))
% 21.54/21.75          | ((X25) = (k1_xboole_0)))),
% 21.54/21.75      inference('simplify', [status(thm)], ['328'])).
% 21.54/21.75  thf('349', plain,
% 21.54/21.75      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 21.54/21.75        | ((sk_C) = (k1_xboole_0))
% 21.54/21.75        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 21.54/21.75      inference('sup-', [status(thm)], ['347', '348'])).
% 21.54/21.75  thf('350', plain,
% 21.54/21.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 21.54/21.75      inference('demod', [status(thm)], ['21', '22'])).
% 21.54/21.75  thf('351', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['305', '312', '313', '314', '315'])).
% 21.54/21.75  thf('352', plain, ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ k1_xboole_0)),
% 21.54/21.75      inference('demod', [status(thm)], ['350', '351'])).
% 21.54/21.75  thf('353', plain,
% 21.54/21.75      ((((u1_struct_0 @ sk_A) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 21.54/21.75      inference('demod', [status(thm)], ['349', '352'])).
% 21.54/21.75  thf('354', plain,
% 21.54/21.75      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 21.54/21.75          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75           (k2_funct_1 @ sk_C)) @ 
% 21.54/21.75          sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['67', '68'])).
% 21.54/21.75  thf('355', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['305', '312', '313', '314', '315'])).
% 21.54/21.75  thf('356', plain,
% 21.54/21.75      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 21.54/21.75          (k2_tops_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_funct_1 @ sk_C)) @ 
% 21.54/21.75          sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['354', '355'])).
% 21.54/21.75  thf('357', plain,
% 21.54/21.75      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 21.54/21.75           (k2_tops_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_funct_1 @ sk_C)) @ sk_C)
% 21.54/21.75        | ((sk_C) = (k1_xboole_0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['353', '356'])).
% 21.54/21.75  thf('358', plain,
% 21.54/21.75      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 21.54/21.75           (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)
% 21.54/21.75        | ((sk_C) = (k1_xboole_0))
% 21.54/21.75        | ((sk_C) = (k1_xboole_0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['344', '357'])).
% 21.54/21.75  thf('359', plain,
% 21.54/21.75      ((((sk_C) = (k1_xboole_0))
% 21.54/21.75        | ~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 21.54/21.75             (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C))),
% 21.54/21.75      inference('simplify', [status(thm)], ['358'])).
% 21.54/21.75  thf('360', plain,
% 21.54/21.75      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 21.54/21.75           sk_C)
% 21.54/21.75        | ~ (v1_relat_1 @ sk_C)
% 21.54/21.75        | ~ (v1_funct_1 @ sk_C)
% 21.54/21.75        | ~ (v2_funct_1 @ sk_C)
% 21.54/21.75        | ((sk_C) = (k1_xboole_0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['319', '359'])).
% 21.54/21.75  thf('361', plain,
% 21.54/21.75      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['309', '310', '311'])).
% 21.54/21.75  thf('362', plain, ((v1_relat_1 @ sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['49', '50'])).
% 21.54/21.75  thf('363', plain, ((v1_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('364', plain, ((v2_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('365', plain, (((sk_C) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['360', '361', '362', '363', '364'])).
% 21.54/21.75  thf('366', plain, (((sk_C) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['360', '361', '362', '363', '364'])).
% 21.54/21.75  thf('367', plain,
% 21.54/21.75      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ 
% 21.54/21.75          (k2_tops_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75           (k2_funct_1 @ k1_xboole_0)) @ 
% 21.54/21.75          k1_xboole_0)),
% 21.54/21.75      inference('demod', [status(thm)], ['318', '365', '366'])).
% 21.54/21.75  thf('368', plain,
% 21.54/21.75      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 21.54/21.75        (k1_zfmisc_1 @ 
% 21.54/21.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 21.54/21.75      inference('simplify', [status(thm)], ['81'])).
% 21.54/21.75  thf(dt_k2_tops_2, axiom,
% 21.54/21.75    (![A:$i,B:$i,C:$i]:
% 21.54/21.75     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 21.54/21.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 21.54/21.75       ( ( v1_funct_1 @ ( k2_tops_2 @ A @ B @ C ) ) & 
% 21.54/21.75         ( v1_funct_2 @ ( k2_tops_2 @ A @ B @ C ) @ B @ A ) & 
% 21.54/21.75         ( m1_subset_1 @
% 21.54/21.75           ( k2_tops_2 @ A @ B @ C ) @ 
% 21.54/21.75           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ))).
% 21.54/21.75  thf('369', plain,
% 21.54/21.75      (![X46 : $i, X47 : $i, X48 : $i]:
% 21.54/21.75         ((m1_subset_1 @ (k2_tops_2 @ X46 @ X47 @ X48) @ 
% 21.54/21.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))
% 21.54/21.75          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 21.54/21.75          | ~ (v1_funct_2 @ X48 @ X46 @ X47)
% 21.54/21.75          | ~ (v1_funct_1 @ X48))),
% 21.54/21.75      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 21.54/21.75  thf('370', plain,
% 21.54/21.75      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 21.54/21.75             (u1_struct_0 @ sk_A))
% 21.54/21.75        | (m1_subset_1 @ 
% 21.54/21.75           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75            (k2_funct_1 @ sk_C)) @ 
% 21.54/21.75           (k1_zfmisc_1 @ 
% 21.54/21.75            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))))),
% 21.54/21.75      inference('sup-', [status(thm)], ['368', '369'])).
% 21.54/21.75  thf('371', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('simplify', [status(thm)], ['150'])).
% 21.54/21.75  thf('372', plain,
% 21.54/21.75      ((m1_subset_1 @ sk_C @ 
% 21.54/21.75        (k1_zfmisc_1 @ 
% 21.54/21.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 21.54/21.75      inference('demod', [status(thm)], ['13', '14'])).
% 21.54/21.75  thf('373', plain,
% 21.54/21.75      (![X36 : $i, X37 : $i, X38 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X36)
% 21.54/21.75          | ((k2_relset_1 @ X38 @ X37 @ X36) != (X37))
% 21.54/21.75          | (v1_funct_2 @ (k2_funct_1 @ X36) @ X37 @ X38)
% 21.54/21.75          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 21.54/21.75          | ~ (v1_funct_2 @ X36 @ X38 @ X37)
% 21.54/21.75          | ~ (v1_funct_1 @ X36))),
% 21.54/21.75      inference('cnf', [status(esa)], [t31_funct_2])).
% 21.54/21.75  thf('374', plain,
% 21.54/21.75      ((~ (v1_funct_1 @ sk_C)
% 21.54/21.75        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 21.54/21.75        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 21.54/21.75           (u1_struct_0 @ sk_A))
% 21.54/21.75        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 21.54/21.75            != (k2_struct_0 @ sk_B))
% 21.54/21.75        | ~ (v2_funct_1 @ sk_C))),
% 21.54/21.75      inference('sup-', [status(thm)], ['372', '373'])).
% 21.54/21.75  thf('375', plain, ((v1_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('376', plain,
% 21.54/21.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 21.54/21.75      inference('demod', [status(thm)], ['21', '22'])).
% 21.54/21.75  thf('377', plain,
% 21.54/21.75      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 21.54/21.75         = (k2_struct_0 @ sk_B))),
% 21.54/21.75      inference('demod', [status(thm)], ['27', '28'])).
% 21.54/21.75  thf('378', plain, ((v2_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('379', plain,
% 21.54/21.75      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 21.54/21.75         (u1_struct_0 @ sk_A))
% 21.54/21.75        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 21.54/21.75      inference('demod', [status(thm)], ['374', '375', '376', '377', '378'])).
% 21.54/21.75  thf('380', plain,
% 21.54/21.75      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 21.54/21.75        (u1_struct_0 @ sk_A))),
% 21.54/21.75      inference('simplify', [status(thm)], ['379'])).
% 21.54/21.75  thf('381', plain,
% 21.54/21.75      ((m1_subset_1 @ 
% 21.54/21.75        (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75         (k2_funct_1 @ sk_C)) @ 
% 21.54/21.75        (k1_zfmisc_1 @ 
% 21.54/21.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 21.54/21.75      inference('demod', [status(thm)], ['370', '371', '380'])).
% 21.54/21.75  thf('382', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['305', '312', '313', '314', '315'])).
% 21.54/21.75  thf('383', plain, (((sk_C) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['360', '361', '362', '363', '364'])).
% 21.54/21.75  thf('384', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['305', '312', '313', '314', '315'])).
% 21.54/21.75  thf('385', plain,
% 21.54/21.75      ((m1_subset_1 @ 
% 21.54/21.75        (k2_tops_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75         (k2_funct_1 @ k1_xboole_0)) @ 
% 21.54/21.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)))),
% 21.54/21.75      inference('demod', [status(thm)], ['381', '382', '383', '384'])).
% 21.54/21.75  thf('386', plain,
% 21.54/21.75      (![X25 : $i, X26 : $i]:
% 21.54/21.75         (~ (m1_subset_1 @ X26 @ 
% 21.54/21.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ k1_xboole_0)))
% 21.54/21.75          | ~ (v1_funct_2 @ X26 @ X25 @ k1_xboole_0)
% 21.54/21.75          | ((X26) = (k1_xboole_0))
% 21.54/21.75          | ((X25) = (k1_xboole_0)))),
% 21.54/21.75      inference('simplify', [status(thm)], ['328'])).
% 21.54/21.75  thf('387', plain,
% 21.54/21.75      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 21.54/21.75        | ((k2_tops_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75            (k2_funct_1 @ k1_xboole_0)) = (k1_xboole_0))
% 21.54/21.75        | ~ (v1_funct_2 @ 
% 21.54/21.75             (k2_tops_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75              (k2_funct_1 @ k1_xboole_0)) @ 
% 21.54/21.75             (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 21.54/21.75      inference('sup-', [status(thm)], ['385', '386'])).
% 21.54/21.75  thf('388', plain,
% 21.54/21.75      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 21.54/21.75        (k1_zfmisc_1 @ 
% 21.54/21.75         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 21.54/21.75      inference('simplify', [status(thm)], ['81'])).
% 21.54/21.75  thf('389', plain,
% 21.54/21.75      (![X46 : $i, X47 : $i, X48 : $i]:
% 21.54/21.75         ((v1_funct_2 @ (k2_tops_2 @ X46 @ X47 @ X48) @ X47 @ X46)
% 21.54/21.75          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 21.54/21.75          | ~ (v1_funct_2 @ X48 @ X46 @ X47)
% 21.54/21.75          | ~ (v1_funct_1 @ X48))),
% 21.54/21.75      inference('cnf', [status(esa)], [dt_k2_tops_2])).
% 21.54/21.75  thf('390', plain,
% 21.54/21.75      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 21.54/21.75             (u1_struct_0 @ sk_A))
% 21.54/21.75        | (v1_funct_2 @ 
% 21.54/21.75           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75            (k2_funct_1 @ sk_C)) @ 
% 21.54/21.75           (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['388', '389'])).
% 21.54/21.75  thf('391', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('simplify', [status(thm)], ['150'])).
% 21.54/21.75  thf('392', plain,
% 21.54/21.75      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 21.54/21.75        (u1_struct_0 @ sk_A))),
% 21.54/21.75      inference('simplify', [status(thm)], ['379'])).
% 21.54/21.75  thf('393', plain,
% 21.54/21.75      ((v1_funct_2 @ 
% 21.54/21.75        (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75         (k2_funct_1 @ sk_C)) @ 
% 21.54/21.75        (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 21.54/21.75      inference('demod', [status(thm)], ['390', '391', '392'])).
% 21.54/21.75  thf('394', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['305', '312', '313', '314', '315'])).
% 21.54/21.75  thf('395', plain, (((sk_C) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['360', '361', '362', '363', '364'])).
% 21.54/21.75  thf('396', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['305', '312', '313', '314', '315'])).
% 21.54/21.75  thf('397', plain,
% 21.54/21.75      ((v1_funct_2 @ 
% 21.54/21.75        (k2_tops_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75         (k2_funct_1 @ k1_xboole_0)) @ 
% 21.54/21.75        (u1_struct_0 @ sk_A) @ k1_xboole_0)),
% 21.54/21.75      inference('demod', [status(thm)], ['393', '394', '395', '396'])).
% 21.54/21.75  thf('398', plain,
% 21.54/21.75      ((((u1_struct_0 @ sk_A) = (k1_xboole_0))
% 21.54/21.75        | ((k2_tops_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75            (k2_funct_1 @ k1_xboole_0)) = (k1_xboole_0)))),
% 21.54/21.75      inference('demod', [status(thm)], ['387', '397'])).
% 21.54/21.75  thf('399', plain,
% 21.54/21.75      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ 
% 21.54/21.75          (k2_tops_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 21.54/21.75           (k2_funct_1 @ k1_xboole_0)) @ 
% 21.54/21.75          k1_xboole_0)),
% 21.54/21.75      inference('demod', [status(thm)], ['318', '365', '366'])).
% 21.54/21.75  thf('400', plain,
% 21.54/21.75      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ k1_xboole_0 @ 
% 21.54/21.75           k1_xboole_0)
% 21.54/21.75        | ((u1_struct_0 @ sk_A) = (k1_xboole_0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['398', '399'])).
% 21.54/21.75  thf('401', plain,
% 21.54/21.75      ((m1_subset_1 @ sk_C @ 
% 21.54/21.75        (k1_zfmisc_1 @ 
% 21.54/21.75         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 21.54/21.75      inference('demod', [status(thm)], ['13', '14'])).
% 21.54/21.75  thf('402', plain,
% 21.54/21.75      (![X30 : $i, X31 : $i, X32 : $i]:
% 21.54/21.75         ((r2_funct_2 @ X30 @ X31 @ X32 @ X32)
% 21.54/21.75          | ~ (v1_funct_1 @ X32)
% 21.54/21.75          | ~ (v1_funct_2 @ X32 @ X30 @ X31)
% 21.54/21.75          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 21.54/21.75      inference('simplify', [status(thm)], ['307'])).
% 21.54/21.75  thf('403', plain,
% 21.54/21.75      ((~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 21.54/21.75        | ~ (v1_funct_1 @ sk_C)
% 21.54/21.75        | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ 
% 21.54/21.75           sk_C))),
% 21.54/21.75      inference('sup-', [status(thm)], ['401', '402'])).
% 21.54/21.75  thf('404', plain,
% 21.54/21.75      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 21.54/21.75      inference('demod', [status(thm)], ['21', '22'])).
% 21.54/21.75  thf('405', plain, ((v1_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('406', plain,
% 21.54/21.75      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['403', '404', '405'])).
% 21.54/21.75  thf('407', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['305', '312', '313', '314', '315'])).
% 21.54/21.75  thf('408', plain,
% 21.54/21.75      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ sk_C @ sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['406', '407'])).
% 21.54/21.75  thf('409', plain, (((sk_C) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['360', '361', '362', '363', '364'])).
% 21.54/21.75  thf('410', plain, (((sk_C) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['360', '361', '362', '363', '364'])).
% 21.54/21.75  thf('411', plain,
% 21.54/21.75      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ k1_xboole_0 @ 
% 21.54/21.75        k1_xboole_0)),
% 21.54/21.75      inference('demod', [status(thm)], ['408', '409', '410'])).
% 21.54/21.75  thf('412', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['400', '411'])).
% 21.54/21.75  thf('413', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['400', '411'])).
% 21.54/21.75  thf('414', plain,
% 21.54/21.75      (~ (r2_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ 
% 21.54/21.75          (k2_tops_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_funct_1 @ k1_xboole_0)) @ 
% 21.54/21.75          k1_xboole_0)),
% 21.54/21.75      inference('demod', [status(thm)], ['367', '412', '413'])).
% 21.54/21.75  thf('415', plain,
% 21.54/21.75      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 21.54/21.75      inference('demod', [status(thm)], ['296', '297', '298'])).
% 21.54/21.75  thf('416', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['305', '312', '313', '314', '315'])).
% 21.54/21.75  thf('417', plain, (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['415', '416'])).
% 21.54/21.75  thf('418', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v2_funct_1 @ X0)
% 21.54/21.75          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 21.54/21.75              = (k2_funct_1 @ X0))
% 21.54/21.75          | ~ (v1_relat_1 @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ X0))),
% 21.54/21.75      inference('simplify', [status(thm)], ['271'])).
% 21.54/21.75  thf('419', plain,
% 21.54/21.75      ((((k2_tops_2 @ k1_xboole_0 @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 21.54/21.75          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 21.54/21.75        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 21.54/21.75        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 21.54/21.75      inference('sup+', [status(thm)], ['417', '418'])).
% 21.54/21.75  thf('420', plain,
% 21.54/21.75      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 21.54/21.75      inference('demod', [status(thm)], ['256', '257', '258', '259'])).
% 21.54/21.75  thf('421', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('simplify', [status(thm)], ['150'])).
% 21.54/21.75  thf('422', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('demod', [status(thm)], ['84', '85'])).
% 21.54/21.75  thf('423', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 21.54/21.75      inference('simplify', [status(thm)], ['190'])).
% 21.54/21.75  thf('424', plain,
% 21.54/21.75      (((k2_tops_2 @ k1_xboole_0 @ (k1_relat_1 @ sk_C) @ (k2_funct_1 @ sk_C))
% 21.54/21.75         = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 21.54/21.75      inference('demod', [status(thm)], ['419', '420', '421', '422', '423'])).
% 21.54/21.75  thf('425', plain, (((sk_C) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['360', '361', '362', '363', '364'])).
% 21.54/21.75  thf('426', plain, (((sk_C) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['360', '361', '362', '363', '364'])).
% 21.54/21.75  thf('427', plain, (((sk_C) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['360', '361', '362', '363', '364'])).
% 21.54/21.75  thf('428', plain,
% 21.54/21.75      (((k2_tops_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 21.54/21.75         (k2_funct_1 @ k1_xboole_0))
% 21.54/21.75         = (k2_funct_1 @ (k2_funct_1 @ k1_xboole_0)))),
% 21.54/21.75      inference('demod', [status(thm)], ['424', '425', '426', '427'])).
% 21.54/21.75  thf('429', plain,
% 21.54/21.75      ((m1_subset_1 @ sk_C @ 
% 21.54/21.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)))),
% 21.54/21.75      inference('demod', [status(thm)], ['345', '346'])).
% 21.54/21.75  thf('430', plain, (((sk_C) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['360', '361', '362', '363', '364'])).
% 21.54/21.75  thf('431', plain,
% 21.54/21.75      ((m1_subset_1 @ k1_xboole_0 @ 
% 21.54/21.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)))),
% 21.54/21.75      inference('demod', [status(thm)], ['429', '430'])).
% 21.54/21.75  thf('432', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['400', '411'])).
% 21.54/21.75  thf('433', plain,
% 21.54/21.75      ((m1_subset_1 @ k1_xboole_0 @ 
% 21.54/21.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 21.54/21.75      inference('demod', [status(thm)], ['431', '432'])).
% 21.54/21.75  thf('434', plain,
% 21.54/21.75      (![X33 : $i, X34 : $i, X35 : $i]:
% 21.54/21.75         (((X35) != (k1_xboole_0))
% 21.54/21.75          | ~ (v1_funct_1 @ X34)
% 21.54/21.75          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X33)))
% 21.54/21.75          | (v1_partfun1 @ X34 @ X35)
% 21.54/21.75          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X33)))
% 21.54/21.75          | ~ (v1_funct_2 @ X34 @ X35 @ X33)
% 21.54/21.75          | ~ (v1_funct_1 @ X34))),
% 21.54/21.75      inference('cnf', [status(esa)], [t132_funct_2])).
% 21.54/21.75  thf('435', plain,
% 21.54/21.75      (![X33 : $i, X34 : $i]:
% 21.54/21.75         (~ (v1_funct_2 @ X34 @ k1_xboole_0 @ X33)
% 21.54/21.75          | (v1_partfun1 @ X34 @ k1_xboole_0)
% 21.54/21.75          | ~ (m1_subset_1 @ X34 @ 
% 21.54/21.75               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X33)))
% 21.54/21.75          | ~ (v1_funct_1 @ X34))),
% 21.54/21.75      inference('simplify', [status(thm)], ['434'])).
% 21.54/21.75  thf('436', plain,
% 21.54/21.75      ((~ (v1_funct_1 @ k1_xboole_0)
% 21.54/21.75        | (v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)
% 21.54/21.75        | ~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 21.54/21.75      inference('sup-', [status(thm)], ['433', '435'])).
% 21.54/21.75  thf('437', plain, ((v1_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('438', plain, (((sk_C) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['360', '361', '362', '363', '364'])).
% 21.54/21.75  thf('439', plain, ((v1_funct_1 @ k1_xboole_0)),
% 21.54/21.75      inference('demod', [status(thm)], ['437', '438'])).
% 21.54/21.75  thf('440', plain, ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ k1_xboole_0)),
% 21.54/21.75      inference('demod', [status(thm)], ['350', '351'])).
% 21.54/21.75  thf('441', plain, (((sk_C) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['360', '361', '362', '363', '364'])).
% 21.54/21.75  thf('442', plain,
% 21.54/21.75      ((v1_funct_2 @ k1_xboole_0 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)),
% 21.54/21.75      inference('demod', [status(thm)], ['440', '441'])).
% 21.54/21.75  thf('443', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['400', '411'])).
% 21.54/21.75  thf('444', plain, ((v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 21.54/21.75      inference('demod', [status(thm)], ['442', '443'])).
% 21.54/21.75  thf('445', plain, ((v1_partfun1 @ k1_xboole_0 @ k1_xboole_0)),
% 21.54/21.75      inference('demod', [status(thm)], ['436', '439', '444'])).
% 21.54/21.75  thf('446', plain,
% 21.54/21.75      (![X27 : $i, X28 : $i]:
% 21.54/21.75         (~ (v1_partfun1 @ X28 @ X27)
% 21.54/21.75          | ((k1_relat_1 @ X28) = (X27))
% 21.54/21.75          | ~ (v4_relat_1 @ X28 @ X27)
% 21.54/21.75          | ~ (v1_relat_1 @ X28))),
% 21.54/21.75      inference('cnf', [status(esa)], [d4_partfun1])).
% 21.54/21.75  thf('447', plain,
% 21.54/21.75      ((~ (v1_relat_1 @ k1_xboole_0)
% 21.54/21.75        | ~ (v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 21.54/21.75        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 21.54/21.75      inference('sup-', [status(thm)], ['445', '446'])).
% 21.54/21.75  thf('448', plain, ((v1_relat_1 @ sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['49', '50'])).
% 21.54/21.75  thf('449', plain, (((sk_C) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['360', '361', '362', '363', '364'])).
% 21.54/21.75  thf('450', plain, ((v1_relat_1 @ k1_xboole_0)),
% 21.54/21.75      inference('demod', [status(thm)], ['448', '449'])).
% 21.54/21.75  thf('451', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 21.54/21.75      inference('sup-', [status(thm)], ['52', '53'])).
% 21.54/21.75  thf('452', plain, (((sk_C) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['360', '361', '362', '363', '364'])).
% 21.54/21.75  thf('453', plain, ((v4_relat_1 @ k1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 21.54/21.75      inference('demod', [status(thm)], ['451', '452'])).
% 21.54/21.75  thf('454', plain, (((u1_struct_0 @ sk_A) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['400', '411'])).
% 21.54/21.75  thf('455', plain, ((v4_relat_1 @ k1_xboole_0 @ k1_xboole_0)),
% 21.54/21.75      inference('demod', [status(thm)], ['453', '454'])).
% 21.54/21.75  thf('456', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['447', '450', '455'])).
% 21.54/21.75  thf('457', plain,
% 21.54/21.75      (((k2_tops_2 @ k1_xboole_0 @ k1_xboole_0 @ (k2_funct_1 @ k1_xboole_0))
% 21.54/21.75         = (k2_funct_1 @ (k2_funct_1 @ k1_xboole_0)))),
% 21.54/21.75      inference('demod', [status(thm)], ['428', '456'])).
% 21.54/21.75  thf('458', plain,
% 21.54/21.75      (~ (r2_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ 
% 21.54/21.75          (k2_funct_1 @ (k2_funct_1 @ k1_xboole_0)) @ k1_xboole_0)),
% 21.54/21.75      inference('demod', [status(thm)], ['414', '457'])).
% 21.54/21.75  thf('459', plain,
% 21.54/21.75      ((~ (r2_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 21.54/21.75        | ~ (v1_relat_1 @ k1_xboole_0)
% 21.54/21.75        | ~ (v1_funct_1 @ k1_xboole_0)
% 21.54/21.75        | ~ (v2_funct_1 @ k1_xboole_0))),
% 21.54/21.75      inference('sup-', [status(thm)], ['0', '458'])).
% 21.54/21.75  thf('460', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 21.54/21.75      inference('sup+', [status(thm)], ['277', '278'])).
% 21.54/21.75  thf('461', plain,
% 21.54/21.75      (![X40 : $i, X41 : $i]:
% 21.54/21.75         (~ (r1_tarski @ (k2_relat_1 @ X40) @ X41)
% 21.54/21.75          | (m1_subset_1 @ X40 @ 
% 21.54/21.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X40) @ X41)))
% 21.54/21.75          | ~ (v1_funct_1 @ X40)
% 21.54/21.75          | ~ (v1_relat_1 @ X40))),
% 21.54/21.75      inference('cnf', [status(esa)], [t4_funct_2])).
% 21.54/21.75  thf('462', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (r1_tarski @ (k2_struct_0 @ sk_B) @ X0)
% 21.54/21.75          | ~ (v1_relat_1 @ sk_C)
% 21.54/21.75          | ~ (v1_funct_1 @ sk_C)
% 21.54/21.75          | (m1_subset_1 @ sk_C @ 
% 21.54/21.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ X0))))),
% 21.54/21.75      inference('sup-', [status(thm)], ['460', '461'])).
% 21.54/21.75  thf('463', plain, ((v1_relat_1 @ sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['49', '50'])).
% 21.54/21.75  thf('464', plain, ((v1_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('465', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (r1_tarski @ (k2_struct_0 @ sk_B) @ X0)
% 21.54/21.75          | (m1_subset_1 @ sk_C @ 
% 21.54/21.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ X0))))),
% 21.54/21.75      inference('demod', [status(thm)], ['462', '463', '464'])).
% 21.54/21.75  thf('466', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['305', '312', '313', '314', '315'])).
% 21.54/21.75  thf('467', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 21.54/21.75      inference('cnf', [status(esa)], [t2_xboole_1])).
% 21.54/21.75  thf('468', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (m1_subset_1 @ sk_C @ 
% 21.54/21.75          (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ X0)))),
% 21.54/21.75      inference('demod', [status(thm)], ['465', '466', '467'])).
% 21.54/21.75  thf('469', plain,
% 21.54/21.75      (![X30 : $i, X31 : $i, X32 : $i]:
% 21.54/21.75         ((r2_funct_2 @ X30 @ X31 @ X32 @ X32)
% 21.54/21.75          | ~ (v1_funct_1 @ X32)
% 21.54/21.75          | ~ (v1_funct_2 @ X32 @ X30 @ X31)
% 21.54/21.75          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 21.54/21.75      inference('simplify', [status(thm)], ['307'])).
% 21.54/21.75  thf('470', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ X0)
% 21.54/21.75          | ~ (v1_funct_1 @ sk_C)
% 21.54/21.75          | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ X0 @ sk_C @ sk_C))),
% 21.54/21.75      inference('sup-', [status(thm)], ['468', '469'])).
% 21.54/21.75  thf('471', plain,
% 21.54/21.75      (![X0 : $i]: (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ X0)),
% 21.54/21.75      inference('demod', [status(thm)], ['336', '337', '338'])).
% 21.54/21.75  thf('472', plain, ((v1_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('473', plain,
% 21.54/21.75      (![X0 : $i]: (r2_funct_2 @ (k1_relat_1 @ sk_C) @ X0 @ sk_C @ sk_C)),
% 21.54/21.75      inference('demod', [status(thm)], ['470', '471', '472'])).
% 21.54/21.75  thf('474', plain, (((sk_C) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['360', '361', '362', '363', '364'])).
% 21.54/21.75  thf('475', plain, (((sk_C) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['360', '361', '362', '363', '364'])).
% 21.54/21.75  thf('476', plain, (((sk_C) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['360', '361', '362', '363', '364'])).
% 21.54/21.75  thf('477', plain,
% 21.54/21.75      (![X0 : $i]:
% 21.54/21.75         (r2_funct_2 @ (k1_relat_1 @ k1_xboole_0) @ X0 @ k1_xboole_0 @ 
% 21.54/21.75          k1_xboole_0)),
% 21.54/21.75      inference('demod', [status(thm)], ['473', '474', '475', '476'])).
% 21.54/21.75  thf('478', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['447', '450', '455'])).
% 21.54/21.75  thf('479', plain,
% 21.54/21.75      (![X0 : $i]: (r2_funct_2 @ k1_xboole_0 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 21.54/21.75      inference('demod', [status(thm)], ['477', '478'])).
% 21.54/21.75  thf('480', plain, ((v1_relat_1 @ k1_xboole_0)),
% 21.54/21.75      inference('demod', [status(thm)], ['448', '449'])).
% 21.54/21.75  thf('481', plain, ((v1_funct_1 @ k1_xboole_0)),
% 21.54/21.75      inference('demod', [status(thm)], ['437', '438'])).
% 21.54/21.75  thf('482', plain, ((v2_funct_1 @ sk_C)),
% 21.54/21.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.54/21.75  thf('483', plain, (((sk_C) = (k1_xboole_0))),
% 21.54/21.75      inference('demod', [status(thm)], ['360', '361', '362', '363', '364'])).
% 21.54/21.75  thf('484', plain, ((v2_funct_1 @ k1_xboole_0)),
% 21.54/21.75      inference('demod', [status(thm)], ['482', '483'])).
% 21.54/21.75  thf('485', plain, ($false),
% 21.54/21.75      inference('demod', [status(thm)], ['459', '479', '480', '481', '484'])).
% 21.54/21.75  
% 21.54/21.75  % SZS output end Refutation
% 21.54/21.75  
% 21.54/21.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
