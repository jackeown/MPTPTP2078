%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gfERhhnHBc

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:09 EST 2020

% Result     : Theorem 6.62s
% Output     : Refutation 6.62s
% Verified   : 
% Statistics : Number of formulae       :  384 (2913 expanded)
%              Number of leaves         :   49 ( 851 expanded)
%              Depth                    :   76
%              Number of atoms          : 4277 (59191 expanded)
%              Number of equality atoms :  232 (2197 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
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
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_relset_1 @ X35 @ X34 @ X36 )
       != X34 )
      | ~ ( v2_funct_1 @ X36 )
      | ( ( k2_tops_2 @ X35 @ X34 @ X36 )
        = ( k2_funct_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
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
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
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
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
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
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['10','31'])).

thf('33',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('38',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('39',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_relset_1 @ X35 @ X34 @ X36 )
       != X34 )
      | ~ ( v2_funct_1 @ X36 )
      | ( ( k2_tops_2 @ X35 @ X34 @ X36 )
        = ( k2_funct_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('50',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('52',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('53',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('56',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('57',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X29 ) @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('63',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('74',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('76',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('77',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('80',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('81',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['77','78','79','80','81'])).

thf('83',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('84',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('85',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('87',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('88',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('89',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
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

thf('92',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X6 ) @ X6 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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

thf('93',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v2_funct_1 @ X3 )
      | ( ( k2_relat_1 @ X3 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('94',plain,(
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
    inference('sup-',[status(thm)],['92','93'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('95',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('96',plain,(
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
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
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
    inference('sup-',[status(thm)],['91','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['90','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
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
    inference('sup-',[status(thm)],['89','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('106',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('110',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ X6 @ ( k2_funct_1 @ X6 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('114',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('118',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('122',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('123',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X6 ) @ X6 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['122','123'])).

thf('125',plain,(
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
    inference('sup-',[status(thm)],['121','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['120','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['119','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['118','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['117','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['116','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['115','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['114','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['113','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['112','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['111','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['110','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['109','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['108','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['107','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['106','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['105','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['104','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['103','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v2_funct_1 @ X3 )
      | ( ( k2_relat_1 @ X3 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['88','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['87','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['86','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['85','172'])).

thf('174',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('175',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('176',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('177',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['176','177'])).

thf('179',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('180',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('181',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['178','181'])).

thf('183',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('185',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('187',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('188',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['185','188'])).

thf('190',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['182','189'])).

thf('191',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['175','190'])).

thf('192',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['191','192'])).

thf('194',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['174','193'])).

thf('195',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('197',plain,(
    ! [X33: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('198',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['200','201'])).

thf('203',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('205',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['58'])).

thf('209',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['173','202','205','206','207','208'])).

thf('210',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['74','209'])).

thf('211',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['200','201'])).

thf('212',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['203','204'])).

thf('213',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['210','211','212','213','214'])).

thf('216',plain,(
    v2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['73','216'])).

thf('218',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['203','204'])).

thf('219',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['217','218','219','220'])).

thf('222',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','59','72','221'])).

thf('223',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('224',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('225',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('226',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 = X0 )
      | ( zip_tseitin_0 @ X0 @ X3 )
      | ( zip_tseitin_0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['224','225'])).

thf('227',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('228',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( ( u1_struct_0 @ sk_B )
        = X1 )
      | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['185','188'])).

thf('230',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['200','201'])).

thf('231',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['229','230'])).

thf('232',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( zip_tseitin_0 @ X0 @ X1 )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['228','231'])).

thf('233',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_struct_0 @ sk_B )
        = X0 )
      | ~ ( l1_struct_0 @ sk_B )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['223','232'])).

thf('234',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_struct_0 @ sk_B )
        = X0 )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X33: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 )
      | ( v2_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('237',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['237','238'])).

thf('240',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('241',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('242',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('243',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['185','188'])).

thf('245',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['243','244'])).

thf('246',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['200','201'])).

thf('247',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['245','246'])).

thf('248',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('249',plain,
    ( ~ ( zip_tseitin_0 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['247','248'])).

thf('250',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['229','230'])).

thf('251',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['249','250'])).

thf('252',plain,
    ( ~ ( zip_tseitin_0 @ k1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['240','251'])).

thf('253',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( ~ ( zip_tseitin_0 @ k1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['252','253'])).

thf('255',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['239','254'])).

thf('256',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('257',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['255','256'])).

thf('258',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['257'])).

thf('259',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['258','259'])).

thf('261',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['258','259'])).

thf('262',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('263',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('264',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['262','263'])).

thf('265',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['264','265'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('267',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('268',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['266','267'])).

thf('269',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('270',plain,(
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X7 ) )
        = X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('271',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('272',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('273',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('274',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('275',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['273','274'])).

thf('276',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['58'])).

thf('277',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['71'])).

thf('278',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['217','218','219','220'])).

thf('279',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['275','276','277','278'])).

thf('280',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('281',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('282',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['280','281'])).

thf('283',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['279','282'])).

thf('284',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['272','283'])).

thf('285',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['200','201'])).

thf('286',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['203','204'])).

thf('287',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('288',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('289',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['284','285','286','287','288'])).

thf('290',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['271','289'])).

thf('291',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['290','291'])).

thf('293',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['292'])).

thf('294',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('295',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['293','294'])).

thf('296',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['270','295'])).

thf('297',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('298',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['200','201'])).

thf('299',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['297','298'])).

thf('300',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['203','204'])).

thf('301',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('302',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('303',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['296','299','300','301','302'])).

thf('304',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['269','303'])).

thf('305',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('306',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['58'])).

thf('307',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['217','218','219','220'])).

thf('308',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['304','305','306','307'])).

thf('309',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['268','308'])).

thf('310',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['258','259'])).

thf('311',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['222','260','261','309','310'])).

thf('312',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['311'])).

thf('313',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['35','312'])).

thf('314',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','313'])).

thf('315',plain,(
    ! [X32: $i] :
      ( ( ( k2_struct_0 @ X32 )
        = ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('316',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('317',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('318',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_funct_2 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('319',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['317','318'])).

thf('320',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('321',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('322',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['319','320','321'])).

thf('323',plain,
    ( ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['316','322'])).

thf('324',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('326',plain,(
    r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['323','324','325'])).

thf('327',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['315','326'])).

thf('328',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['327','328'])).

thf('330',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['203','204'])).

thf('331',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('332',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('333',plain,(
    $false ),
    inference(demod,[status(thm)],['314','329','330','331','332'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gfERhhnHBc
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:18:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 6.62/6.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.62/6.81  % Solved by: fo/fo7.sh
% 6.62/6.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.62/6.81  % done 5607 iterations in 6.344s
% 6.62/6.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.62/6.81  % SZS output start Refutation
% 6.62/6.81  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 6.62/6.81  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 6.62/6.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.62/6.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.62/6.81  thf(sk_B_type, type, sk_B: $i).
% 6.62/6.81  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 6.62/6.81  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.62/6.81  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 6.62/6.81  thf(sk_A_type, type, sk_A: $i).
% 6.62/6.81  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 6.62/6.81  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 6.62/6.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.62/6.81  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.62/6.81  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 6.62/6.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 6.62/6.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.62/6.81  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 6.62/6.81  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 6.62/6.81  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 6.62/6.81  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.62/6.81  thf(sk_C_type, type, sk_C: $i).
% 6.62/6.81  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 6.62/6.81  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.62/6.81  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 6.62/6.81  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 6.62/6.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 6.62/6.81  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 6.62/6.81  thf(t65_funct_1, axiom,
% 6.62/6.81    (![A:$i]:
% 6.62/6.81     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.62/6.81       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 6.62/6.81  thf('0', plain,
% 6.62/6.81      (![X7 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ X7)
% 6.62/6.81          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 6.62/6.81          | ~ (v1_funct_1 @ X7)
% 6.62/6.81          | ~ (v1_relat_1 @ X7))),
% 6.62/6.81      inference('cnf', [status(esa)], [t65_funct_1])).
% 6.62/6.81  thf(d3_struct_0, axiom,
% 6.62/6.81    (![A:$i]:
% 6.62/6.81     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 6.62/6.81  thf('1', plain,
% 6.62/6.81      (![X32 : $i]:
% 6.62/6.81         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 6.62/6.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.62/6.81  thf('2', plain,
% 6.62/6.81      (![X32 : $i]:
% 6.62/6.81         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 6.62/6.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.62/6.81  thf('3', plain,
% 6.62/6.81      (![X32 : $i]:
% 6.62/6.81         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 6.62/6.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.62/6.81  thf(t64_tops_2, conjecture,
% 6.62/6.81    (![A:$i]:
% 6.62/6.81     ( ( l1_struct_0 @ A ) =>
% 6.62/6.81       ( ![B:$i]:
% 6.62/6.81         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 6.62/6.81           ( ![C:$i]:
% 6.62/6.81             ( ( ( v1_funct_1 @ C ) & 
% 6.62/6.81                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 6.62/6.81                 ( m1_subset_1 @
% 6.62/6.81                   C @ 
% 6.62/6.81                   ( k1_zfmisc_1 @
% 6.62/6.81                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.62/6.81               ( ( ( ( k2_relset_1 @
% 6.62/6.81                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 6.62/6.81                     ( k2_struct_0 @ B ) ) & 
% 6.62/6.81                   ( v2_funct_1 @ C ) ) =>
% 6.62/6.81                 ( r2_funct_2 @
% 6.62/6.81                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 6.62/6.81                   ( k2_tops_2 @
% 6.62/6.81                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 6.62/6.81                     ( k2_tops_2 @
% 6.62/6.81                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 6.62/6.81                   C ) ) ) ) ) ) ))).
% 6.62/6.81  thf(zf_stmt_0, negated_conjecture,
% 6.62/6.81    (~( ![A:$i]:
% 6.62/6.81        ( ( l1_struct_0 @ A ) =>
% 6.62/6.81          ( ![B:$i]:
% 6.62/6.81            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 6.62/6.81              ( ![C:$i]:
% 6.62/6.81                ( ( ( v1_funct_1 @ C ) & 
% 6.62/6.81                    ( v1_funct_2 @
% 6.62/6.81                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 6.62/6.81                    ( m1_subset_1 @
% 6.62/6.81                      C @ 
% 6.62/6.81                      ( k1_zfmisc_1 @
% 6.62/6.81                        ( k2_zfmisc_1 @
% 6.62/6.81                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.62/6.81                  ( ( ( ( k2_relset_1 @
% 6.62/6.81                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 6.62/6.81                        ( k2_struct_0 @ B ) ) & 
% 6.62/6.81                      ( v2_funct_1 @ C ) ) =>
% 6.62/6.81                    ( r2_funct_2 @
% 6.62/6.81                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 6.62/6.81                      ( k2_tops_2 @
% 6.62/6.81                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 6.62/6.81                        ( k2_tops_2 @
% 6.62/6.81                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 6.62/6.81                      C ) ) ) ) ) ) ) )),
% 6.62/6.81    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 6.62/6.81  thf('4', plain,
% 6.62/6.81      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.62/6.81          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.62/6.81           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 6.62/6.81          sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('5', plain,
% 6.62/6.81      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.62/6.81           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.62/6.81            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 6.62/6.81           sk_C)
% 6.62/6.81        | ~ (l1_struct_0 @ sk_A))),
% 6.62/6.81      inference('sup-', [status(thm)], ['3', '4'])).
% 6.62/6.81  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('7', plain,
% 6.62/6.81      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.62/6.81          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.62/6.81           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 6.62/6.81          sk_C)),
% 6.62/6.81      inference('demod', [status(thm)], ['5', '6'])).
% 6.62/6.81  thf('8', plain,
% 6.62/6.81      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.62/6.81           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.62/6.81            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 6.62/6.81           sk_C)
% 6.62/6.81        | ~ (l1_struct_0 @ sk_B))),
% 6.62/6.81      inference('sup-', [status(thm)], ['2', '7'])).
% 6.62/6.81  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('10', plain,
% 6.62/6.81      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.62/6.81          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.62/6.81           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 6.62/6.81          sk_C)),
% 6.62/6.81      inference('demod', [status(thm)], ['8', '9'])).
% 6.62/6.81  thf('11', plain,
% 6.62/6.81      (![X32 : $i]:
% 6.62/6.81         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 6.62/6.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.62/6.81  thf('12', plain,
% 6.62/6.81      ((m1_subset_1 @ sk_C @ 
% 6.62/6.81        (k1_zfmisc_1 @ 
% 6.62/6.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('13', plain,
% 6.62/6.81      (((m1_subset_1 @ sk_C @ 
% 6.62/6.81         (k1_zfmisc_1 @ 
% 6.62/6.81          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 6.62/6.81        | ~ (l1_struct_0 @ sk_B))),
% 6.62/6.81      inference('sup+', [status(thm)], ['11', '12'])).
% 6.62/6.81  thf('14', plain, ((l1_struct_0 @ sk_B)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('15', plain,
% 6.62/6.81      ((m1_subset_1 @ sk_C @ 
% 6.62/6.81        (k1_zfmisc_1 @ 
% 6.62/6.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 6.62/6.81      inference('demod', [status(thm)], ['13', '14'])).
% 6.62/6.81  thf(d4_tops_2, axiom,
% 6.62/6.81    (![A:$i,B:$i,C:$i]:
% 6.62/6.81     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.62/6.81         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.62/6.81       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 6.62/6.81         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 6.62/6.81  thf('16', plain,
% 6.62/6.81      (![X34 : $i, X35 : $i, X36 : $i]:
% 6.62/6.81         (((k2_relset_1 @ X35 @ X34 @ X36) != (X34))
% 6.62/6.81          | ~ (v2_funct_1 @ X36)
% 6.62/6.81          | ((k2_tops_2 @ X35 @ X34 @ X36) = (k2_funct_1 @ X36))
% 6.62/6.81          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 6.62/6.81          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 6.62/6.81          | ~ (v1_funct_1 @ X36))),
% 6.62/6.81      inference('cnf', [status(esa)], [d4_tops_2])).
% 6.62/6.81  thf('17', plain,
% 6.62/6.81      ((~ (v1_funct_1 @ sk_C)
% 6.62/6.81        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 6.62/6.81        | ((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 6.62/6.81            = (k2_funct_1 @ sk_C))
% 6.62/6.81        | ~ (v2_funct_1 @ sk_C)
% 6.62/6.81        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 6.62/6.81            != (k2_struct_0 @ sk_B)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['15', '16'])).
% 6.62/6.81  thf('18', plain, ((v1_funct_1 @ sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('19', plain,
% 6.62/6.81      (![X32 : $i]:
% 6.62/6.81         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 6.62/6.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.62/6.81  thf('20', plain,
% 6.62/6.81      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('21', plain,
% 6.62/6.81      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 6.62/6.81        | ~ (l1_struct_0 @ sk_B))),
% 6.62/6.81      inference('sup+', [status(thm)], ['19', '20'])).
% 6.62/6.81  thf('22', plain, ((l1_struct_0 @ sk_B)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('23', plain,
% 6.62/6.81      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 6.62/6.81      inference('demod', [status(thm)], ['21', '22'])).
% 6.62/6.81  thf('24', plain, ((v2_funct_1 @ sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('25', plain,
% 6.62/6.81      (![X32 : $i]:
% 6.62/6.81         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 6.62/6.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.62/6.81  thf('26', plain,
% 6.62/6.81      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 6.62/6.81         = (k2_struct_0 @ sk_B))),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('27', plain,
% 6.62/6.81      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 6.62/6.81          = (k2_struct_0 @ sk_B))
% 6.62/6.81        | ~ (l1_struct_0 @ sk_B))),
% 6.62/6.81      inference('sup+', [status(thm)], ['25', '26'])).
% 6.62/6.81  thf('28', plain, ((l1_struct_0 @ sk_B)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('29', plain,
% 6.62/6.81      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 6.62/6.81         = (k2_struct_0 @ sk_B))),
% 6.62/6.81      inference('demod', [status(thm)], ['27', '28'])).
% 6.62/6.81  thf('30', plain,
% 6.62/6.81      ((((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 6.62/6.81          = (k2_funct_1 @ sk_C))
% 6.62/6.81        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 6.62/6.81      inference('demod', [status(thm)], ['17', '18', '23', '24', '29'])).
% 6.62/6.81  thf('31', plain,
% 6.62/6.81      (((k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 6.62/6.81         = (k2_funct_1 @ sk_C))),
% 6.62/6.81      inference('simplify', [status(thm)], ['30'])).
% 6.62/6.81  thf('32', plain,
% 6.62/6.81      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.62/6.81          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.62/6.81           (k2_funct_1 @ sk_C)) @ 
% 6.62/6.81          sk_C)),
% 6.62/6.81      inference('demod', [status(thm)], ['10', '31'])).
% 6.62/6.81  thf('33', plain,
% 6.62/6.81      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.62/6.81           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 6.62/6.81            (k2_funct_1 @ sk_C)) @ 
% 6.62/6.81           sk_C)
% 6.62/6.81        | ~ (l1_struct_0 @ sk_A))),
% 6.62/6.81      inference('sup-', [status(thm)], ['1', '32'])).
% 6.62/6.81  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('35', plain,
% 6.62/6.81      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.62/6.81          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 6.62/6.81           (k2_funct_1 @ sk_C)) @ 
% 6.62/6.81          sk_C)),
% 6.62/6.81      inference('demod', [status(thm)], ['33', '34'])).
% 6.62/6.81  thf('36', plain,
% 6.62/6.81      (![X32 : $i]:
% 6.62/6.81         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 6.62/6.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.62/6.81  thf('37', plain,
% 6.62/6.81      ((m1_subset_1 @ sk_C @ 
% 6.62/6.81        (k1_zfmisc_1 @ 
% 6.62/6.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf(t31_funct_2, axiom,
% 6.62/6.81    (![A:$i,B:$i,C:$i]:
% 6.62/6.81     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.62/6.81         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.62/6.81       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 6.62/6.81         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 6.62/6.81           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 6.62/6.81           ( m1_subset_1 @
% 6.62/6.81             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 6.62/6.81  thf('38', plain,
% 6.62/6.81      (![X29 : $i, X30 : $i, X31 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ X29)
% 6.62/6.81          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 6.62/6.81          | (m1_subset_1 @ (k2_funct_1 @ X29) @ 
% 6.62/6.81             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 6.62/6.81          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 6.62/6.81          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 6.62/6.81          | ~ (v1_funct_1 @ X29))),
% 6.62/6.81      inference('cnf', [status(esa)], [t31_funct_2])).
% 6.62/6.81  thf('39', plain,
% 6.62/6.81      ((~ (v1_funct_1 @ sk_C)
% 6.62/6.81        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 6.62/6.81        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.62/6.81           (k1_zfmisc_1 @ 
% 6.62/6.81            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 6.62/6.81        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 6.62/6.81            != (u1_struct_0 @ sk_B))
% 6.62/6.81        | ~ (v2_funct_1 @ sk_C))),
% 6.62/6.81      inference('sup-', [status(thm)], ['37', '38'])).
% 6.62/6.81  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('41', plain,
% 6.62/6.81      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('42', plain,
% 6.62/6.81      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 6.62/6.81         = (k2_struct_0 @ sk_B))),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('43', plain, ((v2_funct_1 @ sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('44', plain,
% 6.62/6.81      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.62/6.81         (k1_zfmisc_1 @ 
% 6.62/6.81          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 6.62/6.81        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 6.62/6.81      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 6.62/6.81  thf('45', plain,
% 6.62/6.81      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 6.62/6.81        | ~ (l1_struct_0 @ sk_B)
% 6.62/6.81        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.62/6.81           (k1_zfmisc_1 @ 
% 6.62/6.81            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['36', '44'])).
% 6.62/6.81  thf('46', plain, ((l1_struct_0 @ sk_B)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('47', plain,
% 6.62/6.81      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 6.62/6.81        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.62/6.81           (k1_zfmisc_1 @ 
% 6.62/6.81            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))))),
% 6.62/6.81      inference('demod', [status(thm)], ['45', '46'])).
% 6.62/6.81  thf('48', plain,
% 6.62/6.81      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.62/6.81        (k1_zfmisc_1 @ 
% 6.62/6.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 6.62/6.81      inference('simplify', [status(thm)], ['47'])).
% 6.62/6.81  thf('49', plain,
% 6.62/6.81      (![X34 : $i, X35 : $i, X36 : $i]:
% 6.62/6.81         (((k2_relset_1 @ X35 @ X34 @ X36) != (X34))
% 6.62/6.81          | ~ (v2_funct_1 @ X36)
% 6.62/6.81          | ((k2_tops_2 @ X35 @ X34 @ X36) = (k2_funct_1 @ X36))
% 6.62/6.81          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 6.62/6.81          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 6.62/6.81          | ~ (v1_funct_1 @ X36))),
% 6.62/6.81      inference('cnf', [status(esa)], [d4_tops_2])).
% 6.62/6.81  thf('50', plain,
% 6.62/6.81      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.62/6.81        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.62/6.81             (u1_struct_0 @ sk_A))
% 6.62/6.81        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.62/6.81            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 6.62/6.81        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 6.62/6.81        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.62/6.81            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['48', '49'])).
% 6.62/6.81  thf('51', plain,
% 6.62/6.81      ((m1_subset_1 @ sk_C @ 
% 6.62/6.81        (k1_zfmisc_1 @ 
% 6.62/6.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 6.62/6.81      inference('demod', [status(thm)], ['13', '14'])).
% 6.62/6.81  thf('52', plain,
% 6.62/6.81      (![X29 : $i, X30 : $i, X31 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ X29)
% 6.62/6.81          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 6.62/6.81          | (v1_funct_1 @ (k2_funct_1 @ X29))
% 6.62/6.81          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 6.62/6.81          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 6.62/6.81          | ~ (v1_funct_1 @ X29))),
% 6.62/6.81      inference('cnf', [status(esa)], [t31_funct_2])).
% 6.62/6.81  thf('53', plain,
% 6.62/6.81      ((~ (v1_funct_1 @ sk_C)
% 6.62/6.81        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 6.62/6.81        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.62/6.81        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 6.62/6.81            != (k2_struct_0 @ sk_B))
% 6.62/6.81        | ~ (v2_funct_1 @ sk_C))),
% 6.62/6.81      inference('sup-', [status(thm)], ['51', '52'])).
% 6.62/6.81  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('55', plain,
% 6.62/6.81      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 6.62/6.81      inference('demod', [status(thm)], ['21', '22'])).
% 6.62/6.81  thf('56', plain,
% 6.62/6.81      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 6.62/6.81         = (k2_struct_0 @ sk_B))),
% 6.62/6.81      inference('demod', [status(thm)], ['27', '28'])).
% 6.62/6.81  thf('57', plain, ((v2_funct_1 @ sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('58', plain,
% 6.62/6.81      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.62/6.81        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 6.62/6.81      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 6.62/6.81  thf('59', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 6.62/6.81      inference('simplify', [status(thm)], ['58'])).
% 6.62/6.81  thf('60', plain,
% 6.62/6.81      (![X32 : $i]:
% 6.62/6.81         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 6.62/6.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.62/6.81  thf('61', plain,
% 6.62/6.81      ((m1_subset_1 @ sk_C @ 
% 6.62/6.81        (k1_zfmisc_1 @ 
% 6.62/6.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('62', plain,
% 6.62/6.81      (![X29 : $i, X30 : $i, X31 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ X29)
% 6.62/6.81          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 6.62/6.81          | (v1_funct_2 @ (k2_funct_1 @ X29) @ X30 @ X31)
% 6.62/6.81          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 6.62/6.81          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 6.62/6.81          | ~ (v1_funct_1 @ X29))),
% 6.62/6.81      inference('cnf', [status(esa)], [t31_funct_2])).
% 6.62/6.81  thf('63', plain,
% 6.62/6.81      ((~ (v1_funct_1 @ sk_C)
% 6.62/6.81        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 6.62/6.81        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.62/6.81           (u1_struct_0 @ sk_A))
% 6.62/6.81        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 6.62/6.81            != (u1_struct_0 @ sk_B))
% 6.62/6.81        | ~ (v2_funct_1 @ sk_C))),
% 6.62/6.81      inference('sup-', [status(thm)], ['61', '62'])).
% 6.62/6.81  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('65', plain,
% 6.62/6.81      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('66', plain,
% 6.62/6.81      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 6.62/6.81         = (k2_struct_0 @ sk_B))),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('67', plain, ((v2_funct_1 @ sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('68', plain,
% 6.62/6.81      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.62/6.81         (u1_struct_0 @ sk_A))
% 6.62/6.81        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 6.62/6.81      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 6.62/6.81  thf('69', plain,
% 6.62/6.81      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 6.62/6.81        | ~ (l1_struct_0 @ sk_B)
% 6.62/6.81        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.62/6.81           (u1_struct_0 @ sk_A)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['60', '68'])).
% 6.62/6.81  thf('70', plain, ((l1_struct_0 @ sk_B)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('71', plain,
% 6.62/6.81      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 6.62/6.81        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.62/6.81           (u1_struct_0 @ sk_A)))),
% 6.62/6.81      inference('demod', [status(thm)], ['69', '70'])).
% 6.62/6.81  thf('72', plain,
% 6.62/6.81      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.62/6.81        (u1_struct_0 @ sk_A))),
% 6.62/6.81      inference('simplify', [status(thm)], ['71'])).
% 6.62/6.81  thf('73', plain,
% 6.62/6.81      (![X7 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ X7)
% 6.62/6.81          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 6.62/6.81          | ~ (v1_funct_1 @ X7)
% 6.62/6.81          | ~ (v1_relat_1 @ X7))),
% 6.62/6.81      inference('cnf', [status(esa)], [t65_funct_1])).
% 6.62/6.81  thf(t55_funct_1, axiom,
% 6.62/6.81    (![A:$i]:
% 6.62/6.81     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.62/6.81       ( ( v2_funct_1 @ A ) =>
% 6.62/6.81         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 6.62/6.81           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 6.62/6.81  thf('74', plain,
% 6.62/6.81      (![X5 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ X5)
% 6.62/6.81          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 6.62/6.81          | ~ (v1_funct_1 @ X5)
% 6.62/6.81          | ~ (v1_relat_1 @ X5))),
% 6.62/6.81      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.62/6.81  thf('75', plain,
% 6.62/6.81      ((m1_subset_1 @ sk_C @ 
% 6.62/6.81        (k1_zfmisc_1 @ 
% 6.62/6.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 6.62/6.81      inference('demod', [status(thm)], ['13', '14'])).
% 6.62/6.81  thf('76', plain,
% 6.62/6.81      (![X29 : $i, X30 : $i, X31 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ X29)
% 6.62/6.81          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 6.62/6.81          | (m1_subset_1 @ (k2_funct_1 @ X29) @ 
% 6.62/6.81             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 6.62/6.81          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 6.62/6.81          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 6.62/6.81          | ~ (v1_funct_1 @ X29))),
% 6.62/6.81      inference('cnf', [status(esa)], [t31_funct_2])).
% 6.62/6.81  thf('77', plain,
% 6.62/6.81      ((~ (v1_funct_1 @ sk_C)
% 6.62/6.81        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 6.62/6.81        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.62/6.81           (k1_zfmisc_1 @ 
% 6.62/6.81            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 6.62/6.81        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 6.62/6.81            != (k2_struct_0 @ sk_B))
% 6.62/6.81        | ~ (v2_funct_1 @ sk_C))),
% 6.62/6.81      inference('sup-', [status(thm)], ['75', '76'])).
% 6.62/6.81  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('79', plain,
% 6.62/6.81      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 6.62/6.81      inference('demod', [status(thm)], ['21', '22'])).
% 6.62/6.81  thf('80', plain,
% 6.62/6.81      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 6.62/6.81         = (k2_struct_0 @ sk_B))),
% 6.62/6.81      inference('demod', [status(thm)], ['27', '28'])).
% 6.62/6.81  thf('81', plain, ((v2_funct_1 @ sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('82', plain,
% 6.62/6.81      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.62/6.81         (k1_zfmisc_1 @ 
% 6.62/6.81          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))
% 6.62/6.81        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 6.62/6.81      inference('demod', [status(thm)], ['77', '78', '79', '80', '81'])).
% 6.62/6.81  thf('83', plain,
% 6.62/6.81      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.62/6.81        (k1_zfmisc_1 @ 
% 6.62/6.81         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 6.62/6.81      inference('simplify', [status(thm)], ['82'])).
% 6.62/6.81  thf(cc1_relset_1, axiom,
% 6.62/6.81    (![A:$i,B:$i,C:$i]:
% 6.62/6.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.62/6.81       ( v1_relat_1 @ C ) ))).
% 6.62/6.81  thf('84', plain,
% 6.62/6.81      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.62/6.81         ((v1_relat_1 @ X8)
% 6.62/6.81          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 6.62/6.81      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.62/6.81  thf('85', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 6.62/6.81      inference('sup-', [status(thm)], ['83', '84'])).
% 6.62/6.81  thf('86', plain,
% 6.62/6.81      (![X7 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ X7)
% 6.62/6.81          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 6.62/6.81          | ~ (v1_funct_1 @ X7)
% 6.62/6.81          | ~ (v1_relat_1 @ X7))),
% 6.62/6.81      inference('cnf', [status(esa)], [t65_funct_1])).
% 6.62/6.81  thf('87', plain,
% 6.62/6.81      (![X7 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ X7)
% 6.62/6.81          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 6.62/6.81          | ~ (v1_funct_1 @ X7)
% 6.62/6.81          | ~ (v1_relat_1 @ X7))),
% 6.62/6.81      inference('cnf', [status(esa)], [t65_funct_1])).
% 6.62/6.81  thf('88', plain,
% 6.62/6.81      (![X7 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ X7)
% 6.62/6.81          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 6.62/6.81          | ~ (v1_funct_1 @ X7)
% 6.62/6.81          | ~ (v1_relat_1 @ X7))),
% 6.62/6.81      inference('cnf', [status(esa)], [t65_funct_1])).
% 6.62/6.81  thf('89', plain,
% 6.62/6.81      (![X5 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ X5)
% 6.62/6.81          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 6.62/6.81          | ~ (v1_funct_1 @ X5)
% 6.62/6.81          | ~ (v1_relat_1 @ X5))),
% 6.62/6.81      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.62/6.81  thf(dt_k2_funct_1, axiom,
% 6.62/6.81    (![A:$i]:
% 6.62/6.81     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.62/6.81       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 6.62/6.81         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 6.62/6.81  thf('90', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.62/6.81  thf('91', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.62/6.81  thf(t61_funct_1, axiom,
% 6.62/6.81    (![A:$i]:
% 6.62/6.81     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.62/6.81       ( ( v2_funct_1 @ A ) =>
% 6.62/6.81         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 6.62/6.81             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 6.62/6.81           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 6.62/6.81             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 6.62/6.81  thf('92', plain,
% 6.62/6.81      (![X6 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ X6)
% 6.62/6.81          | ((k5_relat_1 @ (k2_funct_1 @ X6) @ X6)
% 6.62/6.81              = (k6_relat_1 @ (k2_relat_1 @ X6)))
% 6.62/6.81          | ~ (v1_funct_1 @ X6)
% 6.62/6.81          | ~ (v1_relat_1 @ X6))),
% 6.62/6.81      inference('cnf', [status(esa)], [t61_funct_1])).
% 6.62/6.81  thf(t48_funct_1, axiom,
% 6.62/6.81    (![A:$i]:
% 6.62/6.81     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 6.62/6.81       ( ![B:$i]:
% 6.62/6.81         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 6.62/6.81           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 6.62/6.81               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 6.62/6.81             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 6.62/6.81  thf('93', plain,
% 6.62/6.81      (![X3 : $i, X4 : $i]:
% 6.62/6.81         (~ (v1_relat_1 @ X3)
% 6.62/6.81          | ~ (v1_funct_1 @ X3)
% 6.62/6.81          | (v2_funct_1 @ X3)
% 6.62/6.81          | ((k2_relat_1 @ X3) != (k1_relat_1 @ X4))
% 6.62/6.81          | ~ (v2_funct_1 @ (k5_relat_1 @ X3 @ X4))
% 6.62/6.81          | ~ (v1_funct_1 @ X4)
% 6.62/6.81          | ~ (v1_relat_1 @ X4))),
% 6.62/6.81      inference('cnf', [status(esa)], [t48_funct_1])).
% 6.62/6.81  thf('94', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 6.62/6.81          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['92', '93'])).
% 6.62/6.81  thf(fc4_funct_1, axiom,
% 6.62/6.81    (![A:$i]:
% 6.62/6.81     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 6.62/6.81       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 6.62/6.81  thf('95', plain, (![X2 : $i]: (v2_funct_1 @ (k6_relat_1 @ X2))),
% 6.62/6.81      inference('cnf', [status(esa)], [fc4_funct_1])).
% 6.62/6.81  thf('96', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 6.62/6.81          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 6.62/6.81      inference('demod', [status(thm)], ['94', '95'])).
% 6.62/6.81  thf('97', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['96'])).
% 6.62/6.81  thf('98', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 6.62/6.81          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['91', '97'])).
% 6.62/6.81  thf('99', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['98'])).
% 6.62/6.81  thf('100', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 6.62/6.81          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['90', '99'])).
% 6.62/6.81  thf('101', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['100'])).
% 6.62/6.81  thf('102', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['89', '101'])).
% 6.62/6.81  thf('103', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['102'])).
% 6.62/6.81  thf('104', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.62/6.81  thf('105', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.62/6.81  thf('106', plain,
% 6.62/6.81      (![X7 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ X7)
% 6.62/6.81          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 6.62/6.81          | ~ (v1_funct_1 @ X7)
% 6.62/6.81          | ~ (v1_relat_1 @ X7))),
% 6.62/6.81      inference('cnf', [status(esa)], [t65_funct_1])).
% 6.62/6.81  thf('107', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['102'])).
% 6.62/6.81  thf('108', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.62/6.81  thf('109', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.62/6.81  thf('110', plain,
% 6.62/6.81      (![X6 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ X6)
% 6.62/6.81          | ((k5_relat_1 @ X6 @ (k2_funct_1 @ X6))
% 6.62/6.81              = (k6_relat_1 @ (k1_relat_1 @ X6)))
% 6.62/6.81          | ~ (v1_funct_1 @ X6)
% 6.62/6.81          | ~ (v1_relat_1 @ X6))),
% 6.62/6.81      inference('cnf', [status(esa)], [t61_funct_1])).
% 6.62/6.81  thf('111', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['102'])).
% 6.62/6.81  thf('112', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.62/6.81  thf('113', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.62/6.81  thf('114', plain,
% 6.62/6.81      (![X7 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ X7)
% 6.62/6.81          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 6.62/6.81          | ~ (v1_funct_1 @ X7)
% 6.62/6.81          | ~ (v1_relat_1 @ X7))),
% 6.62/6.81      inference('cnf', [status(esa)], [t65_funct_1])).
% 6.62/6.81  thf('115', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['102'])).
% 6.62/6.81  thf('116', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.62/6.81  thf('117', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.62/6.81  thf('118', plain,
% 6.62/6.81      (![X7 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ X7)
% 6.62/6.81          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 6.62/6.81          | ~ (v1_funct_1 @ X7)
% 6.62/6.81          | ~ (v1_relat_1 @ X7))),
% 6.62/6.81      inference('cnf', [status(esa)], [t65_funct_1])).
% 6.62/6.81  thf('119', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['102'])).
% 6.62/6.81  thf('120', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.62/6.81  thf('121', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 6.62/6.81  thf('122', plain,
% 6.62/6.81      (![X7 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ X7)
% 6.62/6.81          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 6.62/6.81          | ~ (v1_funct_1 @ X7)
% 6.62/6.81          | ~ (v1_relat_1 @ X7))),
% 6.62/6.81      inference('cnf', [status(esa)], [t65_funct_1])).
% 6.62/6.81  thf('123', plain,
% 6.62/6.81      (![X6 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ X6)
% 6.62/6.81          | ((k5_relat_1 @ (k2_funct_1 @ X6) @ X6)
% 6.62/6.81              = (k6_relat_1 @ (k2_relat_1 @ X6)))
% 6.62/6.81          | ~ (v1_funct_1 @ X6)
% 6.62/6.81          | ~ (v1_relat_1 @ X6))),
% 6.62/6.81      inference('cnf', [status(esa)], [t61_funct_1])).
% 6.62/6.81  thf('124', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 6.62/6.81            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 6.62/6.81      inference('sup+', [status(thm)], ['122', '123'])).
% 6.62/6.81  thf('125', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 6.62/6.81              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['121', '124'])).
% 6.62/6.81  thf('126', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 6.62/6.81            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['125'])).
% 6.62/6.81  thf('127', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 6.62/6.81              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['120', '126'])).
% 6.62/6.81  thf('128', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 6.62/6.81            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['127'])).
% 6.62/6.81  thf('129', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 6.62/6.81              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['119', '128'])).
% 6.62/6.81  thf('130', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 6.62/6.81            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['129'])).
% 6.62/6.81  thf('131', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 6.62/6.81            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 6.62/6.81      inference('sup+', [status(thm)], ['118', '130'])).
% 6.62/6.81  thf('132', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 6.62/6.81              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['117', '131'])).
% 6.62/6.81  thf('133', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 6.62/6.81            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['132'])).
% 6.62/6.81  thf('134', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 6.62/6.81              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['116', '133'])).
% 6.62/6.81  thf('135', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 6.62/6.81            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['134'])).
% 6.62/6.81  thf('136', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 6.62/6.81              = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['115', '135'])).
% 6.62/6.81  thf('137', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 6.62/6.81            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['136'])).
% 6.62/6.81  thf('138', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 6.62/6.81            = (k6_relat_1 @ 
% 6.62/6.81               (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 6.62/6.81      inference('sup+', [status(thm)], ['114', '137'])).
% 6.62/6.81  thf('139', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 6.62/6.81              = (k6_relat_1 @ 
% 6.62/6.81                 (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['113', '138'])).
% 6.62/6.81  thf('140', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 6.62/6.81            = (k6_relat_1 @ 
% 6.62/6.81               (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['139'])).
% 6.62/6.81  thf('141', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 6.62/6.81              = (k6_relat_1 @ 
% 6.62/6.81                 (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['112', '140'])).
% 6.62/6.81  thf('142', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 6.62/6.81            = (k6_relat_1 @ 
% 6.62/6.81               (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['141'])).
% 6.62/6.81  thf('143', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 6.62/6.81              = (k6_relat_1 @ 
% 6.62/6.81                 (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['111', '142'])).
% 6.62/6.81  thf('144', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 6.62/6.81            = (k6_relat_1 @ 
% 6.62/6.81               (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['143'])).
% 6.62/6.81  thf('145', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (((k6_relat_1 @ (k1_relat_1 @ X0))
% 6.62/6.81            = (k6_relat_1 @ 
% 6.62/6.81               (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))))
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0))),
% 6.62/6.81      inference('sup+', [status(thm)], ['110', '144'])).
% 6.62/6.81  thf('146', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 6.62/6.81              = (k6_relat_1 @ 
% 6.62/6.81                 (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))))),
% 6.62/6.81      inference('simplify', [status(thm)], ['145'])).
% 6.62/6.81  thf('147', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 6.62/6.81            = (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['136'])).
% 6.62/6.81  thf('148', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0))
% 6.62/6.81            = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 6.62/6.81      inference('sup+', [status(thm)], ['146', '147'])).
% 6.62/6.81  thf('149', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0))
% 6.62/6.81              = (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['109', '148'])).
% 6.62/6.81  thf('150', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0))
% 6.62/6.81            = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['149'])).
% 6.62/6.81  thf('151', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0))
% 6.62/6.81              = (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['108', '150'])).
% 6.62/6.81  thf('152', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0))
% 6.62/6.81            = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['151'])).
% 6.62/6.81  thf('153', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0))
% 6.62/6.81              = (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['107', '152'])).
% 6.62/6.81  thf('154', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0))
% 6.62/6.81            = (k6_relat_1 @ (k1_relat_1 @ X0)))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['153'])).
% 6.62/6.81  thf('155', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ X0)
% 6.62/6.81            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 6.62/6.81      inference('sup+', [status(thm)], ['106', '154'])).
% 6.62/6.81  thf('156', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ X0)
% 6.62/6.81              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['105', '155'])).
% 6.62/6.81  thf('157', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ X0)
% 6.62/6.81            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['156'])).
% 6.62/6.81  thf('158', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ X0)
% 6.62/6.81              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['104', '157'])).
% 6.62/6.81  thf('159', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ X0)
% 6.62/6.81            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['158'])).
% 6.62/6.81  thf('160', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ X0)
% 6.62/6.81              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['103', '159'])).
% 6.62/6.81  thf('161', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (((k5_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))) @ X0)
% 6.62/6.81            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['160'])).
% 6.62/6.81  thf('162', plain,
% 6.62/6.81      (![X3 : $i, X4 : $i]:
% 6.62/6.81         (~ (v1_relat_1 @ X3)
% 6.62/6.81          | ~ (v1_funct_1 @ X3)
% 6.62/6.81          | (v2_funct_1 @ X3)
% 6.62/6.81          | ((k2_relat_1 @ X3) != (k1_relat_1 @ X4))
% 6.62/6.81          | ~ (v2_funct_1 @ (k5_relat_1 @ X3 @ X4))
% 6.62/6.81          | ~ (v1_funct_1 @ X4)
% 6.62/6.81          | ~ (v1_relat_1 @ X4))),
% 6.62/6.81      inference('cnf', [status(esa)], [t48_funct_1])).
% 6.62/6.81  thf('163', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81              != (k1_relat_1 @ X0))
% 6.62/6.81          | (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['161', '162'])).
% 6.62/6.81  thf('164', plain, (![X2 : $i]: (v2_funct_1 @ (k6_relat_1 @ X2))),
% 6.62/6.81      inference('cnf', [status(esa)], [fc4_funct_1])).
% 6.62/6.81  thf('165', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81              != (k1_relat_1 @ X0))
% 6.62/6.81          | (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 6.62/6.81      inference('demod', [status(thm)], ['163', '164'])).
% 6.62/6.81  thf('166', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81          | (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81          | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81              != (k1_relat_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0))),
% 6.62/6.81      inference('simplify', [status(thm)], ['165'])).
% 6.62/6.81  thf('167', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81              != (k1_relat_1 @ X0))
% 6.62/6.81          | (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['88', '166'])).
% 6.62/6.81  thf('168', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81          | (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81          | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81              != (k1_relat_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 6.62/6.81      inference('simplify', [status(thm)], ['167'])).
% 6.62/6.81  thf('169', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81              != (k1_relat_1 @ X0))
% 6.62/6.81          | (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['87', '168'])).
% 6.62/6.81  thf('170', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         ((v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81          | ((k2_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81              != (k1_relat_1 @ X0))
% 6.62/6.81          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 6.62/6.81      inference('simplify', [status(thm)], ['169'])).
% 6.62/6.81  thf('171', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['86', '170'])).
% 6.62/6.81  thf('172', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         ((v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 6.62/6.81          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 6.62/6.81          | ~ (v2_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_relat_1 @ X0)
% 6.62/6.81          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0)))),
% 6.62/6.81      inference('simplify', [status(thm)], ['171'])).
% 6.62/6.81  thf('173', plain,
% 6.62/6.81      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 6.62/6.81        | ~ (v1_relat_1 @ sk_C)
% 6.62/6.81        | ~ (v1_funct_1 @ sk_C)
% 6.62/6.81        | ~ (v2_funct_1 @ sk_C)
% 6.62/6.81        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.62/6.81        | (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['85', '172'])).
% 6.62/6.81  thf('174', plain,
% 6.62/6.81      (![X32 : $i]:
% 6.62/6.81         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 6.62/6.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.62/6.81  thf('175', plain,
% 6.62/6.81      (![X32 : $i]:
% 6.62/6.81         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 6.62/6.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.62/6.81  thf(d1_funct_2, axiom,
% 6.62/6.81    (![A:$i,B:$i,C:$i]:
% 6.62/6.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.62/6.81       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.62/6.81           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 6.62/6.81             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 6.62/6.81         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.62/6.81           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 6.62/6.81             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 6.62/6.81  thf(zf_stmt_1, axiom,
% 6.62/6.81    (![B:$i,A:$i]:
% 6.62/6.81     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 6.62/6.81       ( zip_tseitin_0 @ B @ A ) ))).
% 6.62/6.81  thf('176', plain,
% 6.62/6.81      (![X17 : $i, X18 : $i]:
% 6.62/6.81         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.62/6.81  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 6.62/6.81  thf('177', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.62/6.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.62/6.81  thf('178', plain,
% 6.62/6.81      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 6.62/6.81      inference('sup+', [status(thm)], ['176', '177'])).
% 6.62/6.81  thf('179', plain,
% 6.62/6.81      ((m1_subset_1 @ sk_C @ 
% 6.62/6.81        (k1_zfmisc_1 @ 
% 6.62/6.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 6.62/6.81  thf(zf_stmt_3, axiom,
% 6.62/6.81    (![C:$i,B:$i,A:$i]:
% 6.62/6.81     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 6.62/6.81       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 6.62/6.81  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 6.62/6.81  thf(zf_stmt_5, axiom,
% 6.62/6.81    (![A:$i,B:$i,C:$i]:
% 6.62/6.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.62/6.81       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 6.62/6.81         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 6.62/6.81           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 6.62/6.81             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 6.62/6.81  thf('180', plain,
% 6.62/6.81      (![X22 : $i, X23 : $i, X24 : $i]:
% 6.62/6.81         (~ (zip_tseitin_0 @ X22 @ X23)
% 6.62/6.81          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 6.62/6.81          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_5])).
% 6.62/6.81  thf('181', plain,
% 6.62/6.81      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.62/6.81        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['179', '180'])).
% 6.62/6.81  thf('182', plain,
% 6.62/6.81      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 6.62/6.81        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['178', '181'])).
% 6.62/6.81  thf('183', plain,
% 6.62/6.81      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('184', plain,
% 6.62/6.81      (![X19 : $i, X20 : $i, X21 : $i]:
% 6.62/6.81         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 6.62/6.81          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 6.62/6.81          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_3])).
% 6.62/6.81  thf('185', plain,
% 6.62/6.81      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.62/6.81        | ((u1_struct_0 @ sk_A)
% 6.62/6.81            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['183', '184'])).
% 6.62/6.81  thf('186', plain,
% 6.62/6.81      ((m1_subset_1 @ sk_C @ 
% 6.62/6.81        (k1_zfmisc_1 @ 
% 6.62/6.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf(redefinition_k1_relset_1, axiom,
% 6.62/6.81    (![A:$i,B:$i,C:$i]:
% 6.62/6.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.62/6.81       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 6.62/6.81  thf('187', plain,
% 6.62/6.81      (![X11 : $i, X12 : $i, X13 : $i]:
% 6.62/6.81         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 6.62/6.81          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 6.62/6.81      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.62/6.81  thf('188', plain,
% 6.62/6.81      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 6.62/6.81         = (k1_relat_1 @ sk_C))),
% 6.62/6.81      inference('sup-', [status(thm)], ['186', '187'])).
% 6.62/6.81  thf('189', plain,
% 6.62/6.81      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.62/6.81        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 6.62/6.81      inference('demod', [status(thm)], ['185', '188'])).
% 6.62/6.81  thf('190', plain,
% 6.62/6.81      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 6.62/6.81        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['182', '189'])).
% 6.62/6.81  thf('191', plain,
% 6.62/6.81      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 6.62/6.81        | ~ (l1_struct_0 @ sk_B)
% 6.62/6.81        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 6.62/6.81      inference('sup+', [status(thm)], ['175', '190'])).
% 6.62/6.81  thf('192', plain, ((l1_struct_0 @ sk_B)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('193', plain,
% 6.62/6.81      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 6.62/6.81        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 6.62/6.81      inference('demod', [status(thm)], ['191', '192'])).
% 6.62/6.81  thf('194', plain,
% 6.62/6.81      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 6.62/6.81        | ~ (l1_struct_0 @ sk_A)
% 6.62/6.81        | (v1_xboole_0 @ (k2_struct_0 @ sk_B)))),
% 6.62/6.81      inference('sup+', [status(thm)], ['174', '193'])).
% 6.62/6.81  thf('195', plain, ((l1_struct_0 @ sk_A)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('196', plain,
% 6.62/6.81      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 6.62/6.81        | (v1_xboole_0 @ (k2_struct_0 @ sk_B)))),
% 6.62/6.81      inference('demod', [status(thm)], ['194', '195'])).
% 6.62/6.81  thf(fc5_struct_0, axiom,
% 6.62/6.81    (![A:$i]:
% 6.62/6.81     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 6.62/6.81       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 6.62/6.81  thf('197', plain,
% 6.62/6.81      (![X33 : $i]:
% 6.62/6.81         (~ (v1_xboole_0 @ (k2_struct_0 @ X33))
% 6.62/6.81          | ~ (l1_struct_0 @ X33)
% 6.62/6.81          | (v2_struct_0 @ X33))),
% 6.62/6.81      inference('cnf', [status(esa)], [fc5_struct_0])).
% 6.62/6.81  thf('198', plain,
% 6.62/6.81      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 6.62/6.81        | (v2_struct_0 @ sk_B)
% 6.62/6.81        | ~ (l1_struct_0 @ sk_B))),
% 6.62/6.81      inference('sup-', [status(thm)], ['196', '197'])).
% 6.62/6.81  thf('199', plain, ((l1_struct_0 @ sk_B)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('200', plain,
% 6.62/6.81      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 6.62/6.81      inference('demod', [status(thm)], ['198', '199'])).
% 6.62/6.81  thf('201', plain, (~ (v2_struct_0 @ sk_B)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('202', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 6.62/6.81      inference('clc', [status(thm)], ['200', '201'])).
% 6.62/6.81  thf('203', plain,
% 6.62/6.81      ((m1_subset_1 @ sk_C @ 
% 6.62/6.81        (k1_zfmisc_1 @ 
% 6.62/6.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('204', plain,
% 6.62/6.81      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.62/6.81         ((v1_relat_1 @ X8)
% 6.62/6.81          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 6.62/6.81      inference('cnf', [status(esa)], [cc1_relset_1])).
% 6.62/6.81  thf('205', plain, ((v1_relat_1 @ sk_C)),
% 6.62/6.81      inference('sup-', [status(thm)], ['203', '204'])).
% 6.62/6.81  thf('206', plain, ((v1_funct_1 @ sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('207', plain, ((v2_funct_1 @ sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('208', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 6.62/6.81      inference('simplify', [status(thm)], ['58'])).
% 6.62/6.81  thf('209', plain,
% 6.62/6.81      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 6.62/6.81        | (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 6.62/6.81      inference('demod', [status(thm)],
% 6.62/6.81                ['173', '202', '205', '206', '207', '208'])).
% 6.62/6.81  thf('210', plain,
% 6.62/6.81      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 6.62/6.81        | ~ (v1_relat_1 @ sk_C)
% 6.62/6.81        | ~ (v1_funct_1 @ sk_C)
% 6.62/6.81        | ~ (v2_funct_1 @ sk_C)
% 6.62/6.81        | (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['74', '209'])).
% 6.62/6.81  thf('211', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 6.62/6.81      inference('clc', [status(thm)], ['200', '201'])).
% 6.62/6.81  thf('212', plain, ((v1_relat_1 @ sk_C)),
% 6.62/6.81      inference('sup-', [status(thm)], ['203', '204'])).
% 6.62/6.81  thf('213', plain, ((v1_funct_1 @ sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('214', plain, ((v2_funct_1 @ sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('215', plain,
% 6.62/6.81      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 6.62/6.81        | (v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 6.62/6.81      inference('demod', [status(thm)], ['210', '211', '212', '213', '214'])).
% 6.62/6.81  thf('216', plain,
% 6.62/6.81      ((v2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 6.62/6.81      inference('simplify', [status(thm)], ['215'])).
% 6.62/6.81  thf('217', plain,
% 6.62/6.81      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 6.62/6.81        | ~ (v1_relat_1 @ sk_C)
% 6.62/6.81        | ~ (v1_funct_1 @ sk_C)
% 6.62/6.81        | ~ (v2_funct_1 @ sk_C))),
% 6.62/6.81      inference('sup+', [status(thm)], ['73', '216'])).
% 6.62/6.81  thf('218', plain, ((v1_relat_1 @ sk_C)),
% 6.62/6.81      inference('sup-', [status(thm)], ['203', '204'])).
% 6.62/6.81  thf('219', plain, ((v1_funct_1 @ sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('220', plain, ((v2_funct_1 @ sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('221', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 6.62/6.81      inference('demod', [status(thm)], ['217', '218', '219', '220'])).
% 6.62/6.81  thf('222', plain,
% 6.62/6.81      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.62/6.81          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 6.62/6.81        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.62/6.81            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 6.62/6.81      inference('demod', [status(thm)], ['50', '59', '72', '221'])).
% 6.62/6.81  thf('223', plain,
% 6.62/6.81      (![X32 : $i]:
% 6.62/6.81         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 6.62/6.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.62/6.81  thf('224', plain,
% 6.62/6.81      (![X17 : $i, X18 : $i]:
% 6.62/6.81         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.62/6.81  thf('225', plain,
% 6.62/6.81      (![X17 : $i, X18 : $i]:
% 6.62/6.81         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.62/6.81  thf('226', plain,
% 6.62/6.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.62/6.81         (((X1) = (X0)) | (zip_tseitin_0 @ X0 @ X3) | (zip_tseitin_0 @ X1 @ X2))),
% 6.62/6.81      inference('sup+', [status(thm)], ['224', '225'])).
% 6.62/6.81  thf('227', plain,
% 6.62/6.81      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.62/6.81        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['179', '180'])).
% 6.62/6.81  thf('228', plain,
% 6.62/6.81      (![X0 : $i, X1 : $i]:
% 6.62/6.81         ((zip_tseitin_0 @ X1 @ X0)
% 6.62/6.81          | ((u1_struct_0 @ sk_B) = (X1))
% 6.62/6.81          | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['226', '227'])).
% 6.62/6.81  thf('229', plain,
% 6.62/6.81      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.62/6.81        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 6.62/6.81      inference('demod', [status(thm)], ['185', '188'])).
% 6.62/6.81  thf('230', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 6.62/6.81      inference('clc', [status(thm)], ['200', '201'])).
% 6.62/6.81  thf('231', plain,
% 6.62/6.81      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.62/6.81        | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))),
% 6.62/6.81      inference('demod', [status(thm)], ['229', '230'])).
% 6.62/6.81  thf('232', plain,
% 6.62/6.81      (![X0 : $i, X1 : $i]:
% 6.62/6.81         (((u1_struct_0 @ sk_B) = (X0))
% 6.62/6.81          | (zip_tseitin_0 @ X0 @ X1)
% 6.62/6.81          | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['228', '231'])).
% 6.62/6.81  thf('233', plain,
% 6.62/6.81      (![X0 : $i, X1 : $i]:
% 6.62/6.81         (((k2_struct_0 @ sk_B) = (X0))
% 6.62/6.81          | ~ (l1_struct_0 @ sk_B)
% 6.62/6.81          | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 6.62/6.81          | (zip_tseitin_0 @ X0 @ X1))),
% 6.62/6.81      inference('sup+', [status(thm)], ['223', '232'])).
% 6.62/6.81  thf('234', plain, ((l1_struct_0 @ sk_B)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('235', plain,
% 6.62/6.81      (![X0 : $i, X1 : $i]:
% 6.62/6.81         (((k2_struct_0 @ sk_B) = (X0))
% 6.62/6.81          | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 6.62/6.81          | (zip_tseitin_0 @ X0 @ X1))),
% 6.62/6.81      inference('demod', [status(thm)], ['233', '234'])).
% 6.62/6.81  thf('236', plain,
% 6.62/6.81      (![X33 : $i]:
% 6.62/6.81         (~ (v1_xboole_0 @ (k2_struct_0 @ X33))
% 6.62/6.81          | ~ (l1_struct_0 @ X33)
% 6.62/6.81          | (v2_struct_0 @ X33))),
% 6.62/6.81      inference('cnf', [status(esa)], [fc5_struct_0])).
% 6.62/6.81  thf('237', plain,
% 6.62/6.81      (![X0 : $i, X1 : $i]:
% 6.62/6.81         (~ (v1_xboole_0 @ X0)
% 6.62/6.81          | (zip_tseitin_0 @ X0 @ X1)
% 6.62/6.81          | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 6.62/6.81          | (v2_struct_0 @ sk_B)
% 6.62/6.81          | ~ (l1_struct_0 @ sk_B))),
% 6.62/6.81      inference('sup-', [status(thm)], ['235', '236'])).
% 6.62/6.81  thf('238', plain, ((l1_struct_0 @ sk_B)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('239', plain,
% 6.62/6.81      (![X0 : $i, X1 : $i]:
% 6.62/6.81         (~ (v1_xboole_0 @ X0)
% 6.62/6.81          | (zip_tseitin_0 @ X0 @ X1)
% 6.62/6.81          | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 6.62/6.81          | (v2_struct_0 @ sk_B))),
% 6.62/6.81      inference('demod', [status(thm)], ['237', '238'])).
% 6.62/6.81  thf('240', plain,
% 6.62/6.81      (![X32 : $i]:
% 6.62/6.81         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 6.62/6.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.62/6.81  thf('241', plain,
% 6.62/6.81      (![X17 : $i, X18 : $i]:
% 6.62/6.81         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 6.62/6.81  thf('242', plain,
% 6.62/6.81      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.62/6.81        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['179', '180'])).
% 6.62/6.81  thf('243', plain,
% 6.62/6.81      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 6.62/6.81        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['241', '242'])).
% 6.62/6.81  thf('244', plain,
% 6.62/6.81      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.62/6.81        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 6.62/6.81      inference('demod', [status(thm)], ['185', '188'])).
% 6.62/6.81  thf('245', plain,
% 6.62/6.81      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 6.62/6.81        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['243', '244'])).
% 6.62/6.81  thf('246', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 6.62/6.81      inference('clc', [status(thm)], ['200', '201'])).
% 6.62/6.81  thf('247', plain,
% 6.62/6.81      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 6.62/6.81        | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))),
% 6.62/6.81      inference('demod', [status(thm)], ['245', '246'])).
% 6.62/6.81  thf('248', plain,
% 6.62/6.81      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.62/6.81        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['179', '180'])).
% 6.62/6.81  thf('249', plain,
% 6.62/6.81      ((~ (zip_tseitin_0 @ k1_xboole_0 @ (u1_struct_0 @ sk_A))
% 6.62/6.81        | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 6.62/6.81        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['247', '248'])).
% 6.62/6.81  thf('250', plain,
% 6.62/6.81      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 6.62/6.81        | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))),
% 6.62/6.81      inference('demod', [status(thm)], ['229', '230'])).
% 6.62/6.81  thf('251', plain,
% 6.62/6.81      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 6.62/6.81        | ~ (zip_tseitin_0 @ k1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 6.62/6.81      inference('clc', [status(thm)], ['249', '250'])).
% 6.62/6.81  thf('252', plain,
% 6.62/6.81      ((~ (zip_tseitin_0 @ k1_xboole_0 @ (k2_struct_0 @ sk_A))
% 6.62/6.81        | ~ (l1_struct_0 @ sk_A)
% 6.62/6.81        | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['240', '251'])).
% 6.62/6.81  thf('253', plain, ((l1_struct_0 @ sk_A)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('254', plain,
% 6.62/6.81      ((~ (zip_tseitin_0 @ k1_xboole_0 @ (k2_struct_0 @ sk_A))
% 6.62/6.81        | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))),
% 6.62/6.81      inference('demod', [status(thm)], ['252', '253'])).
% 6.62/6.81  thf('255', plain,
% 6.62/6.81      (((v2_struct_0 @ sk_B)
% 6.62/6.81        | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 6.62/6.81        | ~ (v1_xboole_0 @ k1_xboole_0)
% 6.62/6.81        | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['239', '254'])).
% 6.62/6.81  thf('256', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 6.62/6.81      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 6.62/6.81  thf('257', plain,
% 6.62/6.81      (((v2_struct_0 @ sk_B)
% 6.62/6.81        | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 6.62/6.81        | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))),
% 6.62/6.81      inference('demod', [status(thm)], ['255', '256'])).
% 6.62/6.81  thf('258', plain,
% 6.62/6.81      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 6.62/6.81      inference('simplify', [status(thm)], ['257'])).
% 6.62/6.81  thf('259', plain, (~ (v2_struct_0 @ sk_B)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('260', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 6.62/6.81      inference('clc', [status(thm)], ['258', '259'])).
% 6.62/6.81  thf('261', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 6.62/6.81      inference('clc', [status(thm)], ['258', '259'])).
% 6.62/6.81  thf('262', plain,
% 6.62/6.81      (![X32 : $i]:
% 6.62/6.81         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 6.62/6.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.62/6.81  thf('263', plain,
% 6.62/6.81      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.62/6.81        (k1_zfmisc_1 @ 
% 6.62/6.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 6.62/6.81      inference('simplify', [status(thm)], ['47'])).
% 6.62/6.81  thf('264', plain,
% 6.62/6.81      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.62/6.81         (k1_zfmisc_1 @ 
% 6.62/6.81          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 6.62/6.81        | ~ (l1_struct_0 @ sk_A))),
% 6.62/6.81      inference('sup+', [status(thm)], ['262', '263'])).
% 6.62/6.81  thf('265', plain, ((l1_struct_0 @ sk_A)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('266', plain,
% 6.62/6.81      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.62/6.81        (k1_zfmisc_1 @ 
% 6.62/6.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 6.62/6.81      inference('demod', [status(thm)], ['264', '265'])).
% 6.62/6.81  thf(redefinition_k2_relset_1, axiom,
% 6.62/6.81    (![A:$i,B:$i,C:$i]:
% 6.62/6.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 6.62/6.81       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 6.62/6.81  thf('267', plain,
% 6.62/6.81      (![X14 : $i, X15 : $i, X16 : $i]:
% 6.62/6.81         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 6.62/6.81          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 6.62/6.81      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 6.62/6.81  thf('268', plain,
% 6.62/6.81      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 6.62/6.81         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['266', '267'])).
% 6.62/6.81  thf('269', plain,
% 6.62/6.81      (![X5 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ X5)
% 6.62/6.81          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 6.62/6.81          | ~ (v1_funct_1 @ X5)
% 6.62/6.81          | ~ (v1_relat_1 @ X5))),
% 6.62/6.81      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.62/6.81  thf('270', plain,
% 6.62/6.81      (![X7 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ X7)
% 6.62/6.81          | ((k2_funct_1 @ (k2_funct_1 @ X7)) = (X7))
% 6.62/6.81          | ~ (v1_funct_1 @ X7)
% 6.62/6.81          | ~ (v1_relat_1 @ X7))),
% 6.62/6.81      inference('cnf', [status(esa)], [t65_funct_1])).
% 6.62/6.81  thf('271', plain,
% 6.62/6.81      (![X32 : $i]:
% 6.62/6.81         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 6.62/6.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.62/6.81  thf('272', plain,
% 6.62/6.81      (![X5 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ X5)
% 6.62/6.81          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 6.62/6.81          | ~ (v1_funct_1 @ X5)
% 6.62/6.81          | ~ (v1_relat_1 @ X5))),
% 6.62/6.81      inference('cnf', [status(esa)], [t55_funct_1])).
% 6.62/6.81  thf('273', plain,
% 6.62/6.81      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.62/6.81        (k1_zfmisc_1 @ 
% 6.62/6.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 6.62/6.81      inference('simplify', [status(thm)], ['47'])).
% 6.62/6.81  thf('274', plain,
% 6.62/6.81      (![X29 : $i, X30 : $i, X31 : $i]:
% 6.62/6.81         (~ (v2_funct_1 @ X29)
% 6.62/6.81          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 6.62/6.81          | (m1_subset_1 @ (k2_funct_1 @ X29) @ 
% 6.62/6.81             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 6.62/6.81          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 6.62/6.81          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 6.62/6.81          | ~ (v1_funct_1 @ X29))),
% 6.62/6.81      inference('cnf', [status(esa)], [t31_funct_2])).
% 6.62/6.81  thf('275', plain,
% 6.62/6.81      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.62/6.81        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.62/6.81             (u1_struct_0 @ sk_A))
% 6.62/6.81        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 6.62/6.81           (k1_zfmisc_1 @ 
% 6.62/6.81            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 6.62/6.81        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.62/6.81            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A))
% 6.62/6.81        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['273', '274'])).
% 6.62/6.81  thf('276', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 6.62/6.81      inference('simplify', [status(thm)], ['58'])).
% 6.62/6.81  thf('277', plain,
% 6.62/6.81      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 6.62/6.81        (u1_struct_0 @ sk_A))),
% 6.62/6.81      inference('simplify', [status(thm)], ['71'])).
% 6.62/6.81  thf('278', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 6.62/6.81      inference('demod', [status(thm)], ['217', '218', '219', '220'])).
% 6.62/6.81  thf('279', plain,
% 6.62/6.81      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 6.62/6.81         (k1_zfmisc_1 @ 
% 6.62/6.81          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 6.62/6.81        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.62/6.81            (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 6.62/6.81      inference('demod', [status(thm)], ['275', '276', '277', '278'])).
% 6.62/6.81  thf('280', plain,
% 6.62/6.81      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 6.62/6.81        (k1_zfmisc_1 @ 
% 6.62/6.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 6.62/6.81      inference('simplify', [status(thm)], ['47'])).
% 6.62/6.81  thf('281', plain,
% 6.62/6.81      (![X14 : $i, X15 : $i, X16 : $i]:
% 6.62/6.81         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 6.62/6.81          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 6.62/6.81      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 6.62/6.81  thf('282', plain,
% 6.62/6.81      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 6.62/6.81         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['280', '281'])).
% 6.62/6.81  thf('283', plain,
% 6.62/6.81      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 6.62/6.81         (k1_zfmisc_1 @ 
% 6.62/6.81          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 6.62/6.81        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (u1_struct_0 @ sk_A)))),
% 6.62/6.81      inference('demod', [status(thm)], ['279', '282'])).
% 6.62/6.81  thf('284', plain,
% 6.62/6.81      ((((k1_relat_1 @ sk_C) != (u1_struct_0 @ sk_A))
% 6.62/6.81        | ~ (v1_relat_1 @ sk_C)
% 6.62/6.81        | ~ (v1_funct_1 @ sk_C)
% 6.62/6.81        | ~ (v2_funct_1 @ sk_C)
% 6.62/6.81        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 6.62/6.81           (k1_zfmisc_1 @ 
% 6.62/6.81            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['272', '283'])).
% 6.62/6.81  thf('285', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 6.62/6.81      inference('clc', [status(thm)], ['200', '201'])).
% 6.62/6.81  thf('286', plain, ((v1_relat_1 @ sk_C)),
% 6.62/6.81      inference('sup-', [status(thm)], ['203', '204'])).
% 6.62/6.81  thf('287', plain, ((v1_funct_1 @ sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('288', plain, ((v2_funct_1 @ sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('289', plain,
% 6.62/6.81      ((((k2_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 6.62/6.81        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 6.62/6.81           (k1_zfmisc_1 @ 
% 6.62/6.81            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 6.62/6.81      inference('demod', [status(thm)], ['284', '285', '286', '287', '288'])).
% 6.62/6.81  thf('290', plain,
% 6.62/6.81      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 6.62/6.81        | ~ (l1_struct_0 @ sk_A)
% 6.62/6.81        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 6.62/6.81           (k1_zfmisc_1 @ 
% 6.62/6.81            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['271', '289'])).
% 6.62/6.81  thf('291', plain, ((l1_struct_0 @ sk_A)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('292', plain,
% 6.62/6.81      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 6.62/6.81        | (m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 6.62/6.81           (k1_zfmisc_1 @ 
% 6.62/6.81            (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))))),
% 6.62/6.81      inference('demod', [status(thm)], ['290', '291'])).
% 6.62/6.81  thf('293', plain,
% 6.62/6.81      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 6.62/6.81        (k1_zfmisc_1 @ 
% 6.62/6.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 6.62/6.81      inference('simplify', [status(thm)], ['292'])).
% 6.62/6.81  thf('294', plain,
% 6.62/6.81      (![X11 : $i, X12 : $i, X13 : $i]:
% 6.62/6.81         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 6.62/6.81          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 6.62/6.81      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 6.62/6.81  thf('295', plain,
% 6.62/6.81      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.62/6.81         (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 6.62/6.81         = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 6.62/6.81      inference('sup-', [status(thm)], ['293', '294'])).
% 6.62/6.81  thf('296', plain,
% 6.62/6.81      ((((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 6.62/6.81          = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 6.62/6.81        | ~ (v1_relat_1 @ sk_C)
% 6.62/6.81        | ~ (v1_funct_1 @ sk_C)
% 6.62/6.81        | ~ (v2_funct_1 @ sk_C))),
% 6.62/6.81      inference('sup+', [status(thm)], ['270', '295'])).
% 6.62/6.81  thf('297', plain,
% 6.62/6.81      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 6.62/6.81         = (k1_relat_1 @ sk_C))),
% 6.62/6.81      inference('sup-', [status(thm)], ['186', '187'])).
% 6.62/6.81  thf('298', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 6.62/6.81      inference('clc', [status(thm)], ['200', '201'])).
% 6.62/6.81  thf('299', plain,
% 6.62/6.81      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 6.62/6.81         = (k2_struct_0 @ sk_A))),
% 6.62/6.81      inference('demod', [status(thm)], ['297', '298'])).
% 6.62/6.81  thf('300', plain, ((v1_relat_1 @ sk_C)),
% 6.62/6.81      inference('sup-', [status(thm)], ['203', '204'])).
% 6.62/6.81  thf('301', plain, ((v1_funct_1 @ sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('302', plain, ((v2_funct_1 @ sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('303', plain,
% 6.62/6.81      (((k2_struct_0 @ sk_A)
% 6.62/6.81         = (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 6.62/6.81      inference('demod', [status(thm)], ['296', '299', '300', '301', '302'])).
% 6.62/6.81  thf('304', plain,
% 6.62/6.81      ((((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 6.62/6.81        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 6.62/6.81        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 6.62/6.81        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 6.62/6.81      inference('sup+', [status(thm)], ['269', '303'])).
% 6.62/6.81  thf('305', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 6.62/6.81      inference('sup-', [status(thm)], ['83', '84'])).
% 6.62/6.81  thf('306', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 6.62/6.81      inference('simplify', [status(thm)], ['58'])).
% 6.62/6.81  thf('307', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 6.62/6.81      inference('demod', [status(thm)], ['217', '218', '219', '220'])).
% 6.62/6.81  thf('308', plain,
% 6.62/6.81      (((k2_struct_0 @ sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 6.62/6.81      inference('demod', [status(thm)], ['304', '305', '306', '307'])).
% 6.62/6.81  thf('309', plain,
% 6.62/6.81      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 6.62/6.81         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 6.62/6.81      inference('demod', [status(thm)], ['268', '308'])).
% 6.62/6.81  thf('310', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 6.62/6.81      inference('clc', [status(thm)], ['258', '259'])).
% 6.62/6.81  thf('311', plain,
% 6.62/6.81      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 6.62/6.81          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 6.62/6.81        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 6.62/6.81      inference('demod', [status(thm)], ['222', '260', '261', '309', '310'])).
% 6.62/6.81  thf('312', plain,
% 6.62/6.81      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 6.62/6.81         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 6.62/6.81      inference('simplify', [status(thm)], ['311'])).
% 6.62/6.81  thf('313', plain,
% 6.62/6.81      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.62/6.81          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 6.62/6.81      inference('demod', [status(thm)], ['35', '312'])).
% 6.62/6.81  thf('314', plain,
% 6.62/6.81      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 6.62/6.81           sk_C)
% 6.62/6.81        | ~ (v1_relat_1 @ sk_C)
% 6.62/6.81        | ~ (v1_funct_1 @ sk_C)
% 6.62/6.81        | ~ (v2_funct_1 @ sk_C))),
% 6.62/6.81      inference('sup-', [status(thm)], ['0', '313'])).
% 6.62/6.81  thf('315', plain,
% 6.62/6.81      (![X32 : $i]:
% 6.62/6.81         (((k2_struct_0 @ X32) = (u1_struct_0 @ X32)) | ~ (l1_struct_0 @ X32))),
% 6.62/6.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 6.62/6.81  thf('316', plain,
% 6.62/6.81      ((m1_subset_1 @ sk_C @ 
% 6.62/6.81        (k1_zfmisc_1 @ 
% 6.62/6.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('317', plain,
% 6.62/6.81      ((m1_subset_1 @ sk_C @ 
% 6.62/6.81        (k1_zfmisc_1 @ 
% 6.62/6.81         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf(reflexivity_r2_funct_2, axiom,
% 6.62/6.81    (![A:$i,B:$i,C:$i,D:$i]:
% 6.62/6.81     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 6.62/6.81         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 6.62/6.81         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 6.62/6.81         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 6.62/6.81       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 6.62/6.81  thf('318', plain,
% 6.62/6.81      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 6.62/6.81         ((r2_funct_2 @ X25 @ X26 @ X27 @ X27)
% 6.62/6.81          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 6.62/6.81          | ~ (v1_funct_2 @ X27 @ X25 @ X26)
% 6.62/6.81          | ~ (v1_funct_1 @ X27)
% 6.62/6.81          | ~ (v1_funct_1 @ X28)
% 6.62/6.81          | ~ (v1_funct_2 @ X28 @ X25 @ X26)
% 6.62/6.81          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 6.62/6.81      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 6.62/6.81  thf('319', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (m1_subset_1 @ X0 @ 
% 6.62/6.81             (k1_zfmisc_1 @ 
% 6.62/6.81              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 6.62/6.81          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | ~ (v1_funct_1 @ sk_C)
% 6.62/6.81          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 6.62/6.81          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 6.62/6.81             sk_C))),
% 6.62/6.81      inference('sup-', [status(thm)], ['317', '318'])).
% 6.62/6.81  thf('320', plain, ((v1_funct_1 @ sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('321', plain,
% 6.62/6.81      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('322', plain,
% 6.62/6.81      (![X0 : $i]:
% 6.62/6.81         (~ (m1_subset_1 @ X0 @ 
% 6.62/6.81             (k1_zfmisc_1 @ 
% 6.62/6.81              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 6.62/6.81          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 6.62/6.81          | ~ (v1_funct_1 @ X0)
% 6.62/6.81          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 6.62/6.81             sk_C))),
% 6.62/6.81      inference('demod', [status(thm)], ['319', '320', '321'])).
% 6.62/6.81  thf('323', plain,
% 6.62/6.81      (((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 6.62/6.81        | ~ (v1_funct_1 @ sk_C)
% 6.62/6.81        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 6.62/6.81      inference('sup-', [status(thm)], ['316', '322'])).
% 6.62/6.81  thf('324', plain, ((v1_funct_1 @ sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('325', plain,
% 6.62/6.81      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('326', plain,
% 6.62/6.81      ((r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 6.62/6.81      inference('demod', [status(thm)], ['323', '324', '325'])).
% 6.62/6.81  thf('327', plain,
% 6.62/6.81      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 6.62/6.81        | ~ (l1_struct_0 @ sk_A))),
% 6.62/6.81      inference('sup+', [status(thm)], ['315', '326'])).
% 6.62/6.81  thf('328', plain, ((l1_struct_0 @ sk_A)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('329', plain,
% 6.62/6.81      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 6.62/6.81      inference('demod', [status(thm)], ['327', '328'])).
% 6.62/6.81  thf('330', plain, ((v1_relat_1 @ sk_C)),
% 6.62/6.81      inference('sup-', [status(thm)], ['203', '204'])).
% 6.62/6.81  thf('331', plain, ((v1_funct_1 @ sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('332', plain, ((v2_funct_1 @ sk_C)),
% 6.62/6.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.62/6.81  thf('333', plain, ($false),
% 6.62/6.81      inference('demod', [status(thm)], ['314', '329', '330', '331', '332'])).
% 6.62/6.81  
% 6.62/6.81  % SZS output end Refutation
% 6.62/6.81  
% 6.62/6.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
