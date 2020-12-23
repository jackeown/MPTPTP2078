%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B0LnWnhY8I

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:59 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  247 (5046 expanded)
%              Number of leaves         :   46 (1474 expanded)
%              Depth                    :   27
%              Number of atoms          : 2280 (125403 expanded)
%              Number of equality atoms :  155 (6243 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t62_tops_2,conjecture,(
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
               => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ B ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ) )).

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
                 => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ B ) )
                    & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_tops_2])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( v1_partfun1 @ X25 @ X26 )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( v1_funct_1 @ X25 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('10',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('17',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('21',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('22',plain,(
    ! [X34: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('23',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','27'])).

thf('29',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','28'])).

thf('30',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('32',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_partfun1 @ X29 @ X28 )
      | ( ( k1_relat_1 @ X29 )
        = X28 )
      | ~ ( v4_relat_1 @ X29 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('37',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('44',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('45',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','38','45'])).

thf('47',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('48',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('49',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('50',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','54'])).

thf('56',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','57'])).

thf('59',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','60'])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('63',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('64',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','38','45'])).

thf('65',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','27'])).

thf('67',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_partfun1 @ X29 @ X28 )
      | ( ( k1_relat_1 @ X29 )
        = X28 )
      | ~ ( v4_relat_1 @ X29 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['36','37'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('72',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','72'])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

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

thf('79',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k2_relset_1 @ X36 @ X35 @ X37 )
       != X35 )
      | ~ ( v2_funct_1 @ X37 )
      | ( ( k2_tops_2 @ X36 @ X35 @ X37 )
        = ( k2_funct_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('80',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('84',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['82','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('92',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','38','45'])).

thf('94',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('97',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('98',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('99',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['96','99'])).

thf('101',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('102',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','38','45'])).

thf('105',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['80','81','94','95','105'])).

thf('107',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

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

thf('109',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v2_funct_1 @ X30 )
      | ( ( k2_relset_1 @ X32 @ X31 @ X30 )
       != X31 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('110',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('113',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('114',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['110','111','112','113','114'])).

thf('116',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('118',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('120',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('121',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('122',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('123',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('125',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('126',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('128',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['123','128'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('130',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('131',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('133',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k7_relat_1 @ X10 @ X11 ) )
      | ~ ( v4_relat_1 @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('134',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['36','37'])).

thf('136',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['36','37'])).

thf('138',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['136','139'])).

thf('141',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','38','45'])).

thf('142',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('144',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['143'])).

thf(t177_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf('145',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X14 @ ( k1_relat_1 @ X15 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X15 ) @ ( k9_relat_1 @ X15 @ X14 ) )
        = X14 )
      | ~ ( v2_funct_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t177_funct_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['142','146'])).

thf('148',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['36','37'])).

thf('151',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['147','148','149','150'])).

thf('152',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('153',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['131','151','152'])).

thf('154',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['118','153'])).

thf('155',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','73','107','154'])).

thf('156',plain,
    ( $false
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('158',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('159',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['126','127'])).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('161',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k9_relat_1 @ X12 @ X13 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X12 ) @ X13 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('162',plain,(
    ! [X9: $i] :
      ( ( ( k10_relat_1 @ X9 @ ( k2_relat_1 @ X9 ) )
        = ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k9_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['160','163'])).

thf('165',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['36','37'])).

thf('168',plain,
    ( ( k9_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['164','165','166','167'])).

thf('169',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['131','151','152'])).

thf('170',plain,
    ( ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('172',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['170','171'])).

thf('173',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['159','172'])).

thf('174',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['106'])).

thf('175',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('176',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('177',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('178',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['50'])).

thf('179',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['176','181'])).

thf('183',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['175','184'])).

thf('186',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('189',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','72'])).

thf('190',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','38','45'])).

thf('191',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('192',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('193',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['187','188','189','190','191','192'])).

thf('194',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['174','193'])).

thf('195',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['173','194'])).

thf('196',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['50'])).

thf('198',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['196','197'])).

thf('199',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['156','198'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B0LnWnhY8I
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:57:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.76/0.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.96  % Solved by: fo/fo7.sh
% 0.76/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.96  % done 468 iterations in 0.488s
% 0.76/0.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.96  % SZS output start Refutation
% 0.76/0.96  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.76/0.96  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.76/0.96  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.76/0.96  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.76/0.96  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.76/0.96  thf(sk_C_type, type, sk_C: $i).
% 0.76/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.96  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.76/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.96  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.76/0.96  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.76/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.96  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.96  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.76/0.96  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.96  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.76/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.96  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.76/0.96  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.76/0.96  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.96  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.76/0.96  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.76/0.96  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.76/0.96  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.76/0.96  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.76/0.96  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.96  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.76/0.96  thf(d3_struct_0, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.76/0.96  thf('0', plain,
% 0.76/0.96      (![X33 : $i]:
% 0.76/0.96         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.76/0.96      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.96  thf('1', plain,
% 0.76/0.96      (![X33 : $i]:
% 0.76/0.96         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.76/0.96      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.96  thf(t62_tops_2, conjecture,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( l1_struct_0 @ A ) =>
% 0.76/0.96       ( ![B:$i]:
% 0.76/0.96         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.76/0.96           ( ![C:$i]:
% 0.76/0.96             ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.96                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.96                 ( m1_subset_1 @
% 0.76/0.96                   C @ 
% 0.76/0.96                   ( k1_zfmisc_1 @
% 0.76/0.96                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.96               ( ( ( ( k2_relset_1 @
% 0.76/0.96                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.76/0.96                     ( k2_struct_0 @ B ) ) & 
% 0.76/0.96                   ( v2_funct_1 @ C ) ) =>
% 0.76/0.96                 ( ( ( k1_relset_1 @
% 0.76/0.96                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.76/0.96                       ( k2_tops_2 @
% 0.76/0.96                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.76/0.96                     ( k2_struct_0 @ B ) ) & 
% 0.76/0.96                   ( ( k2_relset_1 @
% 0.76/0.96                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.76/0.96                       ( k2_tops_2 @
% 0.76/0.96                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.76/0.96                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.76/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.96    (~( ![A:$i]:
% 0.76/0.96        ( ( l1_struct_0 @ A ) =>
% 0.76/0.96          ( ![B:$i]:
% 0.76/0.96            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.76/0.96              ( ![C:$i]:
% 0.76/0.96                ( ( ( v1_funct_1 @ C ) & 
% 0.76/0.96                    ( v1_funct_2 @
% 0.76/0.96                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.76/0.96                    ( m1_subset_1 @
% 0.76/0.96                      C @ 
% 0.76/0.96                      ( k1_zfmisc_1 @
% 0.76/0.96                        ( k2_zfmisc_1 @
% 0.76/0.96                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.76/0.96                  ( ( ( ( k2_relset_1 @
% 0.76/0.96                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.76/0.96                        ( k2_struct_0 @ B ) ) & 
% 0.76/0.96                      ( v2_funct_1 @ C ) ) =>
% 0.76/0.96                    ( ( ( k1_relset_1 @
% 0.76/0.96                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.76/0.96                          ( k2_tops_2 @
% 0.76/0.96                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.76/0.96                        ( k2_struct_0 @ B ) ) & 
% 0.76/0.96                      ( ( k2_relset_1 @
% 0.76/0.96                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.76/0.96                          ( k2_tops_2 @
% 0.76/0.96                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.76/0.96                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.76/0.96    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.76/0.96  thf('2', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ 
% 0.76/0.96        (k1_zfmisc_1 @ 
% 0.76/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('3', plain,
% 0.76/0.96      (((m1_subset_1 @ sk_C @ 
% 0.76/0.96         (k1_zfmisc_1 @ 
% 0.76/0.96          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.76/0.96        | ~ (l1_struct_0 @ sk_B))),
% 0.76/0.96      inference('sup+', [status(thm)], ['1', '2'])).
% 0.76/0.96  thf('4', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('5', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ 
% 0.76/0.96        (k1_zfmisc_1 @ 
% 0.76/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.76/0.96      inference('demod', [status(thm)], ['3', '4'])).
% 0.76/0.96  thf(cc5_funct_2, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.76/0.96       ( ![C:$i]:
% 0.76/0.96         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.96           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.76/0.96             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.76/0.96  thf('6', plain,
% 0.76/0.96      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.76/0.96          | (v1_partfun1 @ X25 @ X26)
% 0.76/0.96          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 0.76/0.96          | ~ (v1_funct_1 @ X25)
% 0.76/0.96          | (v1_xboole_0 @ X27))),
% 0.76/0.96      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.76/0.96  thf('7', plain,
% 0.76/0.96      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.76/0.96        | ~ (v1_funct_1 @ sk_C)
% 0.76/0.96        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.76/0.96        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['5', '6'])).
% 0.76/0.96  thf('8', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('9', plain,
% 0.76/0.96      (![X33 : $i]:
% 0.76/0.96         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.76/0.96      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.96  thf('10', plain,
% 0.76/0.96      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('11', plain,
% 0.76/0.96      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.76/0.96        | ~ (l1_struct_0 @ sk_B))),
% 0.76/0.96      inference('sup+', [status(thm)], ['9', '10'])).
% 0.76/0.96  thf('12', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('13', plain,
% 0.76/0.96      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.76/0.96      inference('demod', [status(thm)], ['11', '12'])).
% 0.76/0.96  thf('14', plain,
% 0.76/0.96      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.76/0.96        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.76/0.96  thf('15', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ 
% 0.76/0.96        (k1_zfmisc_1 @ 
% 0.76/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(redefinition_k2_relset_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.96       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.76/0.96  thf('16', plain,
% 0.76/0.96      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.76/0.96         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 0.76/0.96          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.76/0.96  thf('17', plain,
% 0.76/0.96      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.96         = (k2_relat_1 @ sk_C))),
% 0.76/0.96      inference('sup-', [status(thm)], ['15', '16'])).
% 0.76/0.96  thf('18', plain,
% 0.76/0.96      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.96         = (k2_struct_0 @ sk_B))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('19', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/0.96      inference('sup+', [status(thm)], ['17', '18'])).
% 0.76/0.96  thf('20', plain,
% 0.76/0.96      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.76/0.96        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('demod', [status(thm)], ['14', '19'])).
% 0.76/0.96  thf('21', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/0.96      inference('sup+', [status(thm)], ['17', '18'])).
% 0.76/0.96  thf(fc5_struct_0, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.76/0.96       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.76/0.96  thf('22', plain,
% 0.76/0.96      (![X34 : $i]:
% 0.76/0.96         (~ (v1_xboole_0 @ (k2_struct_0 @ X34))
% 0.76/0.96          | ~ (l1_struct_0 @ X34)
% 0.76/0.96          | (v2_struct_0 @ X34))),
% 0.76/0.96      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.76/0.96  thf('23', plain,
% 0.76/0.96      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.76/0.96        | (v2_struct_0 @ sk_B)
% 0.76/0.96        | ~ (l1_struct_0 @ sk_B))),
% 0.76/0.96      inference('sup-', [status(thm)], ['21', '22'])).
% 0.76/0.96  thf('24', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('25', plain,
% 0.76/0.96      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.76/0.96      inference('demod', [status(thm)], ['23', '24'])).
% 0.76/0.96  thf('26', plain, (~ (v2_struct_0 @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('27', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.76/0.96      inference('clc', [status(thm)], ['25', '26'])).
% 0.76/0.96  thf('28', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.76/0.96      inference('clc', [status(thm)], ['20', '27'])).
% 0.76/0.96  thf('29', plain,
% 0.76/0.96      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.96      inference('sup+', [status(thm)], ['0', '28'])).
% 0.76/0.96  thf('30', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('31', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['29', '30'])).
% 0.76/0.96  thf(d4_partfun1, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.76/0.96       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.76/0.96  thf('32', plain,
% 0.76/0.96      (![X28 : $i, X29 : $i]:
% 0.76/0.96         (~ (v1_partfun1 @ X29 @ X28)
% 0.76/0.96          | ((k1_relat_1 @ X29) = (X28))
% 0.76/0.96          | ~ (v4_relat_1 @ X29 @ X28)
% 0.76/0.96          | ~ (v1_relat_1 @ X29))),
% 0.76/0.96      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.76/0.96  thf('33', plain,
% 0.76/0.96      ((~ (v1_relat_1 @ sk_C)
% 0.76/0.96        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.76/0.96        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['31', '32'])).
% 0.76/0.96  thf('34', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ 
% 0.76/0.96        (k1_zfmisc_1 @ 
% 0.76/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf(cc2_relat_1, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( v1_relat_1 @ A ) =>
% 0.76/0.96       ( ![B:$i]:
% 0.76/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.76/0.96  thf('35', plain,
% 0.76/0.96      (![X3 : $i, X4 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.76/0.96          | (v1_relat_1 @ X3)
% 0.76/0.96          | ~ (v1_relat_1 @ X4))),
% 0.76/0.96      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.76/0.96  thf('36', plain,
% 0.76/0.96      ((~ (v1_relat_1 @ 
% 0.76/0.96           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.76/0.96        | (v1_relat_1 @ sk_C))),
% 0.76/0.96      inference('sup-', [status(thm)], ['34', '35'])).
% 0.76/0.96  thf(fc6_relat_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.76/0.96  thf('37', plain,
% 0.76/0.96      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.76/0.96      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.76/0.96  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.96      inference('demod', [status(thm)], ['36', '37'])).
% 0.76/0.96  thf('39', plain,
% 0.76/0.96      (![X33 : $i]:
% 0.76/0.96         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.76/0.96      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.96  thf('40', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ 
% 0.76/0.96        (k1_zfmisc_1 @ 
% 0.76/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('41', plain,
% 0.76/0.96      (((m1_subset_1 @ sk_C @ 
% 0.76/0.96         (k1_zfmisc_1 @ 
% 0.76/0.96          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.76/0.96        | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.96      inference('sup+', [status(thm)], ['39', '40'])).
% 0.76/0.96  thf('42', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('43', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ 
% 0.76/0.96        (k1_zfmisc_1 @ 
% 0.76/0.96         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.96      inference('demod', [status(thm)], ['41', '42'])).
% 0.76/0.96  thf(cc2_relset_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.96       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.76/0.96  thf('44', plain,
% 0.76/0.96      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.76/0.96         ((v4_relat_1 @ X16 @ X17)
% 0.76/0.96          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.76/0.96      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.76/0.96  thf('45', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.76/0.96      inference('sup-', [status(thm)], ['43', '44'])).
% 0.76/0.96  thf('46', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['33', '38', '45'])).
% 0.76/0.96  thf('47', plain,
% 0.76/0.96      (![X33 : $i]:
% 0.76/0.96         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.76/0.96      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.96  thf('48', plain,
% 0.76/0.96      (![X33 : $i]:
% 0.76/0.96         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.76/0.96      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.96  thf('49', plain,
% 0.76/0.96      (![X33 : $i]:
% 0.76/0.96         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.76/0.96      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.96  thf('50', plain,
% 0.76/0.96      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96          != (k2_struct_0 @ sk_B))
% 0.76/0.96        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96            != (k2_struct_0 @ sk_A)))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('51', plain,
% 0.76/0.96      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96          != (k2_struct_0 @ sk_A)))
% 0.76/0.96         <= (~
% 0.76/0.96             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96                = (k2_struct_0 @ sk_A))))),
% 0.76/0.96      inference('split', [status(esa)], ['50'])).
% 0.76/0.96  thf('52', plain,
% 0.76/0.96      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96           != (k2_struct_0 @ sk_A))
% 0.76/0.96         | ~ (l1_struct_0 @ sk_B)))
% 0.76/0.96         <= (~
% 0.76/0.96             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96                = (k2_struct_0 @ sk_A))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['49', '51'])).
% 0.76/0.96  thf('53', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('54', plain,
% 0.76/0.96      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96          != (k2_struct_0 @ sk_A)))
% 0.76/0.96         <= (~
% 0.76/0.96             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96                = (k2_struct_0 @ sk_A))))),
% 0.76/0.96      inference('demod', [status(thm)], ['52', '53'])).
% 0.76/0.96  thf('55', plain,
% 0.76/0.96      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.76/0.96           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96           != (k2_struct_0 @ sk_A))
% 0.76/0.96         | ~ (l1_struct_0 @ sk_A)))
% 0.76/0.96         <= (~
% 0.76/0.96             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96                = (k2_struct_0 @ sk_A))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['48', '54'])).
% 0.76/0.96  thf('56', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('57', plain,
% 0.76/0.96      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.76/0.96          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96          != (k2_struct_0 @ sk_A)))
% 0.76/0.96         <= (~
% 0.76/0.96             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96                = (k2_struct_0 @ sk_A))))),
% 0.76/0.96      inference('demod', [status(thm)], ['55', '56'])).
% 0.76/0.96  thf('58', plain,
% 0.76/0.96      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.76/0.96           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96           != (k2_struct_0 @ sk_A))
% 0.76/0.96         | ~ (l1_struct_0 @ sk_B)))
% 0.76/0.96         <= (~
% 0.76/0.96             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96                = (k2_struct_0 @ sk_A))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['47', '57'])).
% 0.76/0.96  thf('59', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('60', plain,
% 0.76/0.96      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.76/0.96          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96          != (k2_struct_0 @ sk_A)))
% 0.76/0.96         <= (~
% 0.76/0.96             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96                = (k2_struct_0 @ sk_A))))),
% 0.76/0.96      inference('demod', [status(thm)], ['58', '59'])).
% 0.76/0.96  thf('61', plain,
% 0.76/0.96      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.76/0.96          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96          != (k2_struct_0 @ sk_A)))
% 0.76/0.96         <= (~
% 0.76/0.96             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96                = (k2_struct_0 @ sk_A))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['46', '60'])).
% 0.76/0.96  thf('62', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/0.96      inference('sup+', [status(thm)], ['17', '18'])).
% 0.76/0.96  thf('63', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/0.96      inference('sup+', [status(thm)], ['17', '18'])).
% 0.76/0.96  thf('64', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['33', '38', '45'])).
% 0.76/0.96  thf('65', plain,
% 0.76/0.96      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.76/0.96          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.76/0.96          != (k1_relat_1 @ sk_C)))
% 0.76/0.96         <= (~
% 0.76/0.96             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96                = (k2_struct_0 @ sk_A))))),
% 0.76/0.96      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 0.76/0.96  thf('66', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.76/0.96      inference('clc', [status(thm)], ['20', '27'])).
% 0.76/0.96  thf('67', plain,
% 0.76/0.96      (![X28 : $i, X29 : $i]:
% 0.76/0.96         (~ (v1_partfun1 @ X29 @ X28)
% 0.76/0.96          | ((k1_relat_1 @ X29) = (X28))
% 0.76/0.96          | ~ (v4_relat_1 @ X29 @ X28)
% 0.76/0.96          | ~ (v1_relat_1 @ X29))),
% 0.76/0.96      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.76/0.96  thf('68', plain,
% 0.76/0.96      ((~ (v1_relat_1 @ sk_C)
% 0.76/0.96        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.76/0.96        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['66', '67'])).
% 0.76/0.96  thf('69', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.96      inference('demod', [status(thm)], ['36', '37'])).
% 0.76/0.96  thf('70', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ 
% 0.76/0.96        (k1_zfmisc_1 @ 
% 0.76/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('71', plain,
% 0.76/0.96      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.76/0.96         ((v4_relat_1 @ X16 @ X17)
% 0.76/0.96          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.76/0.96      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.76/0.96  thf('72', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.76/0.96      inference('sup-', [status(thm)], ['70', '71'])).
% 0.76/0.96  thf('73', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['68', '69', '72'])).
% 0.76/0.96  thf('74', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ 
% 0.76/0.96        (k1_zfmisc_1 @ 
% 0.76/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.76/0.96      inference('demod', [status(thm)], ['3', '4'])).
% 0.76/0.96  thf('75', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/0.96      inference('sup+', [status(thm)], ['17', '18'])).
% 0.76/0.96  thf('76', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ 
% 0.76/0.96        (k1_zfmisc_1 @ 
% 0.76/0.96         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.76/0.96      inference('demod', [status(thm)], ['74', '75'])).
% 0.76/0.96  thf('77', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['68', '69', '72'])).
% 0.76/0.96  thf('78', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ 
% 0.76/0.96        (k1_zfmisc_1 @ 
% 0.76/0.96         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.76/0.96      inference('demod', [status(thm)], ['76', '77'])).
% 0.76/0.96  thf(d4_tops_2, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.76/0.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.96       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.76/0.96         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.76/0.96  thf('79', plain,
% 0.76/0.96      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.76/0.96         (((k2_relset_1 @ X36 @ X35 @ X37) != (X35))
% 0.76/0.96          | ~ (v2_funct_1 @ X37)
% 0.76/0.96          | ((k2_tops_2 @ X36 @ X35 @ X37) = (k2_funct_1 @ X37))
% 0.76/0.96          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.76/0.96          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 0.76/0.96          | ~ (v1_funct_1 @ X37))),
% 0.76/0.96      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.76/0.96  thf('80', plain,
% 0.76/0.96      ((~ (v1_funct_1 @ sk_C)
% 0.76/0.96        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.76/0.96        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.76/0.96            = (k2_funct_1 @ sk_C))
% 0.76/0.96        | ~ (v2_funct_1 @ sk_C)
% 0.76/0.96        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.76/0.96            != (k2_relat_1 @ sk_C)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['78', '79'])).
% 0.76/0.96  thf('81', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('82', plain,
% 0.76/0.96      (![X33 : $i]:
% 0.76/0.96         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.76/0.96      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.96  thf('83', plain,
% 0.76/0.96      (![X33 : $i]:
% 0.76/0.96         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.76/0.96      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.96  thf('84', plain,
% 0.76/0.96      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('85', plain,
% 0.76/0.96      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.76/0.96        | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.96      inference('sup+', [status(thm)], ['83', '84'])).
% 0.76/0.96  thf('86', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('87', plain,
% 0.76/0.96      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.76/0.96      inference('demod', [status(thm)], ['85', '86'])).
% 0.76/0.96  thf('88', plain,
% 0.76/0.96      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.76/0.96        | ~ (l1_struct_0 @ sk_B))),
% 0.76/0.96      inference('sup+', [status(thm)], ['82', '87'])).
% 0.76/0.96  thf('89', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('90', plain,
% 0.76/0.96      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.76/0.96      inference('demod', [status(thm)], ['88', '89'])).
% 0.76/0.96  thf('91', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/0.96      inference('sup+', [status(thm)], ['17', '18'])).
% 0.76/0.96  thf('92', plain,
% 0.76/0.96      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.76/0.96      inference('demod', [status(thm)], ['90', '91'])).
% 0.76/0.96  thf('93', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['33', '38', '45'])).
% 0.76/0.96  thf('94', plain,
% 0.76/0.96      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.76/0.96      inference('demod', [status(thm)], ['92', '93'])).
% 0.76/0.96  thf('95', plain, ((v2_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('96', plain,
% 0.76/0.96      (![X33 : $i]:
% 0.76/0.96         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.76/0.96      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.96  thf('97', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ 
% 0.76/0.96        (k1_zfmisc_1 @ 
% 0.76/0.96         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.76/0.96      inference('demod', [status(thm)], ['41', '42'])).
% 0.76/0.96  thf('98', plain,
% 0.76/0.96      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.76/0.96         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 0.76/0.96          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.76/0.96  thf('99', plain,
% 0.76/0.96      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.76/0.96         = (k2_relat_1 @ sk_C))),
% 0.76/0.96      inference('sup-', [status(thm)], ['97', '98'])).
% 0.76/0.96  thf('100', plain,
% 0.76/0.96      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.76/0.96          = (k2_relat_1 @ sk_C))
% 0.76/0.96        | ~ (l1_struct_0 @ sk_B))),
% 0.76/0.96      inference('sup+', [status(thm)], ['96', '99'])).
% 0.76/0.96  thf('101', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/0.96      inference('sup+', [status(thm)], ['17', '18'])).
% 0.76/0.96  thf('102', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('103', plain,
% 0.76/0.96      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.76/0.96         = (k2_relat_1 @ sk_C))),
% 0.76/0.96      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.76/0.96  thf('104', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['33', '38', '45'])).
% 0.76/0.96  thf('105', plain,
% 0.76/0.96      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.76/0.96         = (k2_relat_1 @ sk_C))),
% 0.76/0.96      inference('demod', [status(thm)], ['103', '104'])).
% 0.76/0.96  thf('106', plain,
% 0.76/0.96      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.76/0.96          = (k2_funct_1 @ sk_C))
% 0.76/0.96        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.76/0.96      inference('demod', [status(thm)], ['80', '81', '94', '95', '105'])).
% 0.76/0.96  thf('107', plain,
% 0.76/0.96      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.76/0.96         = (k2_funct_1 @ sk_C))),
% 0.76/0.96      inference('simplify', [status(thm)], ['106'])).
% 0.76/0.96  thf('108', plain,
% 0.76/0.96      ((m1_subset_1 @ sk_C @ 
% 0.76/0.96        (k1_zfmisc_1 @ 
% 0.76/0.96         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.76/0.96      inference('demod', [status(thm)], ['76', '77'])).
% 0.76/0.96  thf(t31_funct_2, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.76/0.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.96       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.76/0.96         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.76/0.96           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.76/0.96           ( m1_subset_1 @
% 0.76/0.96             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.76/0.96  thf('109', plain,
% 0.76/0.96      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.76/0.96         (~ (v2_funct_1 @ X30)
% 0.76/0.96          | ((k2_relset_1 @ X32 @ X31 @ X30) != (X31))
% 0.76/0.96          | (m1_subset_1 @ (k2_funct_1 @ X30) @ 
% 0.76/0.96             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.76/0.96          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 0.76/0.96          | ~ (v1_funct_2 @ X30 @ X32 @ X31)
% 0.76/0.96          | ~ (v1_funct_1 @ X30))),
% 0.76/0.96      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.76/0.96  thf('110', plain,
% 0.76/0.96      ((~ (v1_funct_1 @ sk_C)
% 0.76/0.96        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.76/0.96        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.76/0.96           (k1_zfmisc_1 @ 
% 0.76/0.96            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.76/0.96        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.76/0.96            != (k2_relat_1 @ sk_C))
% 0.76/0.96        | ~ (v2_funct_1 @ sk_C))),
% 0.76/0.96      inference('sup-', [status(thm)], ['108', '109'])).
% 0.76/0.96  thf('111', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('112', plain,
% 0.76/0.96      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.76/0.96      inference('demod', [status(thm)], ['92', '93'])).
% 0.76/0.96  thf('113', plain,
% 0.76/0.96      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.76/0.96         = (k2_relat_1 @ sk_C))),
% 0.76/0.96      inference('demod', [status(thm)], ['103', '104'])).
% 0.76/0.96  thf('114', plain, ((v2_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('115', plain,
% 0.76/0.96      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.76/0.96         (k1_zfmisc_1 @ 
% 0.76/0.96          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.76/0.96        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.76/0.96      inference('demod', [status(thm)], ['110', '111', '112', '113', '114'])).
% 0.76/0.96  thf('116', plain,
% 0.76/0.96      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.76/0.96        (k1_zfmisc_1 @ 
% 0.76/0.96         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.76/0.96      inference('simplify', [status(thm)], ['115'])).
% 0.76/0.96  thf('117', plain,
% 0.76/0.96      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.76/0.96         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 0.76/0.96          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.76/0.96  thf('118', plain,
% 0.76/0.96      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.76/0.96         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['116', '117'])).
% 0.76/0.96  thf('119', plain,
% 0.76/0.96      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.76/0.96        (k1_zfmisc_1 @ 
% 0.76/0.96         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.76/0.96      inference('simplify', [status(thm)], ['115'])).
% 0.76/0.96  thf('120', plain,
% 0.76/0.96      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.76/0.96         ((v4_relat_1 @ X16 @ X17)
% 0.76/0.96          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.76/0.96      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.76/0.96  thf('121', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.76/0.96      inference('sup-', [status(thm)], ['119', '120'])).
% 0.76/0.96  thf(t209_relat_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.76/0.96       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.76/0.96  thf('122', plain,
% 0.76/0.96      (![X10 : $i, X11 : $i]:
% 0.76/0.96         (((X10) = (k7_relat_1 @ X10 @ X11))
% 0.76/0.96          | ~ (v4_relat_1 @ X10 @ X11)
% 0.76/0.96          | ~ (v1_relat_1 @ X10))),
% 0.76/0.96      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.76/0.96  thf('123', plain,
% 0.76/0.96      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.76/0.96        | ((k2_funct_1 @ sk_C)
% 0.76/0.96            = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['121', '122'])).
% 0.76/0.96  thf('124', plain,
% 0.76/0.96      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.76/0.96        (k1_zfmisc_1 @ 
% 0.76/0.96         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.76/0.96      inference('simplify', [status(thm)], ['115'])).
% 0.76/0.96  thf('125', plain,
% 0.76/0.96      (![X3 : $i, X4 : $i]:
% 0.76/0.96         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.76/0.96          | (v1_relat_1 @ X3)
% 0.76/0.96          | ~ (v1_relat_1 @ X4))),
% 0.76/0.96      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.76/0.96  thf('126', plain,
% 0.76/0.96      ((~ (v1_relat_1 @ 
% 0.76/0.96           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))
% 0.76/0.96        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['124', '125'])).
% 0.76/0.96  thf('127', plain,
% 0.76/0.96      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.76/0.96      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.76/0.96  thf('128', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.76/0.96      inference('demod', [status(thm)], ['126', '127'])).
% 0.76/0.96  thf('129', plain,
% 0.76/0.96      (((k2_funct_1 @ sk_C)
% 0.76/0.96         = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.76/0.96      inference('demod', [status(thm)], ['123', '128'])).
% 0.76/0.96  thf(t148_relat_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( v1_relat_1 @ B ) =>
% 0.76/0.96       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.76/0.96  thf('130', plain,
% 0.76/0.96      (![X7 : $i, X8 : $i]:
% 0.76/0.96         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.76/0.96          | ~ (v1_relat_1 @ X7))),
% 0.76/0.96      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.76/0.96  thf('131', plain,
% 0.76/0.96      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 0.76/0.96          = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C)))
% 0.76/0.96        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.76/0.96      inference('sup+', [status(thm)], ['129', '130'])).
% 0.76/0.96  thf('132', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.76/0.96      inference('sup-', [status(thm)], ['43', '44'])).
% 0.76/0.96  thf('133', plain,
% 0.76/0.96      (![X10 : $i, X11 : $i]:
% 0.76/0.96         (((X10) = (k7_relat_1 @ X10 @ X11))
% 0.76/0.96          | ~ (v4_relat_1 @ X10 @ X11)
% 0.76/0.96          | ~ (v1_relat_1 @ X10))),
% 0.76/0.96      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.76/0.96  thf('134', plain,
% 0.76/0.96      ((~ (v1_relat_1 @ sk_C)
% 0.76/0.96        | ((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['132', '133'])).
% 0.76/0.96  thf('135', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.96      inference('demod', [status(thm)], ['36', '37'])).
% 0.76/0.96  thf('136', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.76/0.96      inference('demod', [status(thm)], ['134', '135'])).
% 0.76/0.96  thf('137', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.96      inference('demod', [status(thm)], ['36', '37'])).
% 0.76/0.96  thf('138', plain,
% 0.76/0.96      (![X7 : $i, X8 : $i]:
% 0.76/0.96         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.76/0.96          | ~ (v1_relat_1 @ X7))),
% 0.76/0.96      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.76/0.96  thf('139', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         ((k2_relat_1 @ (k7_relat_1 @ sk_C @ X0)) = (k9_relat_1 @ sk_C @ X0))),
% 0.76/0.96      inference('sup-', [status(thm)], ['137', '138'])).
% 0.76/0.96  thf('140', plain,
% 0.76/0.96      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.76/0.96      inference('sup+', [status(thm)], ['136', '139'])).
% 0.76/0.96  thf('141', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['33', '38', '45'])).
% 0.76/0.96  thf('142', plain,
% 0.76/0.96      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.76/0.96      inference('demod', [status(thm)], ['140', '141'])).
% 0.76/0.96  thf(d10_xboole_0, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.76/0.96  thf('143', plain,
% 0.76/0.96      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.76/0.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/0.96  thf('144', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.76/0.96      inference('simplify', [status(thm)], ['143'])).
% 0.76/0.96  thf(t177_funct_1, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.76/0.96       ( ![B:$i]:
% 0.76/0.96         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.76/0.96           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 0.76/0.96             ( B ) ) ) ) ))).
% 0.76/0.96  thf('145', plain,
% 0.76/0.96      (![X14 : $i, X15 : $i]:
% 0.76/0.96         (~ (r1_tarski @ X14 @ (k1_relat_1 @ X15))
% 0.76/0.96          | ((k9_relat_1 @ (k2_funct_1 @ X15) @ (k9_relat_1 @ X15 @ X14))
% 0.76/0.96              = (X14))
% 0.76/0.96          | ~ (v2_funct_1 @ X15)
% 0.76/0.96          | ~ (v1_funct_1 @ X15)
% 0.76/0.96          | ~ (v1_relat_1 @ X15))),
% 0.76/0.96      inference('cnf', [status(esa)], [t177_funct_1])).
% 0.76/0.96  thf('146', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (~ (v1_relat_1 @ X0)
% 0.76/0.96          | ~ (v1_funct_1 @ X0)
% 0.76/0.96          | ~ (v2_funct_1 @ X0)
% 0.76/0.96          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.76/0.96              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) = (k1_relat_1 @ X0)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['144', '145'])).
% 0.76/0.96  thf('147', plain,
% 0.76/0.96      ((((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.76/0.96          = (k1_relat_1 @ sk_C))
% 0.76/0.96        | ~ (v2_funct_1 @ sk_C)
% 0.76/0.96        | ~ (v1_funct_1 @ sk_C)
% 0.76/0.96        | ~ (v1_relat_1 @ sk_C))),
% 0.76/0.96      inference('sup+', [status(thm)], ['142', '146'])).
% 0.76/0.96  thf('148', plain, ((v2_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('149', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('150', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.96      inference('demod', [status(thm)], ['36', '37'])).
% 0.76/0.96  thf('151', plain,
% 0.76/0.96      (((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.76/0.96         = (k1_relat_1 @ sk_C))),
% 0.76/0.96      inference('demod', [status(thm)], ['147', '148', '149', '150'])).
% 0.76/0.96  thf('152', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.76/0.96      inference('demod', [status(thm)], ['126', '127'])).
% 0.76/0.96  thf('153', plain,
% 0.76/0.96      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.76/0.96      inference('demod', [status(thm)], ['131', '151', '152'])).
% 0.76/0.96  thf('154', plain,
% 0.76/0.96      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.76/0.96         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.76/0.96      inference('demod', [status(thm)], ['118', '153'])).
% 0.76/0.96  thf('155', plain,
% 0.76/0.96      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 0.76/0.96         <= (~
% 0.76/0.96             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96                = (k2_struct_0 @ sk_A))))),
% 0.76/0.96      inference('demod', [status(thm)], ['65', '73', '107', '154'])).
% 0.76/0.96  thf('156', plain,
% 0.76/0.96      (($false)
% 0.76/0.96         <= (~
% 0.76/0.96             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96                = (k2_struct_0 @ sk_A))))),
% 0.76/0.96      inference('simplify', [status(thm)], ['155'])).
% 0.76/0.96  thf('157', plain,
% 0.76/0.96      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.76/0.96        (k1_zfmisc_1 @ 
% 0.76/0.96         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.76/0.96      inference('simplify', [status(thm)], ['115'])).
% 0.76/0.96  thf(redefinition_k1_relset_1, axiom,
% 0.76/0.96    (![A:$i,B:$i,C:$i]:
% 0.76/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.96       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.76/0.96  thf('158', plain,
% 0.76/0.96      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.76/0.96         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.76/0.96          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.76/0.96      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.76/0.96  thf('159', plain,
% 0.76/0.96      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.76/0.96         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.76/0.96      inference('sup-', [status(thm)], ['157', '158'])).
% 0.76/0.96  thf('160', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.76/0.96      inference('demod', [status(thm)], ['126', '127'])).
% 0.76/0.96  thf(t154_funct_1, axiom,
% 0.76/0.96    (![A:$i,B:$i]:
% 0.76/0.96     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.76/0.96       ( ( v2_funct_1 @ B ) =>
% 0.76/0.96         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.76/0.96  thf('161', plain,
% 0.76/0.96      (![X12 : $i, X13 : $i]:
% 0.76/0.96         (~ (v2_funct_1 @ X12)
% 0.76/0.96          | ((k9_relat_1 @ X12 @ X13)
% 0.76/0.96              = (k10_relat_1 @ (k2_funct_1 @ X12) @ X13))
% 0.76/0.96          | ~ (v1_funct_1 @ X12)
% 0.76/0.96          | ~ (v1_relat_1 @ X12))),
% 0.76/0.96      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.76/0.96  thf(t169_relat_1, axiom,
% 0.76/0.96    (![A:$i]:
% 0.76/0.96     ( ( v1_relat_1 @ A ) =>
% 0.76/0.96       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.76/0.96  thf('162', plain,
% 0.76/0.96      (![X9 : $i]:
% 0.76/0.96         (((k10_relat_1 @ X9 @ (k2_relat_1 @ X9)) = (k1_relat_1 @ X9))
% 0.76/0.96          | ~ (v1_relat_1 @ X9))),
% 0.76/0.96      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.76/0.96  thf('163', plain,
% 0.76/0.96      (![X0 : $i]:
% 0.76/0.96         (((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.76/0.96            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.76/0.96          | ~ (v1_relat_1 @ X0)
% 0.76/0.96          | ~ (v1_funct_1 @ X0)
% 0.76/0.96          | ~ (v2_funct_1 @ X0)
% 0.76/0.96          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.76/0.96      inference('sup+', [status(thm)], ['161', '162'])).
% 0.76/0.96  thf('164', plain,
% 0.76/0.96      ((~ (v2_funct_1 @ sk_C)
% 0.76/0.96        | ~ (v1_funct_1 @ sk_C)
% 0.76/0.96        | ~ (v1_relat_1 @ sk_C)
% 0.76/0.96        | ((k9_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.76/0.96            = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['160', '163'])).
% 0.76/0.96  thf('165', plain, ((v2_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('166', plain, ((v1_funct_1 @ sk_C)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('167', plain, ((v1_relat_1 @ sk_C)),
% 0.76/0.96      inference('demod', [status(thm)], ['36', '37'])).
% 0.76/0.96  thf('168', plain,
% 0.76/0.96      (((k9_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.76/0.96         = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.76/0.96      inference('demod', [status(thm)], ['164', '165', '166', '167'])).
% 0.76/0.96  thf('169', plain,
% 0.76/0.96      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.76/0.96      inference('demod', [status(thm)], ['131', '151', '152'])).
% 0.76/0.96  thf('170', plain,
% 0.76/0.96      (((k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.76/0.96         = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.76/0.96      inference('demod', [status(thm)], ['168', '169'])).
% 0.76/0.96  thf('171', plain,
% 0.76/0.96      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.76/0.96      inference('demod', [status(thm)], ['140', '141'])).
% 0.76/0.96  thf('172', plain,
% 0.76/0.96      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.76/0.96      inference('sup+', [status(thm)], ['170', '171'])).
% 0.76/0.96  thf('173', plain,
% 0.76/0.96      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.76/0.96         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.76/0.96      inference('demod', [status(thm)], ['159', '172'])).
% 0.76/0.96  thf('174', plain,
% 0.76/0.96      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.76/0.96         = (k2_funct_1 @ sk_C))),
% 0.76/0.96      inference('simplify', [status(thm)], ['106'])).
% 0.76/0.96  thf('175', plain,
% 0.76/0.96      (![X33 : $i]:
% 0.76/0.96         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.76/0.96      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.96  thf('176', plain,
% 0.76/0.96      (![X33 : $i]:
% 0.76/0.96         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.76/0.96      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.96  thf('177', plain,
% 0.76/0.96      (![X33 : $i]:
% 0.76/0.96         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.76/0.96      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.76/0.96  thf('178', plain,
% 0.76/0.96      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96          != (k2_struct_0 @ sk_B)))
% 0.76/0.96         <= (~
% 0.76/0.96             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96                = (k2_struct_0 @ sk_B))))),
% 0.76/0.96      inference('split', [status(esa)], ['50'])).
% 0.76/0.96  thf('179', plain,
% 0.76/0.96      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96           != (k2_struct_0 @ sk_B))
% 0.76/0.96         | ~ (l1_struct_0 @ sk_B)))
% 0.76/0.96         <= (~
% 0.76/0.96             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96                = (k2_struct_0 @ sk_B))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['177', '178'])).
% 0.76/0.96  thf('180', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('181', plain,
% 0.76/0.96      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96          != (k2_struct_0 @ sk_B)))
% 0.76/0.96         <= (~
% 0.76/0.96             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96                = (k2_struct_0 @ sk_B))))),
% 0.76/0.96      inference('demod', [status(thm)], ['179', '180'])).
% 0.76/0.96  thf('182', plain,
% 0.76/0.96      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96           != (k2_struct_0 @ sk_B))
% 0.76/0.96         | ~ (l1_struct_0 @ sk_A)))
% 0.76/0.96         <= (~
% 0.76/0.96             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96                = (k2_struct_0 @ sk_B))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['176', '181'])).
% 0.76/0.96  thf('183', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('184', plain,
% 0.76/0.96      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96          != (k2_struct_0 @ sk_B)))
% 0.76/0.96         <= (~
% 0.76/0.96             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96                = (k2_struct_0 @ sk_B))))),
% 0.76/0.96      inference('demod', [status(thm)], ['182', '183'])).
% 0.76/0.96  thf('185', plain,
% 0.76/0.96      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96           != (k2_struct_0 @ sk_B))
% 0.76/0.96         | ~ (l1_struct_0 @ sk_B)))
% 0.76/0.96         <= (~
% 0.76/0.96             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96                = (k2_struct_0 @ sk_B))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['175', '184'])).
% 0.76/0.96  thf('186', plain, ((l1_struct_0 @ sk_B)),
% 0.76/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.96  thf('187', plain,
% 0.76/0.96      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96          != (k2_struct_0 @ sk_B)))
% 0.76/0.96         <= (~
% 0.76/0.96             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96                = (k2_struct_0 @ sk_B))))),
% 0.76/0.96      inference('demod', [status(thm)], ['185', '186'])).
% 0.76/0.96  thf('188', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/0.96      inference('sup+', [status(thm)], ['17', '18'])).
% 0.76/0.96  thf('189', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['68', '69', '72'])).
% 0.76/0.96  thf('190', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.76/0.96      inference('demod', [status(thm)], ['33', '38', '45'])).
% 0.76/0.96  thf('191', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/0.96      inference('sup+', [status(thm)], ['17', '18'])).
% 0.76/0.96  thf('192', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.76/0.96      inference('sup+', [status(thm)], ['17', '18'])).
% 0.76/0.96  thf('193', plain,
% 0.76/0.96      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.76/0.96          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.76/0.96          != (k2_relat_1 @ sk_C)))
% 0.76/0.96         <= (~
% 0.76/0.96             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96                = (k2_struct_0 @ sk_B))))),
% 0.76/0.96      inference('demod', [status(thm)],
% 0.76/0.96                ['187', '188', '189', '190', '191', '192'])).
% 0.76/0.96  thf('194', plain,
% 0.76/0.96      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.76/0.96          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.76/0.96         <= (~
% 0.76/0.96             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96                = (k2_struct_0 @ sk_B))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['174', '193'])).
% 0.76/0.96  thf('195', plain,
% 0.76/0.96      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))
% 0.76/0.96         <= (~
% 0.76/0.96             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96                = (k2_struct_0 @ sk_B))))),
% 0.76/0.96      inference('sup-', [status(thm)], ['173', '194'])).
% 0.76/0.96  thf('196', plain,
% 0.76/0.96      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96          = (k2_struct_0 @ sk_B)))),
% 0.76/0.96      inference('simplify', [status(thm)], ['195'])).
% 0.76/0.96  thf('197', plain,
% 0.76/0.96      (~
% 0.76/0.96       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96          = (k2_struct_0 @ sk_A))) | 
% 0.76/0.96       ~
% 0.76/0.96       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96          = (k2_struct_0 @ sk_B)))),
% 0.76/0.96      inference('split', [status(esa)], ['50'])).
% 0.76/0.96  thf('198', plain,
% 0.76/0.96      (~
% 0.76/0.96       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.76/0.96          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.76/0.96          = (k2_struct_0 @ sk_A)))),
% 0.76/0.96      inference('sat_resolution*', [status(thm)], ['196', '197'])).
% 0.76/0.96  thf('199', plain, ($false),
% 0.76/0.96      inference('simpl_trail', [status(thm)], ['156', '198'])).
% 0.76/0.96  
% 0.76/0.96  % SZS output end Refutation
% 0.76/0.96  
% 0.76/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
