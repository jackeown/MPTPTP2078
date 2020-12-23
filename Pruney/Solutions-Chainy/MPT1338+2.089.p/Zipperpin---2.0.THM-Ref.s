%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zAmrTmHP0B

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:02 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :  247 ( 861 expanded)
%              Number of leaves         :   43 ( 267 expanded)
%              Depth                    :   23
%              Number of atoms          : 2320 (22032 expanded)
%              Number of equality atoms :  184 (1230 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( ( k2_relat_1 @ X4 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
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

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('13',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['10','15'])).

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

thf('17',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k2_relset_1 @ X26 @ X25 @ X27 )
       != X25 )
      | ~ ( v2_funct_1 @ X27 )
      | ( ( k2_tops_2 @ X26 @ X25 @ X27 )
        = ( k2_funct_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('21',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('30',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('32',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_funct_1 @ X5 )
        = ( k4_relat_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
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
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['33','38','39'])).

thf('41',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('43',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('44',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','47'])).

thf('49',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('53',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['18','19','30','40','41','53'])).

thf('55',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('57',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('58',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('67',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('68',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','68'])).

thf('70',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','69'])).

thf('71',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('72',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('75',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
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

thf('76',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('77',plain,(
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

thf('78',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X17 @ X18 )
      | ( zip_tseitin_1 @ X19 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('79',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_funct_2 @ X16 @ X14 @ X15 )
      | ( X14
        = ( k1_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_1 @ X16 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('83',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('85',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('86',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['83','86'])).

thf('88',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','87'])).

thf('89',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['75','88'])).

thf('90',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('91',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['74','92'])).

thf('94',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['54'])).

thf('97',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('98',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('99',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('100',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['58'])).

thf('101',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','106'])).

thf('108',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('111',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('112',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['109','110','111'])).

thf('113',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','112'])).

thf('114',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('115',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['118','119'])).

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

thf('121',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relset_1 @ X22 @ X21 @ X20 )
       != X21 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('122',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('125',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('130',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['33','38','39'])).

thf('132',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('133',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('138',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('139',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['122','123','130','131','139','140'])).

thf('142',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('144',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['36','37'])).

thf('146',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('147',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['144','147'])).

thf('149',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['113','148'])).

thf('150',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k1_relat_1 @ sk_C ) )
      | ( ( k2_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','149'])).

thf('151',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('153',plain,(
    ! [X24: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('154',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['151','158'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('160',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('161',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['58'])).

thf('163',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['161','162'])).

thf('164',plain,(
    ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['73','163'])).

thf('165',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('166',plain,(
    ! [X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('167',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( zip_tseitin_0 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('170',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['83','86'])).

thf('172',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['165','172'])).

thf('174',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('175',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['173','174','175'])).

thf('177',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('178',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('179',plain,(
    ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['164','178'])).

thf('180',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('181',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relset_1 @ X22 @ X21 @ X20 )
       != X21 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X20 @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('182',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('185',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['33','38','39'])).

thf('186',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('187',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['182','183','184','185','186','187'])).

thf('189',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('191',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['176','177'])).

thf('192',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['190','191'])).

thf('193',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['189','194'])).

thf('196',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('197',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['179','197'])).

thf('199',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','198'])).

thf('200',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['36','37'])).

thf('201',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,(
    $false ),
    inference(simplify,[status(thm)],['201'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zAmrTmHP0B
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:48:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.18/1.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.18/1.45  % Solved by: fo/fo7.sh
% 1.18/1.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.18/1.45  % done 675 iterations in 0.992s
% 1.18/1.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.18/1.45  % SZS output start Refutation
% 1.18/1.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.18/1.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.18/1.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.18/1.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.18/1.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.18/1.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.18/1.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.18/1.45  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.18/1.45  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.18/1.45  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.18/1.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.18/1.45  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.18/1.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.18/1.45  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.18/1.45  thf(sk_B_type, type, sk_B: $i).
% 1.18/1.45  thf(sk_A_type, type, sk_A: $i).
% 1.18/1.45  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.18/1.45  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.18/1.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.18/1.45  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.18/1.45  thf(sk_C_type, type, sk_C: $i).
% 1.18/1.45  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.18/1.45  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.18/1.45  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.18/1.45  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.18/1.45  thf(t37_relat_1, axiom,
% 1.18/1.45    (![A:$i]:
% 1.18/1.45     ( ( v1_relat_1 @ A ) =>
% 1.18/1.45       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 1.18/1.45         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 1.18/1.45  thf('0', plain,
% 1.18/1.45      (![X4 : $i]:
% 1.18/1.45         (((k2_relat_1 @ X4) = (k1_relat_1 @ (k4_relat_1 @ X4)))
% 1.18/1.45          | ~ (v1_relat_1 @ X4))),
% 1.18/1.45      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.18/1.45  thf(d3_struct_0, axiom,
% 1.18/1.45    (![A:$i]:
% 1.18/1.45     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.18/1.45  thf('1', plain,
% 1.18/1.45      (![X23 : $i]:
% 1.18/1.45         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.18/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.45  thf('2', plain,
% 1.18/1.45      (![X23 : $i]:
% 1.18/1.45         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.18/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.45  thf('3', plain,
% 1.18/1.45      (![X23 : $i]:
% 1.18/1.45         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.18/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.45  thf(t62_tops_2, conjecture,
% 1.18/1.45    (![A:$i]:
% 1.18/1.45     ( ( l1_struct_0 @ A ) =>
% 1.18/1.45       ( ![B:$i]:
% 1.18/1.45         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.18/1.45           ( ![C:$i]:
% 1.18/1.45             ( ( ( v1_funct_1 @ C ) & 
% 1.18/1.45                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.18/1.45                 ( m1_subset_1 @
% 1.18/1.45                   C @ 
% 1.18/1.45                   ( k1_zfmisc_1 @
% 1.18/1.45                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.18/1.45               ( ( ( ( k2_relset_1 @
% 1.18/1.45                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.18/1.45                     ( k2_struct_0 @ B ) ) & 
% 1.18/1.45                   ( v2_funct_1 @ C ) ) =>
% 1.18/1.45                 ( ( ( k1_relset_1 @
% 1.18/1.45                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.18/1.45                       ( k2_tops_2 @
% 1.18/1.45                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.18/1.45                     ( k2_struct_0 @ B ) ) & 
% 1.18/1.45                   ( ( k2_relset_1 @
% 1.18/1.45                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.18/1.45                       ( k2_tops_2 @
% 1.18/1.45                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.18/1.45                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.18/1.45  thf(zf_stmt_0, negated_conjecture,
% 1.18/1.45    (~( ![A:$i]:
% 1.18/1.45        ( ( l1_struct_0 @ A ) =>
% 1.18/1.45          ( ![B:$i]:
% 1.18/1.45            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.18/1.45              ( ![C:$i]:
% 1.18/1.45                ( ( ( v1_funct_1 @ C ) & 
% 1.18/1.45                    ( v1_funct_2 @
% 1.18/1.45                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.18/1.45                    ( m1_subset_1 @
% 1.18/1.45                      C @ 
% 1.18/1.45                      ( k1_zfmisc_1 @
% 1.18/1.45                        ( k2_zfmisc_1 @
% 1.18/1.45                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.18/1.45                  ( ( ( ( k2_relset_1 @
% 1.18/1.45                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.18/1.45                        ( k2_struct_0 @ B ) ) & 
% 1.18/1.45                      ( v2_funct_1 @ C ) ) =>
% 1.18/1.45                    ( ( ( k1_relset_1 @
% 1.18/1.45                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.18/1.45                          ( k2_tops_2 @
% 1.18/1.45                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.18/1.45                        ( k2_struct_0 @ B ) ) & 
% 1.18/1.45                      ( ( k2_relset_1 @
% 1.18/1.45                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.18/1.45                          ( k2_tops_2 @
% 1.18/1.45                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.18/1.45                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.18/1.45    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.18/1.45  thf('4', plain,
% 1.18/1.45      ((m1_subset_1 @ sk_C @ 
% 1.18/1.45        (k1_zfmisc_1 @ 
% 1.18/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('5', plain,
% 1.18/1.45      (((m1_subset_1 @ sk_C @ 
% 1.18/1.45         (k1_zfmisc_1 @ 
% 1.18/1.45          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.18/1.45        | ~ (l1_struct_0 @ sk_A))),
% 1.18/1.45      inference('sup+', [status(thm)], ['3', '4'])).
% 1.18/1.45  thf('6', plain, ((l1_struct_0 @ sk_A)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('7', plain,
% 1.18/1.45      ((m1_subset_1 @ sk_C @ 
% 1.18/1.45        (k1_zfmisc_1 @ 
% 1.18/1.45         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.18/1.45      inference('demod', [status(thm)], ['5', '6'])).
% 1.18/1.45  thf('8', plain,
% 1.18/1.45      (((m1_subset_1 @ sk_C @ 
% 1.18/1.45         (k1_zfmisc_1 @ 
% 1.18/1.45          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.18/1.45        | ~ (l1_struct_0 @ sk_B))),
% 1.18/1.45      inference('sup+', [status(thm)], ['2', '7'])).
% 1.18/1.45  thf('9', plain, ((l1_struct_0 @ sk_B)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('10', plain,
% 1.18/1.45      ((m1_subset_1 @ sk_C @ 
% 1.18/1.45        (k1_zfmisc_1 @ 
% 1.18/1.45         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.18/1.45      inference('demod', [status(thm)], ['8', '9'])).
% 1.18/1.45  thf('11', plain,
% 1.18/1.45      ((m1_subset_1 @ sk_C @ 
% 1.18/1.45        (k1_zfmisc_1 @ 
% 1.18/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf(redefinition_k2_relset_1, axiom,
% 1.18/1.45    (![A:$i,B:$i,C:$i]:
% 1.18/1.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.45       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.18/1.45  thf('12', plain,
% 1.18/1.45      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.18/1.45         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 1.18/1.45          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 1.18/1.45      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.18/1.45  thf('13', plain,
% 1.18/1.45      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.18/1.45         = (k2_relat_1 @ sk_C))),
% 1.18/1.45      inference('sup-', [status(thm)], ['11', '12'])).
% 1.18/1.45  thf('14', plain,
% 1.18/1.45      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.18/1.45         = (k2_struct_0 @ sk_B))),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('15', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.18/1.45      inference('sup+', [status(thm)], ['13', '14'])).
% 1.18/1.45  thf('16', plain,
% 1.18/1.45      ((m1_subset_1 @ sk_C @ 
% 1.18/1.45        (k1_zfmisc_1 @ 
% 1.18/1.45         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.18/1.45      inference('demod', [status(thm)], ['10', '15'])).
% 1.18/1.45  thf(d4_tops_2, axiom,
% 1.18/1.45    (![A:$i,B:$i,C:$i]:
% 1.18/1.45     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.18/1.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.18/1.45       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.18/1.45         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.18/1.45  thf('17', plain,
% 1.18/1.45      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.18/1.45         (((k2_relset_1 @ X26 @ X25 @ X27) != (X25))
% 1.18/1.45          | ~ (v2_funct_1 @ X27)
% 1.18/1.45          | ((k2_tops_2 @ X26 @ X25 @ X27) = (k2_funct_1 @ X27))
% 1.18/1.45          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 1.18/1.45          | ~ (v1_funct_2 @ X27 @ X26 @ X25)
% 1.18/1.45          | ~ (v1_funct_1 @ X27))),
% 1.18/1.45      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.18/1.45  thf('18', plain,
% 1.18/1.45      ((~ (v1_funct_1 @ sk_C)
% 1.18/1.45        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.18/1.45        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.18/1.45            = (k2_funct_1 @ sk_C))
% 1.18/1.45        | ~ (v2_funct_1 @ sk_C)
% 1.18/1.45        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.18/1.45            != (k2_relat_1 @ sk_C)))),
% 1.18/1.45      inference('sup-', [status(thm)], ['16', '17'])).
% 1.18/1.45  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('20', plain,
% 1.18/1.45      (![X23 : $i]:
% 1.18/1.45         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.18/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.45  thf('21', plain,
% 1.18/1.45      (![X23 : $i]:
% 1.18/1.45         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.18/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.45  thf('22', plain,
% 1.18/1.45      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('23', plain,
% 1.18/1.45      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.18/1.45        | ~ (l1_struct_0 @ sk_A))),
% 1.18/1.45      inference('sup+', [status(thm)], ['21', '22'])).
% 1.18/1.45  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('25', plain,
% 1.18/1.45      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.18/1.45      inference('demod', [status(thm)], ['23', '24'])).
% 1.18/1.45  thf('26', plain,
% 1.18/1.45      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.18/1.45        | ~ (l1_struct_0 @ sk_B))),
% 1.18/1.45      inference('sup+', [status(thm)], ['20', '25'])).
% 1.18/1.45  thf('27', plain, ((l1_struct_0 @ sk_B)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('28', plain,
% 1.18/1.45      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.18/1.45      inference('demod', [status(thm)], ['26', '27'])).
% 1.18/1.45  thf('29', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.18/1.45      inference('sup+', [status(thm)], ['13', '14'])).
% 1.18/1.45  thf('30', plain,
% 1.18/1.45      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.18/1.45      inference('demod', [status(thm)], ['28', '29'])).
% 1.18/1.45  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf(d9_funct_1, axiom,
% 1.18/1.45    (![A:$i]:
% 1.18/1.45     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.18/1.45       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 1.18/1.45  thf('32', plain,
% 1.18/1.45      (![X5 : $i]:
% 1.18/1.45         (~ (v2_funct_1 @ X5)
% 1.18/1.45          | ((k2_funct_1 @ X5) = (k4_relat_1 @ X5))
% 1.18/1.45          | ~ (v1_funct_1 @ X5)
% 1.18/1.45          | ~ (v1_relat_1 @ X5))),
% 1.18/1.45      inference('cnf', [status(esa)], [d9_funct_1])).
% 1.18/1.45  thf('33', plain,
% 1.18/1.45      ((~ (v1_relat_1 @ sk_C)
% 1.18/1.45        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 1.18/1.45        | ~ (v2_funct_1 @ sk_C))),
% 1.18/1.45      inference('sup-', [status(thm)], ['31', '32'])).
% 1.18/1.45  thf('34', plain,
% 1.18/1.45      ((m1_subset_1 @ sk_C @ 
% 1.18/1.45        (k1_zfmisc_1 @ 
% 1.18/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf(cc2_relat_1, axiom,
% 1.18/1.45    (![A:$i]:
% 1.18/1.45     ( ( v1_relat_1 @ A ) =>
% 1.18/1.45       ( ![B:$i]:
% 1.18/1.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.18/1.45  thf('35', plain,
% 1.18/1.45      (![X0 : $i, X1 : $i]:
% 1.18/1.45         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.18/1.45          | (v1_relat_1 @ X0)
% 1.18/1.45          | ~ (v1_relat_1 @ X1))),
% 1.18/1.45      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.18/1.45  thf('36', plain,
% 1.18/1.45      ((~ (v1_relat_1 @ 
% 1.18/1.45           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 1.18/1.45        | (v1_relat_1 @ sk_C))),
% 1.18/1.45      inference('sup-', [status(thm)], ['34', '35'])).
% 1.18/1.45  thf(fc6_relat_1, axiom,
% 1.18/1.45    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.18/1.45  thf('37', plain,
% 1.18/1.45      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 1.18/1.45      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.18/1.45  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 1.18/1.45      inference('demod', [status(thm)], ['36', '37'])).
% 1.18/1.45  thf('39', plain, ((v2_funct_1 @ sk_C)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('40', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.18/1.45      inference('demod', [status(thm)], ['33', '38', '39'])).
% 1.18/1.45  thf('41', plain, ((v2_funct_1 @ sk_C)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('42', plain,
% 1.18/1.45      (![X23 : $i]:
% 1.18/1.45         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.18/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.45  thf('43', plain,
% 1.18/1.45      (![X23 : $i]:
% 1.18/1.45         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.18/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.45  thf('44', plain,
% 1.18/1.45      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.18/1.45         = (k2_struct_0 @ sk_B))),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('45', plain,
% 1.18/1.45      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.18/1.45          = (k2_struct_0 @ sk_B))
% 1.18/1.45        | ~ (l1_struct_0 @ sk_A))),
% 1.18/1.45      inference('sup+', [status(thm)], ['43', '44'])).
% 1.18/1.45  thf('46', plain, ((l1_struct_0 @ sk_A)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('47', plain,
% 1.18/1.45      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.18/1.45         = (k2_struct_0 @ sk_B))),
% 1.18/1.45      inference('demod', [status(thm)], ['45', '46'])).
% 1.18/1.45  thf('48', plain,
% 1.18/1.45      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.18/1.45          = (k2_struct_0 @ sk_B))
% 1.18/1.45        | ~ (l1_struct_0 @ sk_B))),
% 1.18/1.45      inference('sup+', [status(thm)], ['42', '47'])).
% 1.18/1.45  thf('49', plain, ((l1_struct_0 @ sk_B)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('50', plain,
% 1.18/1.45      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.18/1.45         = (k2_struct_0 @ sk_B))),
% 1.18/1.45      inference('demod', [status(thm)], ['48', '49'])).
% 1.18/1.45  thf('51', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.18/1.45      inference('sup+', [status(thm)], ['13', '14'])).
% 1.18/1.45  thf('52', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.18/1.45      inference('sup+', [status(thm)], ['13', '14'])).
% 1.18/1.45  thf('53', plain,
% 1.18/1.45      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.18/1.45         = (k2_relat_1 @ sk_C))),
% 1.18/1.45      inference('demod', [status(thm)], ['50', '51', '52'])).
% 1.18/1.45  thf('54', plain,
% 1.18/1.45      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.18/1.45          = (k4_relat_1 @ sk_C))
% 1.18/1.45        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.18/1.45      inference('demod', [status(thm)], ['18', '19', '30', '40', '41', '53'])).
% 1.18/1.45  thf('55', plain,
% 1.18/1.45      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.18/1.45         = (k4_relat_1 @ sk_C))),
% 1.18/1.45      inference('simplify', [status(thm)], ['54'])).
% 1.18/1.45  thf('56', plain,
% 1.18/1.45      (![X23 : $i]:
% 1.18/1.45         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.18/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.45  thf('57', plain,
% 1.18/1.45      (![X23 : $i]:
% 1.18/1.45         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.18/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.45  thf('58', plain,
% 1.18/1.45      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45          != (k2_struct_0 @ sk_B))
% 1.18/1.45        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45            != (k2_struct_0 @ sk_A)))),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('59', plain,
% 1.18/1.45      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45          != (k2_struct_0 @ sk_B)))
% 1.18/1.45         <= (~
% 1.18/1.45             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45                = (k2_struct_0 @ sk_B))))),
% 1.18/1.45      inference('split', [status(esa)], ['58'])).
% 1.18/1.45  thf('60', plain,
% 1.18/1.45      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45           != (k2_struct_0 @ sk_B))
% 1.18/1.45         | ~ (l1_struct_0 @ sk_A)))
% 1.18/1.45         <= (~
% 1.18/1.45             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45                = (k2_struct_0 @ sk_B))))),
% 1.18/1.45      inference('sup-', [status(thm)], ['57', '59'])).
% 1.18/1.45  thf('61', plain, ((l1_struct_0 @ sk_A)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('62', plain,
% 1.18/1.45      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45          != (k2_struct_0 @ sk_B)))
% 1.18/1.45         <= (~
% 1.18/1.45             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45                = (k2_struct_0 @ sk_B))))),
% 1.18/1.45      inference('demod', [status(thm)], ['60', '61'])).
% 1.18/1.45  thf('63', plain,
% 1.18/1.45      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45           != (k2_struct_0 @ sk_B))
% 1.18/1.45         | ~ (l1_struct_0 @ sk_B)))
% 1.18/1.45         <= (~
% 1.18/1.45             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45                = (k2_struct_0 @ sk_B))))),
% 1.18/1.45      inference('sup-', [status(thm)], ['56', '62'])).
% 1.18/1.45  thf('64', plain, ((l1_struct_0 @ sk_B)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('65', plain,
% 1.18/1.45      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45          != (k2_struct_0 @ sk_B)))
% 1.18/1.45         <= (~
% 1.18/1.45             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45                = (k2_struct_0 @ sk_B))))),
% 1.18/1.45      inference('demod', [status(thm)], ['63', '64'])).
% 1.18/1.45  thf('66', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.18/1.45      inference('sup+', [status(thm)], ['13', '14'])).
% 1.18/1.45  thf('67', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.18/1.45      inference('sup+', [status(thm)], ['13', '14'])).
% 1.18/1.45  thf('68', plain,
% 1.18/1.45      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.18/1.45          != (k2_relat_1 @ sk_C)))
% 1.18/1.45         <= (~
% 1.18/1.45             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45                = (k2_struct_0 @ sk_B))))),
% 1.18/1.45      inference('demod', [status(thm)], ['65', '66', '67'])).
% 1.18/1.45  thf('69', plain,
% 1.18/1.45      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45          (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.18/1.45         <= (~
% 1.18/1.45             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45                = (k2_struct_0 @ sk_B))))),
% 1.18/1.45      inference('sup-', [status(thm)], ['55', '68'])).
% 1.18/1.45  thf('70', plain,
% 1.18/1.45      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45           (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C))
% 1.18/1.45         | ~ (l1_struct_0 @ sk_B)))
% 1.18/1.45         <= (~
% 1.18/1.45             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45                = (k2_struct_0 @ sk_B))))),
% 1.18/1.45      inference('sup-', [status(thm)], ['1', '69'])).
% 1.18/1.45  thf('71', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.18/1.45      inference('sup+', [status(thm)], ['13', '14'])).
% 1.18/1.45  thf('72', plain, ((l1_struct_0 @ sk_B)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('73', plain,
% 1.18/1.45      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45          (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.18/1.45         <= (~
% 1.18/1.45             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45                = (k2_struct_0 @ sk_B))))),
% 1.18/1.45      inference('demod', [status(thm)], ['70', '71', '72'])).
% 1.18/1.45  thf('74', plain,
% 1.18/1.45      (![X23 : $i]:
% 1.18/1.45         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.18/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.45  thf('75', plain,
% 1.18/1.45      (![X23 : $i]:
% 1.18/1.45         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.18/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.45  thf(d1_funct_2, axiom,
% 1.18/1.45    (![A:$i,B:$i,C:$i]:
% 1.18/1.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.45       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.18/1.45           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.18/1.45             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.18/1.45         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.18/1.45           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.18/1.45             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.18/1.45  thf(zf_stmt_1, axiom,
% 1.18/1.45    (![B:$i,A:$i]:
% 1.18/1.45     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.18/1.45       ( zip_tseitin_0 @ B @ A ) ))).
% 1.18/1.45  thf('76', plain,
% 1.18/1.45      (![X12 : $i, X13 : $i]:
% 1.18/1.45         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.18/1.45  thf('77', plain,
% 1.18/1.45      ((m1_subset_1 @ sk_C @ 
% 1.18/1.45        (k1_zfmisc_1 @ 
% 1.18/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.18/1.45  thf(zf_stmt_3, axiom,
% 1.18/1.45    (![C:$i,B:$i,A:$i]:
% 1.18/1.45     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.18/1.45       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.18/1.45  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.18/1.45  thf(zf_stmt_5, axiom,
% 1.18/1.45    (![A:$i,B:$i,C:$i]:
% 1.18/1.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.45       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.18/1.45         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.18/1.45           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.18/1.45             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.18/1.45  thf('78', plain,
% 1.18/1.45      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.18/1.45         (~ (zip_tseitin_0 @ X17 @ X18)
% 1.18/1.45          | (zip_tseitin_1 @ X19 @ X17 @ X18)
% 1.18/1.45          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X17))))),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.18/1.45  thf('79', plain,
% 1.18/1.45      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.18/1.45        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.18/1.45      inference('sup-', [status(thm)], ['77', '78'])).
% 1.18/1.45  thf('80', plain,
% 1.18/1.45      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.18/1.45        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.18/1.45      inference('sup-', [status(thm)], ['76', '79'])).
% 1.18/1.45  thf('81', plain,
% 1.18/1.45      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('82', plain,
% 1.18/1.45      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.18/1.45         (~ (v1_funct_2 @ X16 @ X14 @ X15)
% 1.18/1.45          | ((X14) = (k1_relset_1 @ X14 @ X15 @ X16))
% 1.18/1.45          | ~ (zip_tseitin_1 @ X16 @ X15 @ X14))),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.18/1.45  thf('83', plain,
% 1.18/1.45      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.18/1.45        | ((u1_struct_0 @ sk_A)
% 1.18/1.45            = (k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)))),
% 1.18/1.45      inference('sup-', [status(thm)], ['81', '82'])).
% 1.18/1.45  thf('84', plain,
% 1.18/1.45      ((m1_subset_1 @ sk_C @ 
% 1.18/1.45        (k1_zfmisc_1 @ 
% 1.18/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf(redefinition_k1_relset_1, axiom,
% 1.18/1.45    (![A:$i,B:$i,C:$i]:
% 1.18/1.45     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.18/1.45       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.18/1.45  thf('85', plain,
% 1.18/1.45      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.18/1.45         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 1.18/1.45          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 1.18/1.45      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.18/1.45  thf('86', plain,
% 1.18/1.45      (((k1_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.18/1.45         = (k1_relat_1 @ sk_C))),
% 1.18/1.45      inference('sup-', [status(thm)], ['84', '85'])).
% 1.18/1.45  thf('87', plain,
% 1.18/1.45      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.18/1.45        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.18/1.45      inference('demod', [status(thm)], ['83', '86'])).
% 1.18/1.45  thf('88', plain,
% 1.18/1.45      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 1.18/1.45        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.18/1.45      inference('sup-', [status(thm)], ['80', '87'])).
% 1.18/1.45  thf('89', plain,
% 1.18/1.45      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 1.18/1.45        | ~ (l1_struct_0 @ sk_B)
% 1.18/1.45        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.18/1.45      inference('sup+', [status(thm)], ['75', '88'])).
% 1.18/1.45  thf('90', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.18/1.45      inference('sup+', [status(thm)], ['13', '14'])).
% 1.18/1.45  thf('91', plain, ((l1_struct_0 @ sk_B)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('92', plain,
% 1.18/1.45      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 1.18/1.45        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.18/1.45      inference('demod', [status(thm)], ['89', '90', '91'])).
% 1.18/1.45  thf('93', plain,
% 1.18/1.45      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 1.18/1.45        | ~ (l1_struct_0 @ sk_A)
% 1.18/1.45        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.18/1.45      inference('sup+', [status(thm)], ['74', '92'])).
% 1.18/1.45  thf('94', plain, ((l1_struct_0 @ sk_A)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('95', plain,
% 1.18/1.45      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))
% 1.18/1.45        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.18/1.45      inference('demod', [status(thm)], ['93', '94'])).
% 1.18/1.45  thf('96', plain,
% 1.18/1.45      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.18/1.45         = (k4_relat_1 @ sk_C))),
% 1.18/1.45      inference('simplify', [status(thm)], ['54'])).
% 1.18/1.45  thf('97', plain,
% 1.18/1.45      (![X23 : $i]:
% 1.18/1.45         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.18/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.45  thf('98', plain,
% 1.18/1.45      (![X23 : $i]:
% 1.18/1.45         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.18/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.45  thf('99', plain,
% 1.18/1.45      (![X23 : $i]:
% 1.18/1.45         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.18/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.45  thf('100', plain,
% 1.18/1.45      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45          != (k2_struct_0 @ sk_A)))
% 1.18/1.45         <= (~
% 1.18/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45                = (k2_struct_0 @ sk_A))))),
% 1.18/1.45      inference('split', [status(esa)], ['58'])).
% 1.18/1.45  thf('101', plain,
% 1.18/1.45      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45           != (k2_struct_0 @ sk_A))
% 1.18/1.45         | ~ (l1_struct_0 @ sk_B)))
% 1.18/1.45         <= (~
% 1.18/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45                = (k2_struct_0 @ sk_A))))),
% 1.18/1.45      inference('sup-', [status(thm)], ['99', '100'])).
% 1.18/1.45  thf('102', plain, ((l1_struct_0 @ sk_B)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('103', plain,
% 1.18/1.45      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45          != (k2_struct_0 @ sk_A)))
% 1.18/1.45         <= (~
% 1.18/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45                = (k2_struct_0 @ sk_A))))),
% 1.18/1.45      inference('demod', [status(thm)], ['101', '102'])).
% 1.18/1.45  thf('104', plain,
% 1.18/1.45      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45           != (k2_struct_0 @ sk_A))
% 1.18/1.45         | ~ (l1_struct_0 @ sk_A)))
% 1.18/1.45         <= (~
% 1.18/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45                = (k2_struct_0 @ sk_A))))),
% 1.18/1.45      inference('sup-', [status(thm)], ['98', '103'])).
% 1.18/1.45  thf('105', plain, ((l1_struct_0 @ sk_A)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('106', plain,
% 1.18/1.45      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45          != (k2_struct_0 @ sk_A)))
% 1.18/1.45         <= (~
% 1.18/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45                = (k2_struct_0 @ sk_A))))),
% 1.18/1.45      inference('demod', [status(thm)], ['104', '105'])).
% 1.18/1.45  thf('107', plain,
% 1.18/1.45      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45           != (k2_struct_0 @ sk_A))
% 1.18/1.45         | ~ (l1_struct_0 @ sk_B)))
% 1.18/1.45         <= (~
% 1.18/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45                = (k2_struct_0 @ sk_A))))),
% 1.18/1.45      inference('sup-', [status(thm)], ['97', '106'])).
% 1.18/1.45  thf('108', plain, ((l1_struct_0 @ sk_B)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('109', plain,
% 1.18/1.45      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45          != (k2_struct_0 @ sk_A)))
% 1.18/1.45         <= (~
% 1.18/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45                = (k2_struct_0 @ sk_A))))),
% 1.18/1.45      inference('demod', [status(thm)], ['107', '108'])).
% 1.18/1.45  thf('110', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.18/1.45      inference('sup+', [status(thm)], ['13', '14'])).
% 1.18/1.45  thf('111', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.18/1.45      inference('sup+', [status(thm)], ['13', '14'])).
% 1.18/1.45  thf('112', plain,
% 1.18/1.45      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.18/1.45          != (k2_struct_0 @ sk_A)))
% 1.18/1.45         <= (~
% 1.18/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45                = (k2_struct_0 @ sk_A))))),
% 1.18/1.45      inference('demod', [status(thm)], ['109', '110', '111'])).
% 1.18/1.45  thf('113', plain,
% 1.18/1.45      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45          (k4_relat_1 @ sk_C)) != (k2_struct_0 @ sk_A)))
% 1.18/1.45         <= (~
% 1.18/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45                = (k2_struct_0 @ sk_A))))),
% 1.18/1.45      inference('sup-', [status(thm)], ['96', '112'])).
% 1.18/1.45  thf('114', plain,
% 1.18/1.45      (![X23 : $i]:
% 1.18/1.45         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.18/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.45  thf('115', plain,
% 1.18/1.45      ((m1_subset_1 @ sk_C @ 
% 1.18/1.45        (k1_zfmisc_1 @ 
% 1.18/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('116', plain,
% 1.18/1.45      (((m1_subset_1 @ sk_C @ 
% 1.18/1.45         (k1_zfmisc_1 @ 
% 1.18/1.45          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.18/1.45        | ~ (l1_struct_0 @ sk_B))),
% 1.18/1.45      inference('sup+', [status(thm)], ['114', '115'])).
% 1.18/1.45  thf('117', plain, ((l1_struct_0 @ sk_B)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('118', plain,
% 1.18/1.45      ((m1_subset_1 @ sk_C @ 
% 1.18/1.45        (k1_zfmisc_1 @ 
% 1.18/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.18/1.45      inference('demod', [status(thm)], ['116', '117'])).
% 1.18/1.45  thf('119', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.18/1.45      inference('sup+', [status(thm)], ['13', '14'])).
% 1.18/1.45  thf('120', plain,
% 1.18/1.45      ((m1_subset_1 @ sk_C @ 
% 1.18/1.45        (k1_zfmisc_1 @ 
% 1.18/1.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.18/1.45      inference('demod', [status(thm)], ['118', '119'])).
% 1.18/1.45  thf(t31_funct_2, axiom,
% 1.18/1.45    (![A:$i,B:$i,C:$i]:
% 1.18/1.45     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.18/1.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.18/1.45       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.18/1.45         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.18/1.45           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.18/1.45           ( m1_subset_1 @
% 1.18/1.45             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.18/1.45  thf('121', plain,
% 1.18/1.45      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.18/1.45         (~ (v2_funct_1 @ X20)
% 1.18/1.45          | ((k2_relset_1 @ X22 @ X21 @ X20) != (X21))
% 1.18/1.45          | (m1_subset_1 @ (k2_funct_1 @ X20) @ 
% 1.18/1.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.18/1.45          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 1.18/1.45          | ~ (v1_funct_2 @ X20 @ X22 @ X21)
% 1.18/1.45          | ~ (v1_funct_1 @ X20))),
% 1.18/1.45      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.18/1.45  thf('122', plain,
% 1.18/1.45      ((~ (v1_funct_1 @ sk_C)
% 1.18/1.45        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.18/1.45        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.18/1.45           (k1_zfmisc_1 @ 
% 1.18/1.45            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 1.18/1.45        | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.18/1.45            != (k2_relat_1 @ sk_C))
% 1.18/1.45        | ~ (v2_funct_1 @ sk_C))),
% 1.18/1.45      inference('sup-', [status(thm)], ['120', '121'])).
% 1.18/1.45  thf('123', plain, ((v1_funct_1 @ sk_C)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('124', plain,
% 1.18/1.45      (![X23 : $i]:
% 1.18/1.45         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.18/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.45  thf('125', plain,
% 1.18/1.45      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('126', plain,
% 1.18/1.45      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.18/1.45        | ~ (l1_struct_0 @ sk_B))),
% 1.18/1.45      inference('sup+', [status(thm)], ['124', '125'])).
% 1.18/1.45  thf('127', plain, ((l1_struct_0 @ sk_B)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('128', plain,
% 1.18/1.45      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.18/1.45      inference('demod', [status(thm)], ['126', '127'])).
% 1.18/1.45  thf('129', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.18/1.45      inference('sup+', [status(thm)], ['13', '14'])).
% 1.18/1.45  thf('130', plain,
% 1.18/1.45      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.18/1.45      inference('demod', [status(thm)], ['128', '129'])).
% 1.18/1.45  thf('131', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.18/1.45      inference('demod', [status(thm)], ['33', '38', '39'])).
% 1.18/1.45  thf('132', plain,
% 1.18/1.45      (![X23 : $i]:
% 1.18/1.45         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.18/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.45  thf('133', plain,
% 1.18/1.45      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.18/1.45         = (k2_struct_0 @ sk_B))),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('134', plain,
% 1.18/1.45      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.18/1.45          = (k2_struct_0 @ sk_B))
% 1.18/1.45        | ~ (l1_struct_0 @ sk_B))),
% 1.18/1.45      inference('sup+', [status(thm)], ['132', '133'])).
% 1.18/1.45  thf('135', plain, ((l1_struct_0 @ sk_B)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('136', plain,
% 1.18/1.45      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.18/1.45         = (k2_struct_0 @ sk_B))),
% 1.18/1.45      inference('demod', [status(thm)], ['134', '135'])).
% 1.18/1.45  thf('137', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.18/1.45      inference('sup+', [status(thm)], ['13', '14'])).
% 1.18/1.45  thf('138', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.18/1.45      inference('sup+', [status(thm)], ['13', '14'])).
% 1.18/1.45  thf('139', plain,
% 1.18/1.45      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.18/1.45         = (k2_relat_1 @ sk_C))),
% 1.18/1.45      inference('demod', [status(thm)], ['136', '137', '138'])).
% 1.18/1.45  thf('140', plain, ((v2_funct_1 @ sk_C)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('141', plain,
% 1.18/1.45      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.18/1.45         (k1_zfmisc_1 @ 
% 1.18/1.45          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))
% 1.18/1.45        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.18/1.45      inference('demod', [status(thm)],
% 1.18/1.45                ['122', '123', '130', '131', '139', '140'])).
% 1.18/1.45  thf('142', plain,
% 1.18/1.45      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.18/1.45        (k1_zfmisc_1 @ 
% 1.18/1.45         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A))))),
% 1.18/1.45      inference('simplify', [status(thm)], ['141'])).
% 1.18/1.45  thf('143', plain,
% 1.18/1.45      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.18/1.45         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 1.18/1.45          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 1.18/1.45      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.18/1.45  thf('144', plain,
% 1.18/1.45      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45         (k4_relat_1 @ sk_C)) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.18/1.45      inference('sup-', [status(thm)], ['142', '143'])).
% 1.18/1.45  thf('145', plain, ((v1_relat_1 @ sk_C)),
% 1.18/1.45      inference('demod', [status(thm)], ['36', '37'])).
% 1.18/1.45  thf('146', plain,
% 1.18/1.45      (![X4 : $i]:
% 1.18/1.45         (((k1_relat_1 @ X4) = (k2_relat_1 @ (k4_relat_1 @ X4)))
% 1.18/1.45          | ~ (v1_relat_1 @ X4))),
% 1.18/1.45      inference('cnf', [status(esa)], [t37_relat_1])).
% 1.18/1.45  thf('147', plain,
% 1.18/1.45      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.18/1.45      inference('sup-', [status(thm)], ['145', '146'])).
% 1.18/1.45  thf('148', plain,
% 1.18/1.45      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45         (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 1.18/1.45      inference('demod', [status(thm)], ['144', '147'])).
% 1.18/1.45  thf('149', plain,
% 1.18/1.45      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A)))
% 1.18/1.45         <= (~
% 1.18/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45                = (k2_struct_0 @ sk_A))))),
% 1.18/1.45      inference('demod', [status(thm)], ['113', '148'])).
% 1.18/1.45  thf('150', plain,
% 1.18/1.45      (((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 1.18/1.45         | ((k2_relat_1 @ sk_C) = (k1_xboole_0))))
% 1.18/1.45         <= (~
% 1.18/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45                = (k2_struct_0 @ sk_A))))),
% 1.18/1.45      inference('sup-', [status(thm)], ['95', '149'])).
% 1.18/1.45  thf('151', plain,
% 1.18/1.45      ((((k2_relat_1 @ sk_C) = (k1_xboole_0)))
% 1.18/1.45         <= (~
% 1.18/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45                = (k2_struct_0 @ sk_A))))),
% 1.18/1.45      inference('simplify', [status(thm)], ['150'])).
% 1.18/1.45  thf('152', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.18/1.45      inference('sup+', [status(thm)], ['13', '14'])).
% 1.18/1.45  thf(fc5_struct_0, axiom,
% 1.18/1.45    (![A:$i]:
% 1.18/1.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.18/1.45       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 1.18/1.45  thf('153', plain,
% 1.18/1.45      (![X24 : $i]:
% 1.18/1.45         (~ (v1_xboole_0 @ (k2_struct_0 @ X24))
% 1.18/1.45          | ~ (l1_struct_0 @ X24)
% 1.18/1.45          | (v2_struct_0 @ X24))),
% 1.18/1.45      inference('cnf', [status(esa)], [fc5_struct_0])).
% 1.18/1.45  thf('154', plain,
% 1.18/1.45      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.18/1.45        | (v2_struct_0 @ sk_B)
% 1.18/1.45        | ~ (l1_struct_0 @ sk_B))),
% 1.18/1.45      inference('sup-', [status(thm)], ['152', '153'])).
% 1.18/1.45  thf('155', plain, ((l1_struct_0 @ sk_B)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('156', plain,
% 1.18/1.45      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.18/1.45      inference('demod', [status(thm)], ['154', '155'])).
% 1.18/1.45  thf('157', plain, (~ (v2_struct_0 @ sk_B)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('158', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.18/1.45      inference('clc', [status(thm)], ['156', '157'])).
% 1.18/1.45  thf('159', plain,
% 1.18/1.45      ((~ (v1_xboole_0 @ k1_xboole_0))
% 1.18/1.45         <= (~
% 1.18/1.45             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45                = (k2_struct_0 @ sk_A))))),
% 1.18/1.45      inference('sup-', [status(thm)], ['151', '158'])).
% 1.18/1.45  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.18/1.45  thf('160', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.18/1.45      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.18/1.45  thf('161', plain,
% 1.18/1.45      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45          = (k2_struct_0 @ sk_A)))),
% 1.18/1.45      inference('demod', [status(thm)], ['159', '160'])).
% 1.18/1.45  thf('162', plain,
% 1.18/1.45      (~
% 1.18/1.45       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45          = (k2_struct_0 @ sk_B))) | 
% 1.18/1.45       ~
% 1.18/1.45       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45          = (k2_struct_0 @ sk_A)))),
% 1.18/1.45      inference('split', [status(esa)], ['58'])).
% 1.18/1.45  thf('163', plain,
% 1.18/1.45      (~
% 1.18/1.45       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.18/1.45          = (k2_struct_0 @ sk_B)))),
% 1.18/1.45      inference('sat_resolution*', [status(thm)], ['161', '162'])).
% 1.18/1.45  thf('164', plain,
% 1.18/1.45      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.18/1.45         (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 1.18/1.45      inference('simpl_trail', [status(thm)], ['73', '163'])).
% 1.18/1.45  thf('165', plain,
% 1.18/1.45      (![X23 : $i]:
% 1.18/1.45         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.18/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.45  thf('166', plain,
% 1.18/1.45      (![X12 : $i, X13 : $i]:
% 1.18/1.45         ((zip_tseitin_0 @ X12 @ X13) | ((X12) = (k1_xboole_0)))),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.18/1.45  thf('167', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.18/1.45      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.18/1.45  thf('168', plain,
% 1.18/1.45      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.18/1.45      inference('sup+', [status(thm)], ['166', '167'])).
% 1.18/1.45  thf('169', plain,
% 1.18/1.45      (((zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.18/1.45        | ~ (zip_tseitin_0 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.18/1.45      inference('sup-', [status(thm)], ['77', '78'])).
% 1.18/1.45  thf('170', plain,
% 1.18/1.45      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.18/1.45        | (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A)))),
% 1.18/1.45      inference('sup-', [status(thm)], ['168', '169'])).
% 1.18/1.45  thf('171', plain,
% 1.18/1.45      ((~ (zip_tseitin_1 @ sk_C @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 1.18/1.45        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.18/1.45      inference('demod', [status(thm)], ['83', '86'])).
% 1.18/1.45  thf('172', plain,
% 1.18/1.45      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 1.18/1.45        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.18/1.45      inference('sup-', [status(thm)], ['170', '171'])).
% 1.18/1.45  thf('173', plain,
% 1.18/1.45      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 1.18/1.45        | ~ (l1_struct_0 @ sk_B)
% 1.18/1.45        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.18/1.45      inference('sup+', [status(thm)], ['165', '172'])).
% 1.18/1.45  thf('174', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.18/1.45      inference('sup+', [status(thm)], ['13', '14'])).
% 1.18/1.45  thf('175', plain, ((l1_struct_0 @ sk_B)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('176', plain,
% 1.18/1.45      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.18/1.45        | ((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)))),
% 1.18/1.45      inference('demod', [status(thm)], ['173', '174', '175'])).
% 1.18/1.45  thf('177', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.18/1.45      inference('clc', [status(thm)], ['156', '157'])).
% 1.18/1.45  thf('178', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.18/1.45      inference('clc', [status(thm)], ['176', '177'])).
% 1.18/1.45  thf('179', plain,
% 1.18/1.45      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.18/1.45         (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 1.18/1.45      inference('demod', [status(thm)], ['164', '178'])).
% 1.18/1.45  thf('180', plain,
% 1.18/1.45      ((m1_subset_1 @ sk_C @ 
% 1.18/1.45        (k1_zfmisc_1 @ 
% 1.18/1.45         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.18/1.45      inference('demod', [status(thm)], ['10', '15'])).
% 1.18/1.45  thf('181', plain,
% 1.18/1.45      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.18/1.45         (~ (v2_funct_1 @ X20)
% 1.18/1.45          | ((k2_relset_1 @ X22 @ X21 @ X20) != (X21))
% 1.18/1.45          | (m1_subset_1 @ (k2_funct_1 @ X20) @ 
% 1.18/1.45             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 1.18/1.45          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21)))
% 1.18/1.45          | ~ (v1_funct_2 @ X20 @ X22 @ X21)
% 1.18/1.45          | ~ (v1_funct_1 @ X20))),
% 1.18/1.45      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.18/1.45  thf('182', plain,
% 1.18/1.45      ((~ (v1_funct_1 @ sk_C)
% 1.18/1.45        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.18/1.45        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.18/1.45           (k1_zfmisc_1 @ 
% 1.18/1.45            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 1.18/1.45        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.18/1.45            != (k2_relat_1 @ sk_C))
% 1.18/1.45        | ~ (v2_funct_1 @ sk_C))),
% 1.18/1.45      inference('sup-', [status(thm)], ['180', '181'])).
% 1.18/1.45  thf('183', plain, ((v1_funct_1 @ sk_C)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('184', plain,
% 1.18/1.45      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.18/1.45      inference('demod', [status(thm)], ['28', '29'])).
% 1.18/1.45  thf('185', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 1.18/1.45      inference('demod', [status(thm)], ['33', '38', '39'])).
% 1.18/1.45  thf('186', plain,
% 1.18/1.45      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.18/1.45         = (k2_relat_1 @ sk_C))),
% 1.18/1.45      inference('demod', [status(thm)], ['50', '51', '52'])).
% 1.18/1.45  thf('187', plain, ((v2_funct_1 @ sk_C)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('188', plain,
% 1.18/1.45      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.18/1.45         (k1_zfmisc_1 @ 
% 1.18/1.45          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 1.18/1.45        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.18/1.45      inference('demod', [status(thm)],
% 1.18/1.45                ['182', '183', '184', '185', '186', '187'])).
% 1.18/1.45  thf('189', plain,
% 1.18/1.45      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.18/1.45        (k1_zfmisc_1 @ 
% 1.18/1.45         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 1.18/1.45      inference('simplify', [status(thm)], ['188'])).
% 1.18/1.45  thf('190', plain,
% 1.18/1.45      (![X23 : $i]:
% 1.18/1.45         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 1.18/1.45      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.18/1.45  thf('191', plain, (((u1_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.18/1.45      inference('clc', [status(thm)], ['176', '177'])).
% 1.18/1.45  thf('192', plain,
% 1.18/1.45      ((((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C)) | ~ (l1_struct_0 @ sk_A))),
% 1.18/1.45      inference('sup+', [status(thm)], ['190', '191'])).
% 1.18/1.45  thf('193', plain, ((l1_struct_0 @ sk_A)),
% 1.18/1.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.18/1.45  thf('194', plain, (((k2_struct_0 @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.18/1.45      inference('demod', [status(thm)], ['192', '193'])).
% 1.18/1.45  thf('195', plain,
% 1.18/1.45      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 1.18/1.45        (k1_zfmisc_1 @ 
% 1.18/1.45         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.18/1.45      inference('demod', [status(thm)], ['189', '194'])).
% 1.18/1.45  thf('196', plain,
% 1.18/1.45      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.18/1.45         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 1.18/1.45          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 1.18/1.45      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.18/1.45  thf('197', plain,
% 1.18/1.45      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.18/1.45         (k4_relat_1 @ sk_C)) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 1.18/1.45      inference('sup-', [status(thm)], ['195', '196'])).
% 1.18/1.45  thf('198', plain,
% 1.18/1.45      (((k1_relat_1 @ (k4_relat_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 1.18/1.45      inference('demod', [status(thm)], ['179', '197'])).
% 1.18/1.45  thf('199', plain,
% 1.18/1.45      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)) | ~ (v1_relat_1 @ sk_C))),
% 1.18/1.45      inference('sup-', [status(thm)], ['0', '198'])).
% 1.18/1.45  thf('200', plain, ((v1_relat_1 @ sk_C)),
% 1.18/1.45      inference('demod', [status(thm)], ['36', '37'])).
% 1.18/1.45  thf('201', plain, (((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))),
% 1.18/1.45      inference('demod', [status(thm)], ['199', '200'])).
% 1.18/1.45  thf('202', plain, ($false), inference('simplify', [status(thm)], ['201'])).
% 1.18/1.45  
% 1.18/1.45  % SZS output end Refutation
% 1.18/1.45  
% 1.29/1.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
