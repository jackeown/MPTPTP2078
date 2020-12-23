%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:18 EST 2020

% Result     : Theorem 6.73s
% Output     : CNFRefutation 7.12s
% Verified   : 
% Statistics : Number of formulae       :  215 ( 782 expanded)
%              Number of leaves         :   50 ( 280 expanded)
%              Depth                    :   12
%              Number of atoms          :  404 (2166 expanded)
%              Number of equality atoms :   81 ( 224 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_182,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_140,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_90,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_138,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_124,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_128,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_162,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_75,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_86,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_82,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_39,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_70,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_154,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_84,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_82,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_80,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_78,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_76,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_64,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_40,plain,(
    ! [A_24] : v2_funct_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_85,plain,(
    ! [A_24] : v2_funct_1(k6_partfun1(A_24)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_40])).

tff(c_1809,plain,(
    ! [A_260,E_259,C_261,D_262,B_264,F_263] :
      ( k1_partfun1(A_260,B_264,C_261,D_262,E_259,F_263) = k5_relat_1(E_259,F_263)
      | ~ m1_subset_1(F_263,k1_zfmisc_1(k2_zfmisc_1(C_261,D_262)))
      | ~ v1_funct_1(F_263)
      | ~ m1_subset_1(E_259,k1_zfmisc_1(k2_zfmisc_1(A_260,B_264)))
      | ~ v1_funct_1(E_259) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1815,plain,(
    ! [A_260,B_264,E_259] :
      ( k1_partfun1(A_260,B_264,'#skF_2','#skF_1',E_259,'#skF_4') = k5_relat_1(E_259,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_259,k1_zfmisc_1(k2_zfmisc_1(A_260,B_264)))
      | ~ v1_funct_1(E_259) ) ),
    inference(resolution,[status(thm)],[c_74,c_1809])).

tff(c_2009,plain,(
    ! [A_286,B_287,E_288] :
      ( k1_partfun1(A_286,B_287,'#skF_2','#skF_1',E_288,'#skF_4') = k5_relat_1(E_288,'#skF_4')
      | ~ m1_subset_1(E_288,k1_zfmisc_1(k2_zfmisc_1(A_286,B_287)))
      | ~ v1_funct_1(E_288) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1815])).

tff(c_2018,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_2009])).

tff(c_2032,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2018])).

tff(c_54,plain,(
    ! [D_37,A_34,F_39,B_35,C_36,E_38] :
      ( m1_subset_1(k1_partfun1(A_34,B_35,C_36,D_37,E_38,F_39),k1_zfmisc_1(k2_zfmisc_1(A_34,D_37)))
      | ~ m1_subset_1(F_39,k1_zfmisc_1(k2_zfmisc_1(C_36,D_37)))
      | ~ v1_funct_1(F_39)
      | ~ m1_subset_1(E_38,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ v1_funct_1(E_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_2041,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2032,c_54])).

tff(c_2045,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_74,c_2041])).

tff(c_60,plain,(
    ! [A_40] : m1_subset_1(k6_partfun1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_72,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1636,plain,(
    ! [D_240,C_241,A_242,B_243] :
      ( D_240 = C_241
      | ~ r2_relset_1(A_242,B_243,C_241,D_240)
      | ~ m1_subset_1(D_240,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243)))
      | ~ m1_subset_1(C_241,k1_zfmisc_1(k2_zfmisc_1(A_242,B_243))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1646,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_72,c_1636])).

tff(c_1665,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1646])).

tff(c_1668,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1665])).

tff(c_2437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2045,c_2032,c_1668])).

tff(c_2438,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1665])).

tff(c_3028,plain,(
    ! [B_361,A_362,D_360,C_363,E_359] :
      ( k1_xboole_0 = C_363
      | v2_funct_1(D_360)
      | ~ v2_funct_1(k1_partfun1(A_362,B_361,B_361,C_363,D_360,E_359))
      | ~ m1_subset_1(E_359,k1_zfmisc_1(k2_zfmisc_1(B_361,C_363)))
      | ~ v1_funct_2(E_359,B_361,C_363)
      | ~ v1_funct_1(E_359)
      | ~ m1_subset_1(D_360,k1_zfmisc_1(k2_zfmisc_1(A_362,B_361)))
      | ~ v1_funct_2(D_360,A_362,B_361)
      | ~ v1_funct_1(D_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_3032,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2438,c_3028])).

tff(c_3036,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_85,c_3032])).

tff(c_3037,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_154,c_3036])).

tff(c_30,plain,(
    ! [A_18,B_19] : v1_relat_1(k2_zfmisc_1(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_187,plain,(
    ! [B_73,A_74] :
      ( v1_relat_1(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_199,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_74,c_187])).

tff(c_211,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_199])).

tff(c_375,plain,(
    ! [C_93,B_94,A_95] :
      ( v5_relat_1(C_93,B_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_95,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_393,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_375])).

tff(c_584,plain,(
    ! [B_117,A_118] :
      ( k2_relat_1(B_117) = A_118
      | ~ v2_funct_2(B_117,A_118)
      | ~ v5_relat_1(B_117,A_118)
      | ~ v1_relat_1(B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_599,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_393,c_584])).

tff(c_616,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_599])).

tff(c_633,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_616])).

tff(c_196,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_80,c_187])).

tff(c_208,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_196])).

tff(c_36,plain,(
    ! [A_23] : k2_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_87,plain,(
    ! [A_23] : k2_relat_1(k6_partfun1(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_36])).

tff(c_1012,plain,(
    ! [B_172,F_170,D_169,C_173,E_171,A_168] :
      ( m1_subset_1(k1_partfun1(A_168,B_172,C_173,D_169,E_171,F_170),k1_zfmisc_1(k2_zfmisc_1(A_168,D_169)))
      | ~ m1_subset_1(F_170,k1_zfmisc_1(k2_zfmisc_1(C_173,D_169)))
      | ~ v1_funct_1(F_170)
      | ~ m1_subset_1(E_171,k1_zfmisc_1(k2_zfmisc_1(A_168,B_172)))
      | ~ v1_funct_1(E_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_715,plain,(
    ! [D_123,C_124,A_125,B_126] :
      ( D_123 = C_124
      | ~ r2_relset_1(A_125,B_126,C_124,D_123)
      | ~ m1_subset_1(D_123,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126)))
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_725,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_72,c_715])).

tff(c_744,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_725])).

tff(c_777,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_744])).

tff(c_1018,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1012,c_777])).

tff(c_1050,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_74,c_1018])).

tff(c_1051,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_744])).

tff(c_1233,plain,(
    ! [B_205,E_200,D_203,C_202,F_204,A_201] :
      ( k1_partfun1(A_201,B_205,C_202,D_203,E_200,F_204) = k5_relat_1(E_200,F_204)
      | ~ m1_subset_1(F_204,k1_zfmisc_1(k2_zfmisc_1(C_202,D_203)))
      | ~ v1_funct_1(F_204)
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_201,B_205)))
      | ~ v1_funct_1(E_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1239,plain,(
    ! [A_201,B_205,E_200] :
      ( k1_partfun1(A_201,B_205,'#skF_2','#skF_1',E_200,'#skF_4') = k5_relat_1(E_200,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_200,k1_zfmisc_1(k2_zfmisc_1(A_201,B_205)))
      | ~ v1_funct_1(E_200) ) ),
    inference(resolution,[status(thm)],[c_74,c_1233])).

tff(c_1503,plain,(
    ! [A_237,B_238,E_239] :
      ( k1_partfun1(A_237,B_238,'#skF_2','#skF_1',E_239,'#skF_4') = k5_relat_1(E_239,'#skF_4')
      | ~ m1_subset_1(E_239,k1_zfmisc_1(k2_zfmisc_1(A_237,B_238)))
      | ~ v1_funct_1(E_239) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1239])).

tff(c_1515,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_1503])).

tff(c_1532,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_1051,c_1515])).

tff(c_32,plain,(
    ! [A_20,B_22] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_20,B_22)),k2_relat_1(B_22))
      | ~ v1_relat_1(B_22)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1542,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1532,c_32])).

tff(c_1548,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_211,c_87,c_1542])).

tff(c_344,plain,(
    ! [B_88,A_89] :
      ( r1_tarski(k2_relat_1(B_88),A_89)
      | ~ v5_relat_1(B_88,A_89)
      | ~ v1_relat_1(B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_362,plain,(
    ! [B_88,A_89] :
      ( k2_relat_1(B_88) = A_89
      | ~ r1_tarski(A_89,k2_relat_1(B_88))
      | ~ v5_relat_1(B_88,A_89)
      | ~ v1_relat_1(B_88) ) ),
    inference(resolution,[status(thm)],[c_344,c_4])).

tff(c_1552,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1548,c_362])).

tff(c_1557,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_393,c_1552])).

tff(c_416,plain,(
    ! [B_98,A_99] :
      ( v5_relat_1(B_98,A_99)
      | ~ r1_tarski(k2_relat_1(B_98),A_99)
      | ~ v1_relat_1(B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_435,plain,(
    ! [B_98] :
      ( v5_relat_1(B_98,k2_relat_1(B_98))
      | ~ v1_relat_1(B_98) ) ),
    inference(resolution,[status(thm)],[c_8,c_416])).

tff(c_461,plain,(
    ! [B_104] :
      ( v2_funct_2(B_104,k2_relat_1(B_104))
      | ~ v5_relat_1(B_104,k2_relat_1(B_104))
      | ~ v1_relat_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_475,plain,(
    ! [B_98] :
      ( v2_funct_2(B_98,k2_relat_1(B_98))
      | ~ v1_relat_1(B_98) ) ),
    inference(resolution,[status(thm)],[c_435,c_461])).

tff(c_1576,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1557,c_475])).

tff(c_1597,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_1576])).

tff(c_1599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_633,c_1597])).

tff(c_1600,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_616])).

tff(c_26,plain,(
    ! [B_17,A_16] :
      ( v5_relat_1(B_17,A_16)
      | ~ r1_tarski(k2_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1617,plain,(
    ! [A_16] :
      ( v5_relat_1('#skF_4',A_16)
      | ~ r1_tarski('#skF_1',A_16)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1600,c_26])).

tff(c_2460,plain,(
    ! [A_305] :
      ( v5_relat_1('#skF_4',A_305)
      | ~ r1_tarski('#skF_1',A_305) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_1617])).

tff(c_12,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_165,plain,(
    ! [B_70,A_71] :
      ( ~ r1_xboole_0(B_70,A_71)
      | ~ r1_tarski(B_70,A_71)
      | v1_xboole_0(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_169,plain,(
    ! [A_5] :
      ( ~ r1_tarski(A_5,k1_xboole_0)
      | v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_165])).

tff(c_363,plain,(
    ! [B_88] :
      ( v1_xboole_0(k2_relat_1(B_88))
      | ~ v5_relat_1(B_88,k1_xboole_0)
      | ~ v1_relat_1(B_88) ) ),
    inference(resolution,[status(thm)],[c_344,c_169])).

tff(c_1605,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v5_relat_1('#skF_4',k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1600,c_363])).

tff(c_1624,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_1605])).

tff(c_1667,plain,(
    ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1624])).

tff(c_2471,plain,(
    ~ r1_tarski('#skF_1',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2460,c_1667])).

tff(c_3050,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3037,c_2471])).

tff(c_3078,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3050])).

tff(c_3079,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1624])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3084,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_3079,c_2])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3107,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3084,c_3084,c_18])).

tff(c_235,plain,(
    ! [B_78,A_79] :
      ( v1_xboole_0(B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_79))
      | ~ v1_xboole_0(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_253,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_74,c_235])).

tff(c_283,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_253])).

tff(c_3312,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3107,c_283])).

tff(c_3316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3079,c_3312])).

tff(c_3317,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_3322,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3317,c_2])).

tff(c_20,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3329,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_4',B_9) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3322,c_3322,c_20])).

tff(c_3332,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3322,c_3322,c_18])).

tff(c_3318,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_3422,plain,(
    ! [A_396] :
      ( A_396 = '#skF_4'
      | ~ v1_xboole_0(A_396) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3322,c_2])).

tff(c_3429,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3318,c_3422])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | k2_zfmisc_1(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3372,plain,(
    ! [B_9,A_8] :
      ( B_9 = '#skF_4'
      | A_8 = '#skF_4'
      | k2_zfmisc_1(A_8,B_9) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3322,c_3322,c_3322,c_16])).

tff(c_3485,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3429,c_3372])).

tff(c_3491,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3485])).

tff(c_252,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_80,c_235])).

tff(c_3323,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_3493,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3491,c_3323])).

tff(c_3501,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3317,c_3332,c_3493])).

tff(c_3502,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3485])).

tff(c_3523,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3502,c_3323])).

tff(c_3531,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3317,c_3329,c_3523])).

tff(c_3532,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_3537,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3532,c_2])).

tff(c_3555,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3322,c_3537])).

tff(c_3560,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3555,c_154])).

tff(c_170,plain,(
    ! [A_72] :
      ( ~ r1_tarski(A_72,k1_xboole_0)
      | v1_xboole_0(A_72) ) ),
    inference(resolution,[status(thm)],[c_12,c_165])).

tff(c_179,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_170])).

tff(c_155,plain,(
    ! [A_69] : m1_subset_1(k6_partfun1(A_69),k1_zfmisc_1(k2_zfmisc_1(A_69,A_69))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_159,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_155])).

tff(c_238,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_159,c_235])).

tff(c_250,plain,(
    v1_xboole_0(k6_partfun1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_238])).

tff(c_257,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_250,c_2])).

tff(c_277,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_85])).

tff(c_3538,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3322,c_277])).

tff(c_3570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3560,c_3538])).

tff(c_3571,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_3668,plain,(
    ! [B_407,A_408] :
      ( v1_relat_1(B_407)
      | ~ m1_subset_1(B_407,k1_zfmisc_1(A_408))
      | ~ v1_relat_1(A_408) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3680,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_74,c_3668])).

tff(c_3692,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3680])).

tff(c_3765,plain,(
    ! [C_419,B_420,A_421] :
      ( v5_relat_1(C_419,B_420)
      | ~ m1_subset_1(C_419,k1_zfmisc_1(k2_zfmisc_1(A_421,B_420))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_3783,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_3765])).

tff(c_3677,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_80,c_3668])).

tff(c_3689,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_3677])).

tff(c_4410,plain,(
    ! [C_503,A_498,F_500,D_499,B_502,E_501] :
      ( m1_subset_1(k1_partfun1(A_498,B_502,C_503,D_499,E_501,F_500),k1_zfmisc_1(k2_zfmisc_1(A_498,D_499)))
      | ~ m1_subset_1(F_500,k1_zfmisc_1(k2_zfmisc_1(C_503,D_499)))
      | ~ v1_funct_1(F_500)
      | ~ m1_subset_1(E_501,k1_zfmisc_1(k2_zfmisc_1(A_498,B_502)))
      | ~ v1_funct_1(E_501) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_4075,plain,(
    ! [D_454,C_455,A_456,B_457] :
      ( D_454 = C_455
      | ~ r2_relset_1(A_456,B_457,C_455,D_454)
      | ~ m1_subset_1(D_454,k1_zfmisc_1(k2_zfmisc_1(A_456,B_457)))
      | ~ m1_subset_1(C_455,k1_zfmisc_1(k2_zfmisc_1(A_456,B_457))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_4085,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_72,c_4075])).

tff(c_4104,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_4085])).

tff(c_4163,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4104])).

tff(c_4416,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4410,c_4163])).

tff(c_4448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_74,c_4416])).

tff(c_4449,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4104])).

tff(c_4657,plain,(
    ! [B_537,E_532,A_533,F_536,D_535,C_534] :
      ( k1_partfun1(A_533,B_537,C_534,D_535,E_532,F_536) = k5_relat_1(E_532,F_536)
      | ~ m1_subset_1(F_536,k1_zfmisc_1(k2_zfmisc_1(C_534,D_535)))
      | ~ v1_funct_1(F_536)
      | ~ m1_subset_1(E_532,k1_zfmisc_1(k2_zfmisc_1(A_533,B_537)))
      | ~ v1_funct_1(E_532) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_4663,plain,(
    ! [A_533,B_537,E_532] :
      ( k1_partfun1(A_533,B_537,'#skF_2','#skF_1',E_532,'#skF_4') = k5_relat_1(E_532,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_532,k1_zfmisc_1(k2_zfmisc_1(A_533,B_537)))
      | ~ v1_funct_1(E_532) ) ),
    inference(resolution,[status(thm)],[c_74,c_4657])).

tff(c_4912,plain,(
    ! [A_566,B_567,E_568] :
      ( k1_partfun1(A_566,B_567,'#skF_2','#skF_1',E_568,'#skF_4') = k5_relat_1(E_568,'#skF_4')
      | ~ m1_subset_1(E_568,k1_zfmisc_1(k2_zfmisc_1(A_566,B_567)))
      | ~ v1_funct_1(E_568) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4663])).

tff(c_4924,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_4912])).

tff(c_4941,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_4449,c_4924])).

tff(c_4951,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4941,c_32])).

tff(c_4957,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3689,c_3692,c_87,c_4951])).

tff(c_3822,plain,(
    ! [B_429,A_430] :
      ( r1_tarski(k2_relat_1(B_429),A_430)
      | ~ v5_relat_1(B_429,A_430)
      | ~ v1_relat_1(B_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3844,plain,(
    ! [B_429,A_430] :
      ( k2_relat_1(B_429) = A_430
      | ~ r1_tarski(A_430,k2_relat_1(B_429))
      | ~ v5_relat_1(B_429,A_430)
      | ~ v1_relat_1(B_429) ) ),
    inference(resolution,[status(thm)],[c_3822,c_4])).

tff(c_4961,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4957,c_3844])).

tff(c_4966,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3692,c_3783,c_4961])).

tff(c_3788,plain,(
    ! [B_423,A_424] :
      ( v5_relat_1(B_423,A_424)
      | ~ r1_tarski(k2_relat_1(B_423),A_424)
      | ~ v1_relat_1(B_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3803,plain,(
    ! [B_423] :
      ( v5_relat_1(B_423,k2_relat_1(B_423))
      | ~ v1_relat_1(B_423) ) ),
    inference(resolution,[status(thm)],[c_8,c_3788])).

tff(c_3880,plain,(
    ! [B_437] :
      ( v2_funct_2(B_437,k2_relat_1(B_437))
      | ~ v5_relat_1(B_437,k2_relat_1(B_437))
      | ~ v1_relat_1(B_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3894,plain,(
    ! [B_423] :
      ( v2_funct_2(B_423,k2_relat_1(B_423))
      | ~ v1_relat_1(B_423) ) ),
    inference(resolution,[status(thm)],[c_3803,c_3880])).

tff(c_4982,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4966,c_3894])).

tff(c_5004,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3692,c_4982])).

tff(c_5006,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3571,c_5004])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:41:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.73/2.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.73/2.35  
% 6.73/2.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.73/2.35  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_xboole_0 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.73/2.35  
% 6.73/2.35  %Foreground sorts:
% 6.73/2.35  
% 6.73/2.35  
% 6.73/2.35  %Background operators:
% 6.73/2.35  
% 6.73/2.35  
% 6.73/2.35  %Foreground operators:
% 6.73/2.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.73/2.35  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.73/2.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.73/2.35  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.73/2.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.73/2.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.73/2.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.73/2.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.73/2.35  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.73/2.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.73/2.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.73/2.35  tff('#skF_2', type, '#skF_2': $i).
% 6.73/2.35  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.73/2.35  tff('#skF_3', type, '#skF_3': $i).
% 6.73/2.35  tff('#skF_1', type, '#skF_1': $i).
% 6.73/2.35  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.73/2.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.73/2.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.73/2.35  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.73/2.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.73/2.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.73/2.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.73/2.35  tff('#skF_4', type, '#skF_4': $i).
% 6.73/2.35  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.73/2.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.73/2.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.73/2.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.73/2.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.73/2.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.73/2.35  
% 7.12/2.38  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.12/2.38  tff(f_182, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 7.12/2.38  tff(f_140, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.12/2.38  tff(f_90, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.12/2.38  tff(f_138, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.12/2.38  tff(f_124, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.12/2.38  tff(f_128, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.12/2.38  tff(f_104, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.12/2.38  tff(f_162, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 7.12/2.38  tff(f_75, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.12/2.38  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.12/2.38  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.12/2.38  tff(f_112, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.12/2.38  tff(f_86, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.12/2.38  tff(f_82, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 7.12/2.38  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.12/2.38  tff(f_39, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.12/2.38  tff(f_47, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 7.12/2.38  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.12/2.38  tff(f_53, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.12/2.38  tff(f_60, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 7.12/2.38  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.12/2.38  tff(c_70, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.12/2.38  tff(c_154, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_70])).
% 7.12/2.38  tff(c_84, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.12/2.38  tff(c_82, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.12/2.38  tff(c_80, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.12/2.38  tff(c_78, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.12/2.38  tff(c_76, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.12/2.38  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.12/2.38  tff(c_64, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_140])).
% 7.12/2.38  tff(c_40, plain, (![A_24]: (v2_funct_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.12/2.38  tff(c_85, plain, (![A_24]: (v2_funct_1(k6_partfun1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_40])).
% 7.12/2.38  tff(c_1809, plain, (![A_260, E_259, C_261, D_262, B_264, F_263]: (k1_partfun1(A_260, B_264, C_261, D_262, E_259, F_263)=k5_relat_1(E_259, F_263) | ~m1_subset_1(F_263, k1_zfmisc_1(k2_zfmisc_1(C_261, D_262))) | ~v1_funct_1(F_263) | ~m1_subset_1(E_259, k1_zfmisc_1(k2_zfmisc_1(A_260, B_264))) | ~v1_funct_1(E_259))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.12/2.38  tff(c_1815, plain, (![A_260, B_264, E_259]: (k1_partfun1(A_260, B_264, '#skF_2', '#skF_1', E_259, '#skF_4')=k5_relat_1(E_259, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_259, k1_zfmisc_1(k2_zfmisc_1(A_260, B_264))) | ~v1_funct_1(E_259))), inference(resolution, [status(thm)], [c_74, c_1809])).
% 7.12/2.38  tff(c_2009, plain, (![A_286, B_287, E_288]: (k1_partfun1(A_286, B_287, '#skF_2', '#skF_1', E_288, '#skF_4')=k5_relat_1(E_288, '#skF_4') | ~m1_subset_1(E_288, k1_zfmisc_1(k2_zfmisc_1(A_286, B_287))) | ~v1_funct_1(E_288))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1815])).
% 7.12/2.38  tff(c_2018, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_2009])).
% 7.12/2.38  tff(c_2032, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_2018])).
% 7.12/2.38  tff(c_54, plain, (![D_37, A_34, F_39, B_35, C_36, E_38]: (m1_subset_1(k1_partfun1(A_34, B_35, C_36, D_37, E_38, F_39), k1_zfmisc_1(k2_zfmisc_1(A_34, D_37))) | ~m1_subset_1(F_39, k1_zfmisc_1(k2_zfmisc_1(C_36, D_37))) | ~v1_funct_1(F_39) | ~m1_subset_1(E_38, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~v1_funct_1(E_38))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.12/2.38  tff(c_2041, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2032, c_54])).
% 7.12/2.38  tff(c_2045, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_74, c_2041])).
% 7.12/2.38  tff(c_60, plain, (![A_40]: (m1_subset_1(k6_partfun1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.12/2.38  tff(c_72, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 7.12/2.38  tff(c_1636, plain, (![D_240, C_241, A_242, B_243]: (D_240=C_241 | ~r2_relset_1(A_242, B_243, C_241, D_240) | ~m1_subset_1(D_240, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))) | ~m1_subset_1(C_241, k1_zfmisc_1(k2_zfmisc_1(A_242, B_243))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.12/2.38  tff(c_1646, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_72, c_1636])).
% 7.12/2.38  tff(c_1665, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1646])).
% 7.12/2.38  tff(c_1668, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1665])).
% 7.12/2.38  tff(c_2437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2045, c_2032, c_1668])).
% 7.12/2.38  tff(c_2438, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1665])).
% 7.12/2.38  tff(c_3028, plain, (![B_361, A_362, D_360, C_363, E_359]: (k1_xboole_0=C_363 | v2_funct_1(D_360) | ~v2_funct_1(k1_partfun1(A_362, B_361, B_361, C_363, D_360, E_359)) | ~m1_subset_1(E_359, k1_zfmisc_1(k2_zfmisc_1(B_361, C_363))) | ~v1_funct_2(E_359, B_361, C_363) | ~v1_funct_1(E_359) | ~m1_subset_1(D_360, k1_zfmisc_1(k2_zfmisc_1(A_362, B_361))) | ~v1_funct_2(D_360, A_362, B_361) | ~v1_funct_1(D_360))), inference(cnfTransformation, [status(thm)], [f_162])).
% 7.12/2.38  tff(c_3032, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2438, c_3028])).
% 7.12/2.38  tff(c_3036, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_85, c_3032])).
% 7.12/2.38  tff(c_3037, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_154, c_3036])).
% 7.12/2.38  tff(c_30, plain, (![A_18, B_19]: (v1_relat_1(k2_zfmisc_1(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 7.12/2.38  tff(c_187, plain, (![B_73, A_74]: (v1_relat_1(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.12/2.38  tff(c_199, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_74, c_187])).
% 7.12/2.38  tff(c_211, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_199])).
% 7.12/2.38  tff(c_375, plain, (![C_93, B_94, A_95]: (v5_relat_1(C_93, B_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_95, B_94))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.12/2.38  tff(c_393, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_375])).
% 7.12/2.38  tff(c_584, plain, (![B_117, A_118]: (k2_relat_1(B_117)=A_118 | ~v2_funct_2(B_117, A_118) | ~v5_relat_1(B_117, A_118) | ~v1_relat_1(B_117))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.12/2.38  tff(c_599, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_393, c_584])).
% 7.12/2.38  tff(c_616, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_211, c_599])).
% 7.12/2.38  tff(c_633, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitLeft, [status(thm)], [c_616])).
% 7.12/2.38  tff(c_196, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_80, c_187])).
% 7.12/2.38  tff(c_208, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_196])).
% 7.12/2.38  tff(c_36, plain, (![A_23]: (k2_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.12/2.38  tff(c_87, plain, (![A_23]: (k2_relat_1(k6_partfun1(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_36])).
% 7.12/2.38  tff(c_1012, plain, (![B_172, F_170, D_169, C_173, E_171, A_168]: (m1_subset_1(k1_partfun1(A_168, B_172, C_173, D_169, E_171, F_170), k1_zfmisc_1(k2_zfmisc_1(A_168, D_169))) | ~m1_subset_1(F_170, k1_zfmisc_1(k2_zfmisc_1(C_173, D_169))) | ~v1_funct_1(F_170) | ~m1_subset_1(E_171, k1_zfmisc_1(k2_zfmisc_1(A_168, B_172))) | ~v1_funct_1(E_171))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.12/2.38  tff(c_715, plain, (![D_123, C_124, A_125, B_126]: (D_123=C_124 | ~r2_relset_1(A_125, B_126, C_124, D_123) | ~m1_subset_1(D_123, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.12/2.38  tff(c_725, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_72, c_715])).
% 7.12/2.38  tff(c_744, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_725])).
% 7.12/2.38  tff(c_777, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_744])).
% 7.12/2.38  tff(c_1018, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1012, c_777])).
% 7.12/2.38  tff(c_1050, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_74, c_1018])).
% 7.12/2.38  tff(c_1051, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_744])).
% 7.12/2.38  tff(c_1233, plain, (![B_205, E_200, D_203, C_202, F_204, A_201]: (k1_partfun1(A_201, B_205, C_202, D_203, E_200, F_204)=k5_relat_1(E_200, F_204) | ~m1_subset_1(F_204, k1_zfmisc_1(k2_zfmisc_1(C_202, D_203))) | ~v1_funct_1(F_204) | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_201, B_205))) | ~v1_funct_1(E_200))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.12/2.38  tff(c_1239, plain, (![A_201, B_205, E_200]: (k1_partfun1(A_201, B_205, '#skF_2', '#skF_1', E_200, '#skF_4')=k5_relat_1(E_200, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_200, k1_zfmisc_1(k2_zfmisc_1(A_201, B_205))) | ~v1_funct_1(E_200))), inference(resolution, [status(thm)], [c_74, c_1233])).
% 7.12/2.38  tff(c_1503, plain, (![A_237, B_238, E_239]: (k1_partfun1(A_237, B_238, '#skF_2', '#skF_1', E_239, '#skF_4')=k5_relat_1(E_239, '#skF_4') | ~m1_subset_1(E_239, k1_zfmisc_1(k2_zfmisc_1(A_237, B_238))) | ~v1_funct_1(E_239))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1239])).
% 7.12/2.38  tff(c_1515, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_1503])).
% 7.12/2.38  tff(c_1532, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_1051, c_1515])).
% 7.12/2.38  tff(c_32, plain, (![A_20, B_22]: (r1_tarski(k2_relat_1(k5_relat_1(A_20, B_22)), k2_relat_1(B_22)) | ~v1_relat_1(B_22) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.12/2.38  tff(c_1542, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1532, c_32])).
% 7.12/2.38  tff(c_1548, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_211, c_87, c_1542])).
% 7.12/2.38  tff(c_344, plain, (![B_88, A_89]: (r1_tarski(k2_relat_1(B_88), A_89) | ~v5_relat_1(B_88, A_89) | ~v1_relat_1(B_88))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.12/2.38  tff(c_4, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.12/2.38  tff(c_362, plain, (![B_88, A_89]: (k2_relat_1(B_88)=A_89 | ~r1_tarski(A_89, k2_relat_1(B_88)) | ~v5_relat_1(B_88, A_89) | ~v1_relat_1(B_88))), inference(resolution, [status(thm)], [c_344, c_4])).
% 7.12/2.38  tff(c_1552, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1548, c_362])).
% 7.12/2.38  tff(c_1557, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_211, c_393, c_1552])).
% 7.12/2.38  tff(c_416, plain, (![B_98, A_99]: (v5_relat_1(B_98, A_99) | ~r1_tarski(k2_relat_1(B_98), A_99) | ~v1_relat_1(B_98))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.12/2.38  tff(c_435, plain, (![B_98]: (v5_relat_1(B_98, k2_relat_1(B_98)) | ~v1_relat_1(B_98))), inference(resolution, [status(thm)], [c_8, c_416])).
% 7.12/2.38  tff(c_461, plain, (![B_104]: (v2_funct_2(B_104, k2_relat_1(B_104)) | ~v5_relat_1(B_104, k2_relat_1(B_104)) | ~v1_relat_1(B_104))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.12/2.38  tff(c_475, plain, (![B_98]: (v2_funct_2(B_98, k2_relat_1(B_98)) | ~v1_relat_1(B_98))), inference(resolution, [status(thm)], [c_435, c_461])).
% 7.12/2.38  tff(c_1576, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1557, c_475])).
% 7.12/2.38  tff(c_1597, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_211, c_1576])).
% 7.12/2.38  tff(c_1599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_633, c_1597])).
% 7.12/2.38  tff(c_1600, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_616])).
% 7.12/2.38  tff(c_26, plain, (![B_17, A_16]: (v5_relat_1(B_17, A_16) | ~r1_tarski(k2_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.12/2.38  tff(c_1617, plain, (![A_16]: (v5_relat_1('#skF_4', A_16) | ~r1_tarski('#skF_1', A_16) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1600, c_26])).
% 7.12/2.38  tff(c_2460, plain, (![A_305]: (v5_relat_1('#skF_4', A_305) | ~r1_tarski('#skF_1', A_305))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_1617])).
% 7.12/2.38  tff(c_12, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.12/2.38  tff(c_165, plain, (![B_70, A_71]: (~r1_xboole_0(B_70, A_71) | ~r1_tarski(B_70, A_71) | v1_xboole_0(B_70))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.12/2.38  tff(c_169, plain, (![A_5]: (~r1_tarski(A_5, k1_xboole_0) | v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_12, c_165])).
% 7.12/2.38  tff(c_363, plain, (![B_88]: (v1_xboole_0(k2_relat_1(B_88)) | ~v5_relat_1(B_88, k1_xboole_0) | ~v1_relat_1(B_88))), inference(resolution, [status(thm)], [c_344, c_169])).
% 7.12/2.38  tff(c_1605, plain, (v1_xboole_0('#skF_1') | ~v5_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1600, c_363])).
% 7.12/2.38  tff(c_1624, plain, (v1_xboole_0('#skF_1') | ~v5_relat_1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_211, c_1605])).
% 7.12/2.38  tff(c_1667, plain, (~v5_relat_1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1624])).
% 7.12/2.38  tff(c_2471, plain, (~r1_tarski('#skF_1', k1_xboole_0)), inference(resolution, [status(thm)], [c_2460, c_1667])).
% 7.12/2.38  tff(c_3050, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3037, c_2471])).
% 7.12/2.38  tff(c_3078, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_3050])).
% 7.12/2.38  tff(c_3079, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_1624])).
% 7.12/2.38  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.12/2.38  tff(c_3084, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_3079, c_2])).
% 7.12/2.38  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.12/2.38  tff(c_3107, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3084, c_3084, c_18])).
% 7.12/2.38  tff(c_235, plain, (![B_78, A_79]: (v1_xboole_0(B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_79)) | ~v1_xboole_0(A_79))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.12/2.38  tff(c_253, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_74, c_235])).
% 7.12/2.38  tff(c_283, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_253])).
% 7.12/2.38  tff(c_3312, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3107, c_283])).
% 7.12/2.38  tff(c_3316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3079, c_3312])).
% 7.12/2.38  tff(c_3317, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_253])).
% 7.12/2.38  tff(c_3322, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_3317, c_2])).
% 7.12/2.38  tff(c_20, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.12/2.38  tff(c_3329, plain, (![B_9]: (k2_zfmisc_1('#skF_4', B_9)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3322, c_3322, c_20])).
% 7.12/2.38  tff(c_3332, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3322, c_3322, c_18])).
% 7.12/2.38  tff(c_3318, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_253])).
% 7.12/2.38  tff(c_3422, plain, (![A_396]: (A_396='#skF_4' | ~v1_xboole_0(A_396))), inference(demodulation, [status(thm), theory('equality')], [c_3322, c_2])).
% 7.12/2.38  tff(c_3429, plain, (k2_zfmisc_1('#skF_2', '#skF_1')='#skF_4'), inference(resolution, [status(thm)], [c_3318, c_3422])).
% 7.12/2.38  tff(c_16, plain, (![B_9, A_8]: (k1_xboole_0=B_9 | k1_xboole_0=A_8 | k2_zfmisc_1(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.12/2.38  tff(c_3372, plain, (![B_9, A_8]: (B_9='#skF_4' | A_8='#skF_4' | k2_zfmisc_1(A_8, B_9)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3322, c_3322, c_3322, c_16])).
% 7.12/2.38  tff(c_3485, plain, ('#skF_1'='#skF_4' | '#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3429, c_3372])).
% 7.12/2.38  tff(c_3491, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_3485])).
% 7.12/2.38  tff(c_252, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_80, c_235])).
% 7.12/2.38  tff(c_3323, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_252])).
% 7.12/2.38  tff(c_3493, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3491, c_3323])).
% 7.12/2.38  tff(c_3501, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3317, c_3332, c_3493])).
% 7.12/2.38  tff(c_3502, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_3485])).
% 7.12/2.38  tff(c_3523, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3502, c_3323])).
% 7.12/2.38  tff(c_3531, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3317, c_3329, c_3523])).
% 7.12/2.38  tff(c_3532, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_252])).
% 7.12/2.38  tff(c_3537, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3532, c_2])).
% 7.12/2.38  tff(c_3555, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3322, c_3537])).
% 7.12/2.38  tff(c_3560, plain, (~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3555, c_154])).
% 7.12/2.38  tff(c_170, plain, (![A_72]: (~r1_tarski(A_72, k1_xboole_0) | v1_xboole_0(A_72))), inference(resolution, [status(thm)], [c_12, c_165])).
% 7.12/2.38  tff(c_179, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_170])).
% 7.12/2.38  tff(c_155, plain, (![A_69]: (m1_subset_1(k6_partfun1(A_69), k1_zfmisc_1(k2_zfmisc_1(A_69, A_69))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 7.12/2.38  tff(c_159, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_155])).
% 7.12/2.38  tff(c_238, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_159, c_235])).
% 7.12/2.38  tff(c_250, plain, (v1_xboole_0(k6_partfun1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_238])).
% 7.12/2.38  tff(c_257, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_250, c_2])).
% 7.12/2.38  tff(c_277, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_257, c_85])).
% 7.12/2.38  tff(c_3538, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3322, c_277])).
% 7.12/2.38  tff(c_3570, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3560, c_3538])).
% 7.12/2.38  tff(c_3571, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_70])).
% 7.12/2.38  tff(c_3668, plain, (![B_407, A_408]: (v1_relat_1(B_407) | ~m1_subset_1(B_407, k1_zfmisc_1(A_408)) | ~v1_relat_1(A_408))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.12/2.38  tff(c_3680, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_74, c_3668])).
% 7.12/2.38  tff(c_3692, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3680])).
% 7.12/2.38  tff(c_3765, plain, (![C_419, B_420, A_421]: (v5_relat_1(C_419, B_420) | ~m1_subset_1(C_419, k1_zfmisc_1(k2_zfmisc_1(A_421, B_420))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.12/2.38  tff(c_3783, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_74, c_3765])).
% 7.12/2.38  tff(c_3677, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_80, c_3668])).
% 7.12/2.38  tff(c_3689, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_3677])).
% 7.12/2.38  tff(c_4410, plain, (![C_503, A_498, F_500, D_499, B_502, E_501]: (m1_subset_1(k1_partfun1(A_498, B_502, C_503, D_499, E_501, F_500), k1_zfmisc_1(k2_zfmisc_1(A_498, D_499))) | ~m1_subset_1(F_500, k1_zfmisc_1(k2_zfmisc_1(C_503, D_499))) | ~v1_funct_1(F_500) | ~m1_subset_1(E_501, k1_zfmisc_1(k2_zfmisc_1(A_498, B_502))) | ~v1_funct_1(E_501))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.12/2.38  tff(c_4075, plain, (![D_454, C_455, A_456, B_457]: (D_454=C_455 | ~r2_relset_1(A_456, B_457, C_455, D_454) | ~m1_subset_1(D_454, k1_zfmisc_1(k2_zfmisc_1(A_456, B_457))) | ~m1_subset_1(C_455, k1_zfmisc_1(k2_zfmisc_1(A_456, B_457))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 7.12/2.38  tff(c_4085, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_72, c_4075])).
% 7.12/2.38  tff(c_4104, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_4085])).
% 7.12/2.38  tff(c_4163, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_4104])).
% 7.12/2.38  tff(c_4416, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4410, c_4163])).
% 7.12/2.38  tff(c_4448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_74, c_4416])).
% 7.12/2.38  tff(c_4449, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_4104])).
% 7.12/2.38  tff(c_4657, plain, (![B_537, E_532, A_533, F_536, D_535, C_534]: (k1_partfun1(A_533, B_537, C_534, D_535, E_532, F_536)=k5_relat_1(E_532, F_536) | ~m1_subset_1(F_536, k1_zfmisc_1(k2_zfmisc_1(C_534, D_535))) | ~v1_funct_1(F_536) | ~m1_subset_1(E_532, k1_zfmisc_1(k2_zfmisc_1(A_533, B_537))) | ~v1_funct_1(E_532))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.12/2.38  tff(c_4663, plain, (![A_533, B_537, E_532]: (k1_partfun1(A_533, B_537, '#skF_2', '#skF_1', E_532, '#skF_4')=k5_relat_1(E_532, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_532, k1_zfmisc_1(k2_zfmisc_1(A_533, B_537))) | ~v1_funct_1(E_532))), inference(resolution, [status(thm)], [c_74, c_4657])).
% 7.12/2.38  tff(c_4912, plain, (![A_566, B_567, E_568]: (k1_partfun1(A_566, B_567, '#skF_2', '#skF_1', E_568, '#skF_4')=k5_relat_1(E_568, '#skF_4') | ~m1_subset_1(E_568, k1_zfmisc_1(k2_zfmisc_1(A_566, B_567))) | ~v1_funct_1(E_568))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4663])).
% 7.12/2.38  tff(c_4924, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_4912])).
% 7.12/2.38  tff(c_4941, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_4449, c_4924])).
% 7.12/2.38  tff(c_4951, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4941, c_32])).
% 7.12/2.38  tff(c_4957, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3689, c_3692, c_87, c_4951])).
% 7.12/2.38  tff(c_3822, plain, (![B_429, A_430]: (r1_tarski(k2_relat_1(B_429), A_430) | ~v5_relat_1(B_429, A_430) | ~v1_relat_1(B_429))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.12/2.38  tff(c_3844, plain, (![B_429, A_430]: (k2_relat_1(B_429)=A_430 | ~r1_tarski(A_430, k2_relat_1(B_429)) | ~v5_relat_1(B_429, A_430) | ~v1_relat_1(B_429))), inference(resolution, [status(thm)], [c_3822, c_4])).
% 7.12/2.38  tff(c_4961, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4957, c_3844])).
% 7.12/2.38  tff(c_4966, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3692, c_3783, c_4961])).
% 7.12/2.38  tff(c_3788, plain, (![B_423, A_424]: (v5_relat_1(B_423, A_424) | ~r1_tarski(k2_relat_1(B_423), A_424) | ~v1_relat_1(B_423))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.12/2.38  tff(c_3803, plain, (![B_423]: (v5_relat_1(B_423, k2_relat_1(B_423)) | ~v1_relat_1(B_423))), inference(resolution, [status(thm)], [c_8, c_3788])).
% 7.12/2.38  tff(c_3880, plain, (![B_437]: (v2_funct_2(B_437, k2_relat_1(B_437)) | ~v5_relat_1(B_437, k2_relat_1(B_437)) | ~v1_relat_1(B_437))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.12/2.38  tff(c_3894, plain, (![B_423]: (v2_funct_2(B_423, k2_relat_1(B_423)) | ~v1_relat_1(B_423))), inference(resolution, [status(thm)], [c_3803, c_3880])).
% 7.12/2.38  tff(c_4982, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4966, c_3894])).
% 7.12/2.38  tff(c_5004, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3692, c_4982])).
% 7.12/2.38  tff(c_5006, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3571, c_5004])).
% 7.12/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.12/2.38  
% 7.12/2.38  Inference rules
% 7.12/2.38  ----------------------
% 7.12/2.38  #Ref     : 0
% 7.12/2.38  #Sup     : 1029
% 7.12/2.38  #Fact    : 0
% 7.12/2.38  #Define  : 0
% 7.12/2.38  #Split   : 24
% 7.12/2.38  #Chain   : 0
% 7.12/2.38  #Close   : 0
% 7.12/2.38  
% 7.12/2.38  Ordering : KBO
% 7.12/2.38  
% 7.12/2.38  Simplification rules
% 7.12/2.38  ----------------------
% 7.12/2.38  #Subsume      : 117
% 7.12/2.38  #Demod        : 1007
% 7.12/2.38  #Tautology    : 341
% 7.12/2.38  #SimpNegUnit  : 5
% 7.12/2.38  #BackRed      : 129
% 7.12/2.38  
% 7.12/2.38  #Partial instantiations: 0
% 7.12/2.38  #Strategies tried      : 1
% 7.12/2.38  
% 7.12/2.38  Timing (in seconds)
% 7.12/2.38  ----------------------
% 7.12/2.38  Preprocessing        : 0.36
% 7.12/2.38  Parsing              : 0.19
% 7.12/2.38  CNF conversion       : 0.03
% 7.12/2.38  Main loop            : 1.22
% 7.12/2.38  Inferencing          : 0.43
% 7.12/2.38  Reduction            : 0.44
% 7.12/2.38  Demodulation         : 0.32
% 7.12/2.38  BG Simplification    : 0.04
% 7.12/2.38  Subsumption          : 0.20
% 7.12/2.38  Abstraction          : 0.05
% 7.12/2.38  MUC search           : 0.00
% 7.12/2.38  Cooper               : 0.00
% 7.12/2.38  Total                : 1.64
% 7.12/2.38  Index Insertion      : 0.00
% 7.12/2.38  Index Deletion       : 0.00
% 7.12/2.38  Index Matching       : 0.00
% 7.12/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
