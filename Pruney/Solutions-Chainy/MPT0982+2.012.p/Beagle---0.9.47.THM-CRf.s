%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:56 EST 2020

% Result     : Theorem 12.70s
% Output     : CNFRefutation 12.84s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 395 expanded)
%              Number of leaves         :   45 ( 156 expanded)
%              Depth                    :   19
%              Number of atoms          :  252 (1336 expanded)
%              Number of equality atoms :   83 ( 369 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_165,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C
                & v2_funct_1(E) )
             => ( C = k1_xboole_0
                | k2_relset_1(A,B,D) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_143,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_133,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A)
              & v2_funct_1(A) )
           => r1_tarski(k1_relat_1(A),k2_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k2_relat_1(B))
       => k2_relat_1(k8_relat_1(A,B)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_relat_1)).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_27857,plain,(
    ! [F_1071,B_1069,C_1072,E_1067,A_1070,D_1068] :
      ( k1_partfun1(A_1070,B_1069,C_1072,D_1068,E_1067,F_1071) = k5_relat_1(E_1067,F_1071)
      | ~ m1_subset_1(F_1071,k1_zfmisc_1(k2_zfmisc_1(C_1072,D_1068)))
      | ~ v1_funct_1(F_1071)
      | ~ m1_subset_1(E_1067,k1_zfmisc_1(k2_zfmisc_1(A_1070,B_1069)))
      | ~ v1_funct_1(E_1067) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_27861,plain,(
    ! [A_1070,B_1069,E_1067] :
      ( k1_partfun1(A_1070,B_1069,'#skF_2','#skF_3',E_1067,'#skF_5') = k5_relat_1(E_1067,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_1067,k1_zfmisc_1(k2_zfmisc_1(A_1070,B_1069)))
      | ~ v1_funct_1(E_1067) ) ),
    inference(resolution,[status(thm)],[c_62,c_27857])).

tff(c_28084,plain,(
    ! [A_1083,B_1084,E_1085] :
      ( k1_partfun1(A_1083,B_1084,'#skF_2','#skF_3',E_1085,'#skF_5') = k5_relat_1(E_1085,'#skF_5')
      | ~ m1_subset_1(E_1085,k1_zfmisc_1(k2_zfmisc_1(A_1083,B_1084)))
      | ~ v1_funct_1(E_1085) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_27861])).

tff(c_28090,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_28084])).

tff(c_28097,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_28090])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_28102,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28097,c_60])).

tff(c_48,plain,(
    ! [F_41,D_39,A_36,E_40,C_38,B_37] :
      ( m1_subset_1(k1_partfun1(A_36,B_37,C_38,D_39,E_40,F_41),k1_zfmisc_1(k2_zfmisc_1(A_36,D_39)))
      | ~ m1_subset_1(F_41,k1_zfmisc_1(k2_zfmisc_1(C_38,D_39)))
      | ~ v1_funct_1(F_41)
      | ~ m1_subset_1(E_40,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37)))
      | ~ v1_funct_1(E_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_28106,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_28097,c_48])).

tff(c_28110,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_28106])).

tff(c_34,plain,(
    ! [A_30,B_31,C_32] :
      ( k2_relset_1(A_30,B_31,C_32) = k2_relat_1(C_32)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_28137,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_28110,c_34])).

tff(c_28172,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28102,c_28137])).

tff(c_9113,plain,(
    ! [A_447,B_448,C_449] :
      ( k2_relset_1(A_447,B_448,C_449) = k2_relat_1(C_449)
      | ~ m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(A_447,B_448))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_9120,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_9113])).

tff(c_54,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_9122,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9120,c_54])).

tff(c_82,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_89,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_82])).

tff(c_100,plain,(
    ! [C_58,B_59,A_60] :
      ( v5_relat_1(C_58,B_59)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_60,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_107,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_100])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v5_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_217,plain,(
    ! [A_72,B_73] :
      ( k8_relat_1(A_72,B_73) = B_73
      | ~ r1_tarski(k2_relat_1(B_73),A_72)
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_8733,plain,(
    ! [A_427,B_428] :
      ( k8_relat_1(A_427,B_428) = B_428
      | ~ v5_relat_1(B_428,A_427)
      | ~ v1_relat_1(B_428) ) ),
    inference(resolution,[status(thm)],[c_10,c_217])).

tff(c_8748,plain,
    ( k8_relat_1('#skF_2','#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_107,c_8733])).

tff(c_8761,plain,(
    k8_relat_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_8748])).

tff(c_90,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_82])).

tff(c_58,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_64,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_9096,plain,(
    ! [A_444,B_445,C_446] :
      ( k1_relset_1(A_444,B_445,C_446) = k1_relat_1(C_446)
      | ~ m1_subset_1(C_446,k1_zfmisc_1(k2_zfmisc_1(A_444,B_445))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_9104,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_9096])).

tff(c_22114,plain,(
    ! [B_890,A_891,C_892] :
      ( k1_xboole_0 = B_890
      | k1_relset_1(A_891,B_890,C_892) = A_891
      | ~ v1_funct_2(C_892,A_891,B_890)
      | ~ m1_subset_1(C_892,k1_zfmisc_1(k2_zfmisc_1(A_891,B_890))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_22120,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_22114])).

tff(c_22126,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_9104,c_22120])).

tff(c_22127,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_22126])).

tff(c_25703,plain,(
    ! [A_998,B_999] :
      ( r1_tarski(k1_relat_1(A_998),k2_relat_1(B_999))
      | ~ v2_funct_1(A_998)
      | k2_relat_1(k5_relat_1(B_999,A_998)) != k2_relat_1(A_998)
      | ~ v1_funct_1(B_999)
      | ~ v1_relat_1(B_999)
      | ~ v1_funct_1(A_998)
      | ~ v1_relat_1(A_998) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_25721,plain,(
    ! [B_999] :
      ( r1_tarski('#skF_2',k2_relat_1(B_999))
      | ~ v2_funct_1('#skF_5')
      | k2_relat_1(k5_relat_1(B_999,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_999)
      | ~ v1_relat_1(B_999)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22127,c_25703])).

tff(c_25840,plain,(
    ! [B_1000] :
      ( r1_tarski('#skF_2',k2_relat_1(B_1000))
      | k2_relat_1(k5_relat_1(B_1000,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_1000)
      | ~ v1_relat_1(B_1000) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_66,c_58,c_25721])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k2_relat_1(k8_relat_1(A_5,B_6)) = A_5
      | ~ r1_tarski(A_5,k2_relat_1(B_6))
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_27525,plain,(
    ! [B_1056] :
      ( k2_relat_1(k8_relat_1('#skF_2',B_1056)) = '#skF_2'
      | k2_relat_1(k5_relat_1(B_1056,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_1056)
      | ~ v1_relat_1(B_1056) ) ),
    inference(resolution,[status(thm)],[c_25840,c_12])).

tff(c_27582,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != k2_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8761,c_27525])).

tff(c_27588,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_72,c_27582])).

tff(c_27589,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) != k2_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_9122,c_27588])).

tff(c_28199,plain,(
    k2_relat_1('#skF_5') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28172,c_27589])).

tff(c_108,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_100])).

tff(c_8982,plain,(
    ! [B_438,A_439] :
      ( k9_relat_1(B_438,k2_relat_1(A_439)) = k2_relat_1(k5_relat_1(A_439,B_438))
      | ~ v1_relat_1(B_438)
      | ~ v1_relat_1(A_439) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ! [C_55,A_56,B_57] :
      ( v4_relat_1(C_55,A_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_99,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_91])).

tff(c_113,plain,(
    ! [B_61,A_62] :
      ( k7_relat_1(B_61,A_62) = B_61
      | ~ v4_relat_1(B_61,A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_116,plain,
    ( k7_relat_1('#skF_5','#skF_2') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_99,c_113])).

tff(c_122,plain,(
    k7_relat_1('#skF_5','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_116])).

tff(c_134,plain,(
    ! [B_63,A_64] :
      ( k2_relat_1(k7_relat_1(B_63,A_64)) = k9_relat_1(B_63,A_64)
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_146,plain,
    ( k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_134])).

tff(c_152,plain,(
    k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_146])).

tff(c_314,plain,(
    ! [A_79,B_80,C_81] :
      ( k1_relset_1(A_79,B_80,C_81) = k1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_322,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_314])).

tff(c_702,plain,(
    ! [B_112,A_113,C_114] :
      ( k1_xboole_0 = B_112
      | k1_relset_1(A_113,B_112,C_114) = A_113
      | ~ v1_funct_2(C_114,A_113,B_112)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_708,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_702])).

tff(c_714,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_322,c_708])).

tff(c_715,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_714])).

tff(c_185,plain,(
    ! [B_70,A_71] :
      ( r1_tarski(k9_relat_1(B_70,A_71),k9_relat_1(B_70,k1_relat_1(B_70)))
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_190,plain,
    ( r1_tarski(k2_relat_1('#skF_5'),k9_relat_1('#skF_5',k1_relat_1('#skF_5')))
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_185])).

tff(c_196,plain,(
    r1_tarski(k2_relat_1('#skF_5'),k9_relat_1('#skF_5',k1_relat_1('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_190])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_207,plain,
    ( k9_relat_1('#skF_5',k1_relat_1('#skF_5')) = k2_relat_1('#skF_5')
    | ~ r1_tarski(k9_relat_1('#skF_5',k1_relat_1('#skF_5')),k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_196,c_2])).

tff(c_262,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5',k1_relat_1('#skF_5')),k2_relat_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_717,plain,(
    ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_715,c_262])).

tff(c_723,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_152,c_717])).

tff(c_724,plain,(
    k9_relat_1('#skF_5',k1_relat_1('#skF_5')) = k2_relat_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_16,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k9_relat_1(B_10,A_9),k9_relat_1(B_10,k1_relat_1(B_10)))
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_736,plain,(
    ! [A_9] :
      ( r1_tarski(k9_relat_1('#skF_5',A_9),k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_724,c_16])).

tff(c_742,plain,(
    ! [A_9] : r1_tarski(k9_relat_1('#skF_5',A_9),k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_736])).

tff(c_9013,plain,(
    ! [A_439] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_439,'#skF_5')),k2_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_439) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8982,c_742])).

tff(c_9050,plain,(
    ! [A_439] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_439,'#skF_5')),k2_relat_1('#skF_5'))
      | ~ v1_relat_1(A_439) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_9013])).

tff(c_174,plain,(
    ! [B_68,A_69] :
      ( r1_tarski(k2_relat_1(B_68),A_69)
      | ~ v5_relat_1(B_68,A_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_9132,plain,(
    ! [B_452,A_453] :
      ( k2_relat_1(B_452) = A_453
      | ~ r1_tarski(A_453,k2_relat_1(B_452))
      | ~ v5_relat_1(B_452,A_453)
      | ~ v1_relat_1(B_452) ) ),
    inference(resolution,[status(thm)],[c_174,c_2])).

tff(c_9138,plain,(
    ! [A_439] :
      ( k2_relat_1(k5_relat_1(A_439,'#skF_5')) = k2_relat_1('#skF_5')
      | ~ v5_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_439,'#skF_5')))
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_439) ) ),
    inference(resolution,[status(thm)],[c_9050,c_9132])).

tff(c_9170,plain,(
    ! [A_439] :
      ( k2_relat_1(k5_relat_1(A_439,'#skF_5')) = k2_relat_1('#skF_5')
      | ~ v5_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_439,'#skF_5')))
      | ~ v1_relat_1(A_439) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_9138])).

tff(c_28218,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_28172,c_9170])).

tff(c_28280,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_108,c_28172,c_28218])).

tff(c_28314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28199,c_28280])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:46:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.70/5.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.79/5.35  
% 12.79/5.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.79/5.35  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.79/5.35  
% 12.79/5.35  %Foreground sorts:
% 12.79/5.35  
% 12.79/5.35  
% 12.79/5.35  %Background operators:
% 12.79/5.35  
% 12.79/5.35  
% 12.79/5.35  %Foreground operators:
% 12.79/5.35  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.79/5.35  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 12.79/5.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.79/5.35  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 12.79/5.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.79/5.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 12.79/5.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.79/5.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 12.79/5.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.79/5.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.79/5.35  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.79/5.35  tff('#skF_5', type, '#skF_5': $i).
% 12.79/5.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.79/5.35  tff('#skF_2', type, '#skF_2': $i).
% 12.79/5.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.79/5.35  tff('#skF_3', type, '#skF_3': $i).
% 12.79/5.35  tff('#skF_1', type, '#skF_1': $i).
% 12.79/5.35  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 12.79/5.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 12.79/5.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.79/5.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.79/5.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.79/5.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.79/5.35  tff('#skF_4', type, '#skF_4': $i).
% 12.79/5.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.79/5.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 12.79/5.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.79/5.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.79/5.35  
% 12.84/5.38  tff(f_165, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_funct_2)).
% 12.84/5.38  tff(f_143, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 12.84/5.38  tff(f_133, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 12.84/5.38  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.84/5.38  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 12.84/5.38  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 12.84/5.38  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 12.84/5.38  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 12.84/5.38  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 12.84/5.38  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 12.84/5.38  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A)) & v2_funct_1(A)) => r1_tarski(k1_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_funct_1)).
% 12.84/5.38  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k2_relat_1(B)) => (k2_relat_1(k8_relat_1(A, B)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_relat_1)).
% 12.84/5.38  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 12.84/5.38  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.84/5.38  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 12.84/5.38  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 12.84/5.38  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k9_relat_1(B, k1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_relat_1)).
% 12.84/5.38  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.84/5.38  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.84/5.38  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.84/5.38  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.84/5.38  tff(c_27857, plain, (![F_1071, B_1069, C_1072, E_1067, A_1070, D_1068]: (k1_partfun1(A_1070, B_1069, C_1072, D_1068, E_1067, F_1071)=k5_relat_1(E_1067, F_1071) | ~m1_subset_1(F_1071, k1_zfmisc_1(k2_zfmisc_1(C_1072, D_1068))) | ~v1_funct_1(F_1071) | ~m1_subset_1(E_1067, k1_zfmisc_1(k2_zfmisc_1(A_1070, B_1069))) | ~v1_funct_1(E_1067))), inference(cnfTransformation, [status(thm)], [f_143])).
% 12.84/5.38  tff(c_27861, plain, (![A_1070, B_1069, E_1067]: (k1_partfun1(A_1070, B_1069, '#skF_2', '#skF_3', E_1067, '#skF_5')=k5_relat_1(E_1067, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_1067, k1_zfmisc_1(k2_zfmisc_1(A_1070, B_1069))) | ~v1_funct_1(E_1067))), inference(resolution, [status(thm)], [c_62, c_27857])).
% 12.84/5.38  tff(c_28084, plain, (![A_1083, B_1084, E_1085]: (k1_partfun1(A_1083, B_1084, '#skF_2', '#skF_3', E_1085, '#skF_5')=k5_relat_1(E_1085, '#skF_5') | ~m1_subset_1(E_1085, k1_zfmisc_1(k2_zfmisc_1(A_1083, B_1084))) | ~v1_funct_1(E_1085))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_27861])).
% 12.84/5.38  tff(c_28090, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_28084])).
% 12.84/5.38  tff(c_28097, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_28090])).
% 12.84/5.38  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.84/5.38  tff(c_28102, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28097, c_60])).
% 12.84/5.38  tff(c_48, plain, (![F_41, D_39, A_36, E_40, C_38, B_37]: (m1_subset_1(k1_partfun1(A_36, B_37, C_38, D_39, E_40, F_41), k1_zfmisc_1(k2_zfmisc_1(A_36, D_39))) | ~m1_subset_1(F_41, k1_zfmisc_1(k2_zfmisc_1(C_38, D_39))) | ~v1_funct_1(F_41) | ~m1_subset_1(E_40, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))) | ~v1_funct_1(E_40))), inference(cnfTransformation, [status(thm)], [f_133])).
% 12.84/5.38  tff(c_28106, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_28097, c_48])).
% 12.84/5.38  tff(c_28110, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_28106])).
% 12.84/5.38  tff(c_34, plain, (![A_30, B_31, C_32]: (k2_relset_1(A_30, B_31, C_32)=k2_relat_1(C_32) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.84/5.38  tff(c_28137, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_28110, c_34])).
% 12.84/5.38  tff(c_28172, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28102, c_28137])).
% 12.84/5.38  tff(c_9113, plain, (![A_447, B_448, C_449]: (k2_relset_1(A_447, B_448, C_449)=k2_relat_1(C_449) | ~m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1(A_447, B_448))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 12.84/5.38  tff(c_9120, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_9113])).
% 12.84/5.38  tff(c_54, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.84/5.38  tff(c_9122, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9120, c_54])).
% 12.84/5.38  tff(c_82, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 12.84/5.38  tff(c_89, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_68, c_82])).
% 12.84/5.38  tff(c_100, plain, (![C_58, B_59, A_60]: (v5_relat_1(C_58, B_59) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_60, B_59))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.84/5.38  tff(c_107, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_100])).
% 12.84/5.38  tff(c_10, plain, (![B_4, A_3]: (r1_tarski(k2_relat_1(B_4), A_3) | ~v5_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.84/5.38  tff(c_217, plain, (![A_72, B_73]: (k8_relat_1(A_72, B_73)=B_73 | ~r1_tarski(k2_relat_1(B_73), A_72) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.84/5.38  tff(c_8733, plain, (![A_427, B_428]: (k8_relat_1(A_427, B_428)=B_428 | ~v5_relat_1(B_428, A_427) | ~v1_relat_1(B_428))), inference(resolution, [status(thm)], [c_10, c_217])).
% 12.84/5.38  tff(c_8748, plain, (k8_relat_1('#skF_2', '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_107, c_8733])).
% 12.84/5.38  tff(c_8761, plain, (k8_relat_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_89, c_8748])).
% 12.84/5.38  tff(c_90, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_82])).
% 12.84/5.38  tff(c_58, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.84/5.38  tff(c_56, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.84/5.38  tff(c_64, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 12.84/5.38  tff(c_9096, plain, (![A_444, B_445, C_446]: (k1_relset_1(A_444, B_445, C_446)=k1_relat_1(C_446) | ~m1_subset_1(C_446, k1_zfmisc_1(k2_zfmisc_1(A_444, B_445))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 12.84/5.38  tff(c_9104, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_9096])).
% 12.84/5.38  tff(c_22114, plain, (![B_890, A_891, C_892]: (k1_xboole_0=B_890 | k1_relset_1(A_891, B_890, C_892)=A_891 | ~v1_funct_2(C_892, A_891, B_890) | ~m1_subset_1(C_892, k1_zfmisc_1(k2_zfmisc_1(A_891, B_890))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 12.84/5.38  tff(c_22120, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_22114])).
% 12.84/5.38  tff(c_22126, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_9104, c_22120])).
% 12.84/5.38  tff(c_22127, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_56, c_22126])).
% 12.84/5.38  tff(c_25703, plain, (![A_998, B_999]: (r1_tarski(k1_relat_1(A_998), k2_relat_1(B_999)) | ~v2_funct_1(A_998) | k2_relat_1(k5_relat_1(B_999, A_998))!=k2_relat_1(A_998) | ~v1_funct_1(B_999) | ~v1_relat_1(B_999) | ~v1_funct_1(A_998) | ~v1_relat_1(A_998))), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.84/5.38  tff(c_25721, plain, (![B_999]: (r1_tarski('#skF_2', k2_relat_1(B_999)) | ~v2_funct_1('#skF_5') | k2_relat_1(k5_relat_1(B_999, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_999) | ~v1_relat_1(B_999) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_22127, c_25703])).
% 12.84/5.38  tff(c_25840, plain, (![B_1000]: (r1_tarski('#skF_2', k2_relat_1(B_1000)) | k2_relat_1(k5_relat_1(B_1000, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_1000) | ~v1_relat_1(B_1000))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_66, c_58, c_25721])).
% 12.84/5.38  tff(c_12, plain, (![A_5, B_6]: (k2_relat_1(k8_relat_1(A_5, B_6))=A_5 | ~r1_tarski(A_5, k2_relat_1(B_6)) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.84/5.38  tff(c_27525, plain, (![B_1056]: (k2_relat_1(k8_relat_1('#skF_2', B_1056))='#skF_2' | k2_relat_1(k5_relat_1(B_1056, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_1056) | ~v1_relat_1(B_1056))), inference(resolution, [status(thm)], [c_25840, c_12])).
% 12.84/5.38  tff(c_27582, plain, (k2_relat_1('#skF_4')='#skF_2' | k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8761, c_27525])).
% 12.84/5.38  tff(c_27588, plain, (k2_relat_1('#skF_4')='#skF_2' | k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_72, c_27582])).
% 12.84/5.38  tff(c_27589, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))!=k2_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_9122, c_27588])).
% 12.84/5.38  tff(c_28199, plain, (k2_relat_1('#skF_5')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28172, c_27589])).
% 12.84/5.38  tff(c_108, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_100])).
% 12.84/5.38  tff(c_8982, plain, (![B_438, A_439]: (k9_relat_1(B_438, k2_relat_1(A_439))=k2_relat_1(k5_relat_1(A_439, B_438)) | ~v1_relat_1(B_438) | ~v1_relat_1(A_439))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.84/5.38  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.84/5.38  tff(c_91, plain, (![C_55, A_56, B_57]: (v4_relat_1(C_55, A_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 12.84/5.38  tff(c_99, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_91])).
% 12.84/5.38  tff(c_113, plain, (![B_61, A_62]: (k7_relat_1(B_61, A_62)=B_61 | ~v4_relat_1(B_61, A_62) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_70])).
% 12.84/5.38  tff(c_116, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_99, c_113])).
% 12.84/5.38  tff(c_122, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_116])).
% 12.84/5.38  tff(c_134, plain, (![B_63, A_64]: (k2_relat_1(k7_relat_1(B_63, A_64))=k9_relat_1(B_63, A_64) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.84/5.38  tff(c_146, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_122, c_134])).
% 12.84/5.38  tff(c_152, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_146])).
% 12.84/5.38  tff(c_314, plain, (![A_79, B_80, C_81]: (k1_relset_1(A_79, B_80, C_81)=k1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 12.84/5.38  tff(c_322, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_314])).
% 12.84/5.38  tff(c_702, plain, (![B_112, A_113, C_114]: (k1_xboole_0=B_112 | k1_relset_1(A_113, B_112, C_114)=A_113 | ~v1_funct_2(C_114, A_113, B_112) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 12.84/5.38  tff(c_708, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_702])).
% 12.84/5.38  tff(c_714, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_322, c_708])).
% 12.84/5.38  tff(c_715, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_56, c_714])).
% 12.84/5.38  tff(c_185, plain, (![B_70, A_71]: (r1_tarski(k9_relat_1(B_70, A_71), k9_relat_1(B_70, k1_relat_1(B_70))) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.84/5.38  tff(c_190, plain, (r1_tarski(k2_relat_1('#skF_5'), k9_relat_1('#skF_5', k1_relat_1('#skF_5'))) | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_152, c_185])).
% 12.84/5.38  tff(c_196, plain, (r1_tarski(k2_relat_1('#skF_5'), k9_relat_1('#skF_5', k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_190])).
% 12.84/5.38  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.84/5.38  tff(c_207, plain, (k9_relat_1('#skF_5', k1_relat_1('#skF_5'))=k2_relat_1('#skF_5') | ~r1_tarski(k9_relat_1('#skF_5', k1_relat_1('#skF_5')), k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_196, c_2])).
% 12.84/5.38  tff(c_262, plain, (~r1_tarski(k9_relat_1('#skF_5', k1_relat_1('#skF_5')), k2_relat_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_207])).
% 12.84/5.38  tff(c_717, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_715, c_262])).
% 12.84/5.38  tff(c_723, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_152, c_717])).
% 12.84/5.38  tff(c_724, plain, (k9_relat_1('#skF_5', k1_relat_1('#skF_5'))=k2_relat_1('#skF_5')), inference(splitRight, [status(thm)], [c_207])).
% 12.84/5.38  tff(c_16, plain, (![B_10, A_9]: (r1_tarski(k9_relat_1(B_10, A_9), k9_relat_1(B_10, k1_relat_1(B_10))) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 12.84/5.38  tff(c_736, plain, (![A_9]: (r1_tarski(k9_relat_1('#skF_5', A_9), k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_724, c_16])).
% 12.84/5.38  tff(c_742, plain, (![A_9]: (r1_tarski(k9_relat_1('#skF_5', A_9), k2_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_736])).
% 12.84/5.38  tff(c_9013, plain, (![A_439]: (r1_tarski(k2_relat_1(k5_relat_1(A_439, '#skF_5')), k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_439))), inference(superposition, [status(thm), theory('equality')], [c_8982, c_742])).
% 12.84/5.38  tff(c_9050, plain, (![A_439]: (r1_tarski(k2_relat_1(k5_relat_1(A_439, '#skF_5')), k2_relat_1('#skF_5')) | ~v1_relat_1(A_439))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_9013])).
% 12.84/5.38  tff(c_174, plain, (![B_68, A_69]: (r1_tarski(k2_relat_1(B_68), A_69) | ~v5_relat_1(B_68, A_69) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.84/5.38  tff(c_9132, plain, (![B_452, A_453]: (k2_relat_1(B_452)=A_453 | ~r1_tarski(A_453, k2_relat_1(B_452)) | ~v5_relat_1(B_452, A_453) | ~v1_relat_1(B_452))), inference(resolution, [status(thm)], [c_174, c_2])).
% 12.84/5.38  tff(c_9138, plain, (![A_439]: (k2_relat_1(k5_relat_1(A_439, '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_439, '#skF_5'))) | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_439))), inference(resolution, [status(thm)], [c_9050, c_9132])).
% 12.84/5.38  tff(c_9170, plain, (![A_439]: (k2_relat_1(k5_relat_1(A_439, '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_439, '#skF_5'))) | ~v1_relat_1(A_439))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_9138])).
% 12.84/5.38  tff(c_28218, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_28172, c_9170])).
% 12.84/5.38  tff(c_28280, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_89, c_108, c_28172, c_28218])).
% 12.84/5.38  tff(c_28314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28199, c_28280])).
% 12.84/5.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.84/5.38  
% 12.84/5.38  Inference rules
% 12.84/5.38  ----------------------
% 12.84/5.38  #Ref     : 0
% 12.84/5.38  #Sup     : 6327
% 12.84/5.38  #Fact    : 0
% 12.84/5.38  #Define  : 0
% 12.84/5.38  #Split   : 56
% 12.84/5.38  #Chain   : 0
% 12.84/5.38  #Close   : 0
% 12.84/5.38  
% 12.84/5.38  Ordering : KBO
% 12.84/5.38  
% 12.84/5.38  Simplification rules
% 12.84/5.38  ----------------------
% 12.84/5.38  #Subsume      : 477
% 12.84/5.38  #Demod        : 7470
% 12.84/5.38  #Tautology    : 2340
% 12.84/5.38  #SimpNegUnit  : 111
% 12.84/5.38  #BackRed      : 619
% 12.84/5.38  
% 12.84/5.38  #Partial instantiations: 0
% 12.84/5.38  #Strategies tried      : 1
% 12.84/5.38  
% 12.84/5.38  Timing (in seconds)
% 12.84/5.38  ----------------------
% 12.84/5.38  Preprocessing        : 0.37
% 12.84/5.38  Parsing              : 0.20
% 12.84/5.38  CNF conversion       : 0.03
% 12.84/5.38  Main loop            : 4.22
% 12.84/5.38  Inferencing          : 1.17
% 12.84/5.38  Reduction            : 1.75
% 12.84/5.38  Demodulation         : 1.31
% 12.84/5.38  BG Simplification    : 0.13
% 12.84/5.38  Subsumption          : 0.85
% 12.84/5.38  Abstraction          : 0.18
% 12.84/5.38  MUC search           : 0.00
% 12.84/5.38  Cooper               : 0.00
% 12.84/5.38  Total                : 4.64
% 12.84/5.38  Index Insertion      : 0.00
% 12.84/5.38  Index Deletion       : 0.00
% 12.84/5.38  Index Matching       : 0.00
% 12.84/5.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
