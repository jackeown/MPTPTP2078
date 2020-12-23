%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:50 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 143 expanded)
%              Number of leaves         :   37 (  64 expanded)
%              Depth                    :    9
%              Number of atoms          :  121 ( 235 expanded)
%              Number of equality atoms :   26 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r2_relset_1(A,B,k4_relset_1(A,A,A,B,k6_partfun1(A),C),C)
          & r2_relset_1(A,B,k4_relset_1(A,B,B,B,C,k6_partfun1(B)),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_90,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_78,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_51,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_57,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_51])).

tff(c_63,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_57])).

tff(c_416,plain,(
    ! [A_114,B_115,C_116,D_117] :
      ( r2_relset_1(A_114,B_115,C_116,C_116)
      | ~ m1_subset_1(D_117,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115)))
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_428,plain,(
    ! [C_121] :
      ( r2_relset_1('#skF_1','#skF_2',C_121,C_121)
      | ~ m1_subset_1(C_121,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_36,c_416])).

tff(c_431,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_428])).

tff(c_272,plain,(
    ! [C_88,B_89,A_90] :
      ( v5_relat_1(C_88,B_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_90,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_280,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_272])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_344,plain,(
    ! [A_106,B_107] :
      ( k8_relat_1(A_106,B_107) = B_107
      | ~ r1_tarski(k2_relat_1(B_107),A_106)
      | ~ v1_relat_1(B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_349,plain,(
    ! [A_108,B_109] :
      ( k8_relat_1(A_108,B_109) = B_109
      | ~ v5_relat_1(B_109,A_108)
      | ~ v1_relat_1(B_109) ) ),
    inference(resolution,[status(thm)],[c_6,c_344])).

tff(c_355,plain,
    ( k8_relat_1('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_280,c_349])).

tff(c_361,plain,(
    k8_relat_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_355])).

tff(c_32,plain,(
    ! [A_32] : k6_relat_1(A_32) = k6_partfun1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k5_relat_1(B_9,k6_relat_1(A_8)) = k8_relat_1(A_8,B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_38,plain,(
    ! [B_9,A_8] :
      ( k5_relat_1(B_9,k6_partfun1(A_8)) = k8_relat_1(A_8,B_9)
      | ~ v1_relat_1(B_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_10])).

tff(c_30,plain,(
    ! [A_31] : m1_subset_1(k6_partfun1(A_31),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_451,plain,(
    ! [A_124,C_126,F_127,D_125,E_129,B_128] :
      ( k4_relset_1(A_124,B_128,C_126,D_125,E_129,F_127) = k5_relat_1(E_129,F_127)
      | ~ m1_subset_1(F_127,k1_zfmisc_1(k2_zfmisc_1(C_126,D_125)))
      | ~ m1_subset_1(E_129,k1_zfmisc_1(k2_zfmisc_1(A_124,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_482,plain,(
    ! [A_134,B_135,A_136,E_137] :
      ( k4_relset_1(A_134,B_135,A_136,A_136,E_137,k6_partfun1(A_136)) = k5_relat_1(E_137,k6_partfun1(A_136))
      | ~ m1_subset_1(E_137,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(resolution,[status(thm)],[c_30,c_451])).

tff(c_488,plain,(
    ! [A_136] : k4_relset_1('#skF_1','#skF_2',A_136,A_136,'#skF_3',k6_partfun1(A_136)) = k5_relat_1('#skF_3',k6_partfun1(A_136)) ),
    inference(resolution,[status(thm)],[c_36,c_482])).

tff(c_170,plain,(
    ! [A_66,B_67,C_68,D_69] :
      ( r2_relset_1(A_66,B_67,C_68,C_68)
      | ~ m1_subset_1(D_69,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67)))
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_218,plain,(
    ! [C_73] :
      ( r2_relset_1('#skF_1','#skF_2',C_73,C_73)
      | ~ m1_subset_1(C_73,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_36,c_170])).

tff(c_221,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_218])).

tff(c_87,plain,(
    ! [C_51,A_52,B_53] :
      ( v4_relat_1(C_51,A_52)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_95,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_87])).

tff(c_97,plain,(
    ! [B_55,A_56] :
      ( k7_relat_1(B_55,A_56) = B_55
      | ~ v4_relat_1(B_55,A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_103,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_95,c_97])).

tff(c_109,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_103])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_17,A_16)),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_113,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_18])).

tff(c_117,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_113])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( k5_relat_1(k6_relat_1(A_14),B_15) = B_15
      | ~ r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_177,plain,(
    ! [A_70,B_71] :
      ( k5_relat_1(k6_partfun1(A_70),B_71) = B_71
      | ~ r1_tarski(k1_relat_1(B_71),A_70)
      | ~ v1_relat_1(B_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_16])).

tff(c_183,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_117,c_177])).

tff(c_192,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_183])).

tff(c_222,plain,(
    ! [A_74,B_78,C_76,D_75,E_79,F_77] :
      ( k4_relset_1(A_74,B_78,C_76,D_75,E_79,F_77) = k5_relat_1(E_79,F_77)
      | ~ m1_subset_1(F_77,k1_zfmisc_1(k2_zfmisc_1(C_76,D_75)))
      | ~ m1_subset_1(E_79,k1_zfmisc_1(k2_zfmisc_1(A_74,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_253,plain,(
    ! [A_85,B_86,E_87] :
      ( k4_relset_1(A_85,B_86,'#skF_1','#skF_2',E_87,'#skF_3') = k5_relat_1(E_87,'#skF_3')
      | ~ m1_subset_1(E_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(resolution,[status(thm)],[c_36,c_222])).

tff(c_260,plain,(
    ! [A_31] : k4_relset_1(A_31,A_31,'#skF_1','#skF_2',k6_partfun1(A_31),'#skF_3') = k5_relat_1(k6_partfun1(A_31),'#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_253])).

tff(c_34,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3')
    | ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_66,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_2',k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_266,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1(k6_partfun1('#skF_1'),'#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_66])).

tff(c_269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_192,c_266])).

tff(c_270,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_2','#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_489,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k5_relat_1('#skF_3',k6_partfun1('#skF_2')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_270])).

tff(c_501,plain,
    ( ~ r2_relset_1('#skF_1','#skF_2',k8_relat_1('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_489])).

tff(c_504,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_431,c_361,c_501])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:36:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.61  
% 2.56/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.56/1.61  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.56/1.61  
% 2.56/1.61  %Foreground sorts:
% 2.56/1.61  
% 2.56/1.61  
% 2.56/1.61  %Background operators:
% 2.56/1.61  
% 2.56/1.61  
% 2.56/1.61  %Foreground operators:
% 2.56/1.61  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.56/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.61  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.56/1.61  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.56/1.61  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.56/1.61  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.56/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.56/1.61  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.56/1.61  tff('#skF_2', type, '#skF_2': $i).
% 2.56/1.61  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 2.56/1.61  tff('#skF_3', type, '#skF_3': $i).
% 2.56/1.61  tff('#skF_1', type, '#skF_1': $i).
% 2.56/1.61  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.56/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.56/1.61  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.56/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.56/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.56/1.61  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.56/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.61  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.56/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.56/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.56/1.61  
% 2.86/1.63  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.86/1.63  tff(f_97, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r2_relset_1(A, B, k4_relset_1(A, A, A, B, k6_partfun1(A), C), C) & r2_relset_1(A, B, k4_relset_1(A, B, B, B, C, k6_partfun1(B)), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_2)).
% 2.86/1.63  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.86/1.63  tff(f_84, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.86/1.63  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.86/1.63  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.86/1.63  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.86/1.63  tff(f_90, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.86/1.63  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 2.86/1.63  tff(f_88, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 2.86/1.63  tff(f_78, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.86/1.63  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.86/1.63  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.86/1.63  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 2.86/1.63  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.86/1.63  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.86/1.63  tff(c_51, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.86/1.63  tff(c_57, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_51])).
% 2.86/1.63  tff(c_63, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_57])).
% 2.86/1.63  tff(c_416, plain, (![A_114, B_115, C_116, D_117]: (r2_relset_1(A_114, B_115, C_116, C_116) | ~m1_subset_1(D_117, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.86/1.63  tff(c_428, plain, (![C_121]: (r2_relset_1('#skF_1', '#skF_2', C_121, C_121) | ~m1_subset_1(C_121, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_36, c_416])).
% 2.86/1.63  tff(c_431, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_428])).
% 2.86/1.63  tff(c_272, plain, (![C_88, B_89, A_90]: (v5_relat_1(C_88, B_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_90, B_89))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.86/1.63  tff(c_280, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_272])).
% 2.86/1.63  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.86/1.63  tff(c_344, plain, (![A_106, B_107]: (k8_relat_1(A_106, B_107)=B_107 | ~r1_tarski(k2_relat_1(B_107), A_106) | ~v1_relat_1(B_107))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.86/1.63  tff(c_349, plain, (![A_108, B_109]: (k8_relat_1(A_108, B_109)=B_109 | ~v5_relat_1(B_109, A_108) | ~v1_relat_1(B_109))), inference(resolution, [status(thm)], [c_6, c_344])).
% 2.86/1.63  tff(c_355, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_280, c_349])).
% 2.86/1.63  tff(c_361, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_355])).
% 2.86/1.63  tff(c_32, plain, (![A_32]: (k6_relat_1(A_32)=k6_partfun1(A_32))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.86/1.63  tff(c_10, plain, (![B_9, A_8]: (k5_relat_1(B_9, k6_relat_1(A_8))=k8_relat_1(A_8, B_9) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.86/1.63  tff(c_38, plain, (![B_9, A_8]: (k5_relat_1(B_9, k6_partfun1(A_8))=k8_relat_1(A_8, B_9) | ~v1_relat_1(B_9))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_10])).
% 2.86/1.63  tff(c_30, plain, (![A_31]: (m1_subset_1(k6_partfun1(A_31), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.86/1.63  tff(c_451, plain, (![A_124, C_126, F_127, D_125, E_129, B_128]: (k4_relset_1(A_124, B_128, C_126, D_125, E_129, F_127)=k5_relat_1(E_129, F_127) | ~m1_subset_1(F_127, k1_zfmisc_1(k2_zfmisc_1(C_126, D_125))) | ~m1_subset_1(E_129, k1_zfmisc_1(k2_zfmisc_1(A_124, B_128))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.86/1.63  tff(c_482, plain, (![A_134, B_135, A_136, E_137]: (k4_relset_1(A_134, B_135, A_136, A_136, E_137, k6_partfun1(A_136))=k5_relat_1(E_137, k6_partfun1(A_136)) | ~m1_subset_1(E_137, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(resolution, [status(thm)], [c_30, c_451])).
% 2.86/1.63  tff(c_488, plain, (![A_136]: (k4_relset_1('#skF_1', '#skF_2', A_136, A_136, '#skF_3', k6_partfun1(A_136))=k5_relat_1('#skF_3', k6_partfun1(A_136)))), inference(resolution, [status(thm)], [c_36, c_482])).
% 2.86/1.63  tff(c_170, plain, (![A_66, B_67, C_68, D_69]: (r2_relset_1(A_66, B_67, C_68, C_68) | ~m1_subset_1(D_69, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.86/1.63  tff(c_218, plain, (![C_73]: (r2_relset_1('#skF_1', '#skF_2', C_73, C_73) | ~m1_subset_1(C_73, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_36, c_170])).
% 2.86/1.63  tff(c_221, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_218])).
% 2.86/1.63  tff(c_87, plain, (![C_51, A_52, B_53]: (v4_relat_1(C_51, A_52) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.86/1.63  tff(c_95, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_87])).
% 2.86/1.63  tff(c_97, plain, (![B_55, A_56]: (k7_relat_1(B_55, A_56)=B_55 | ~v4_relat_1(B_55, A_56) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.86/1.63  tff(c_103, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_95, c_97])).
% 2.86/1.63  tff(c_109, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_103])).
% 2.86/1.63  tff(c_18, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(k7_relat_1(B_17, A_16)), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.86/1.63  tff(c_113, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_109, c_18])).
% 2.86/1.63  tff(c_117, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_113])).
% 2.86/1.63  tff(c_16, plain, (![A_14, B_15]: (k5_relat_1(k6_relat_1(A_14), B_15)=B_15 | ~r1_tarski(k1_relat_1(B_15), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.86/1.63  tff(c_177, plain, (![A_70, B_71]: (k5_relat_1(k6_partfun1(A_70), B_71)=B_71 | ~r1_tarski(k1_relat_1(B_71), A_70) | ~v1_relat_1(B_71))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_16])).
% 2.86/1.63  tff(c_183, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_117, c_177])).
% 2.86/1.63  tff(c_192, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_183])).
% 2.86/1.63  tff(c_222, plain, (![A_74, B_78, C_76, D_75, E_79, F_77]: (k4_relset_1(A_74, B_78, C_76, D_75, E_79, F_77)=k5_relat_1(E_79, F_77) | ~m1_subset_1(F_77, k1_zfmisc_1(k2_zfmisc_1(C_76, D_75))) | ~m1_subset_1(E_79, k1_zfmisc_1(k2_zfmisc_1(A_74, B_78))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.86/1.63  tff(c_253, plain, (![A_85, B_86, E_87]: (k4_relset_1(A_85, B_86, '#skF_1', '#skF_2', E_87, '#skF_3')=k5_relat_1(E_87, '#skF_3') | ~m1_subset_1(E_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(resolution, [status(thm)], [c_36, c_222])).
% 2.86/1.63  tff(c_260, plain, (![A_31]: (k4_relset_1(A_31, A_31, '#skF_1', '#skF_2', k6_partfun1(A_31), '#skF_3')=k5_relat_1(k6_partfun1(A_31), '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_253])).
% 2.86/1.63  tff(c_34, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3') | ~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.86/1.63  tff(c_66, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_2', k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_34])).
% 2.86/1.63  tff(c_266, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_260, c_66])).
% 2.86/1.63  tff(c_269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_221, c_192, c_266])).
% 2.86/1.63  tff(c_270, plain, (~r2_relset_1('#skF_1', '#skF_2', k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_2', '#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 2.86/1.63  tff(c_489, plain, (~r2_relset_1('#skF_1', '#skF_2', k5_relat_1('#skF_3', k6_partfun1('#skF_2')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_488, c_270])).
% 2.86/1.63  tff(c_501, plain, (~r2_relset_1('#skF_1', '#skF_2', k8_relat_1('#skF_2', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_38, c_489])).
% 2.86/1.63  tff(c_504, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_431, c_361, c_501])).
% 2.86/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.63  
% 2.86/1.63  Inference rules
% 2.86/1.63  ----------------------
% 2.86/1.63  #Ref     : 0
% 2.86/1.63  #Sup     : 101
% 2.86/1.63  #Fact    : 0
% 2.86/1.63  #Define  : 0
% 2.86/1.63  #Split   : 1
% 2.86/1.63  #Chain   : 0
% 2.86/1.63  #Close   : 0
% 2.86/1.63  
% 2.86/1.63  Ordering : KBO
% 2.86/1.63  
% 2.86/1.63  Simplification rules
% 2.86/1.63  ----------------------
% 2.86/1.63  #Subsume      : 0
% 2.86/1.63  #Demod        : 58
% 2.86/1.63  #Tautology    : 53
% 2.86/1.63  #SimpNegUnit  : 0
% 2.86/1.63  #BackRed      : 3
% 2.86/1.63  
% 2.86/1.63  #Partial instantiations: 0
% 2.86/1.63  #Strategies tried      : 1
% 2.86/1.63  
% 2.86/1.63  Timing (in seconds)
% 2.86/1.63  ----------------------
% 2.86/1.63  Preprocessing        : 0.47
% 2.86/1.63  Parsing              : 0.25
% 2.86/1.63  CNF conversion       : 0.03
% 2.86/1.63  Main loop            : 0.27
% 2.86/1.63  Inferencing          : 0.11
% 2.86/1.63  Reduction            : 0.08
% 2.86/1.63  Demodulation         : 0.06
% 2.86/1.63  BG Simplification    : 0.02
% 2.86/1.63  Subsumption          : 0.03
% 2.86/1.63  Abstraction          : 0.02
% 2.86/1.63  MUC search           : 0.00
% 2.86/1.63  Cooper               : 0.00
% 2.86/1.63  Total                : 0.78
% 2.86/1.63  Index Insertion      : 0.00
% 2.86/1.63  Index Deletion       : 0.00
% 2.86/1.63  Index Matching       : 0.00
% 2.86/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
