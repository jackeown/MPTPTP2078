%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:15 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 133 expanded)
%              Number of leaves         :   44 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :  112 ( 190 expanded)
%              Number of equality atoms :   22 (  36 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(C),D)
         => ( r1_tarski(C,k1_relset_1(A,B,D))
            & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_76,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k1_relat_1(A),k1_relat_1(B)),k1_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k6_subset_1(k2_relat_1(A),k2_relat_1(B)),k2_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1328,plain,(
    ! [A_180,B_181,C_182] :
      ( k2_relset_1(A_180,B_181,C_182) = k2_relat_1(C_182)
      | ~ m1_subset_1(C_182,k1_zfmisc_1(k2_zfmisc_1(A_180,B_181))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1332,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_1328])).

tff(c_522,plain,(
    ! [A_111,B_112,C_113] :
      ( k1_relset_1(A_111,B_112,C_113) = k1_relat_1(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_526,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_522])).

tff(c_44,plain,
    ( ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_135,plain,(
    ~ r1_tarski('#skF_3',k1_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_540,plain,(
    ~ r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_135])).

tff(c_4,plain,(
    ! [A_2] : k2_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [A_28] : v1_relat_1(k6_relat_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_123,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_127,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_123])).

tff(c_30,plain,(
    ! [A_27] : k1_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_46,plain,(
    r1_tarski(k6_relat_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_128,plain,(
    ! [A_59,C_60,B_61] :
      ( r1_tarski(A_59,C_60)
      | ~ r1_tarski(B_61,C_60)
      | ~ r1_tarski(A_59,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_136,plain,(
    ! [A_62] :
      ( r1_tarski(A_62,'#skF_4')
      | ~ r1_tarski(A_62,k6_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_46,c_128])).

tff(c_141,plain,(
    ! [B_7] : r1_tarski(k4_xboole_0(k6_relat_1('#skF_3'),B_7),'#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_136])).

tff(c_14,plain,(
    ! [A_13,B_14] : r1_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_118,plain,(
    ! [B_54,A_55] :
      ( ~ r1_xboole_0(B_54,A_55)
      | ~ r1_tarski(B_54,A_55)
      | v1_xboole_0(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_398,plain,(
    ! [A_107,B_108] :
      ( ~ r1_tarski(k4_xboole_0(A_107,B_108),B_108)
      | v1_xboole_0(k4_xboole_0(A_107,B_108)) ) ),
    inference(resolution,[status(thm)],[c_14,c_118])).

tff(c_442,plain,(
    v1_xboole_0(k4_xboole_0(k6_relat_1('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_141,c_398])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_608,plain,(
    k4_xboole_0(k6_relat_1('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_442,c_2])).

tff(c_20,plain,(
    ! [A_19,B_20] : k6_subset_1(A_19,B_20) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    ! [A_21,B_23] :
      ( r1_tarski(k6_subset_1(k1_relat_1(A_21),k1_relat_1(B_23)),k1_relat_1(k6_subset_1(A_21,B_23)))
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_959,plain,(
    ! [A_132,B_133] :
      ( r1_tarski(k4_xboole_0(k1_relat_1(A_132),k1_relat_1(B_133)),k1_relat_1(k4_xboole_0(A_132,B_133)))
      | ~ v1_relat_1(B_133)
      | ~ v1_relat_1(A_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_22])).

tff(c_973,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(k6_relat_1('#skF_3')),k1_relat_1('#skF_4')),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k6_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_959])).

tff(c_1001,plain,(
    r1_tarski(k4_xboole_0('#skF_3',k1_relat_1('#skF_4')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_127,c_30,c_28,c_973])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_tarski(A_8,k2_xboole_0(B_9,C_10))
      | ~ r1_tarski(k4_xboole_0(A_8,B_9),C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1018,plain,(
    r1_tarski('#skF_3',k2_xboole_0(k1_relat_1('#skF_4'),k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_1001,c_10])).

tff(c_1023,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1018])).

tff(c_1025,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_540,c_1023])).

tff(c_1026,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1413,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1332,c_1026])).

tff(c_26,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    ! [A_27] : k2_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1031,plain,(
    ! [A_134] :
      ( r1_tarski(A_134,'#skF_4')
      | ~ r1_tarski(A_134,k6_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_46,c_128])).

tff(c_1036,plain,(
    ! [B_7] : r1_tarski(k4_xboole_0(k6_relat_1('#skF_3'),B_7),'#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_1031])).

tff(c_1277,plain,(
    ! [A_178,B_179] :
      ( ~ r1_tarski(k4_xboole_0(A_178,B_179),B_179)
      | v1_xboole_0(k4_xboole_0(A_178,B_179)) ) ),
    inference(resolution,[status(thm)],[c_14,c_118])).

tff(c_1326,plain,(
    v1_xboole_0(k4_xboole_0(k6_relat_1('#skF_3'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_1036,c_1277])).

tff(c_1527,plain,(
    k4_xboole_0(k6_relat_1('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1326,c_2])).

tff(c_24,plain,(
    ! [A_24,B_26] :
      ( r1_tarski(k6_subset_1(k2_relat_1(A_24),k2_relat_1(B_26)),k2_relat_1(k6_subset_1(A_24,B_26)))
      | ~ v1_relat_1(B_26)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1738,plain,(
    ! [A_200,B_201] :
      ( r1_tarski(k4_xboole_0(k2_relat_1(A_200),k2_relat_1(B_201)),k2_relat_1(k4_xboole_0(A_200,B_201)))
      | ~ v1_relat_1(B_201)
      | ~ v1_relat_1(A_200) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_24])).

tff(c_1749,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1(k6_relat_1('#skF_3')),k2_relat_1('#skF_4')),k2_relat_1(k1_xboole_0))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k6_relat_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1527,c_1738])).

tff(c_1776,plain,(
    r1_tarski(k4_xboole_0('#skF_3',k2_relat_1('#skF_4')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_127,c_26,c_32,c_1749])).

tff(c_1917,plain,(
    r1_tarski('#skF_3',k2_xboole_0(k2_relat_1('#skF_4'),k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_1776,c_10])).

tff(c_1922,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1917])).

tff(c_1924,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1413,c_1922])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:32:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.28/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.57  
% 3.28/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.57  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k6_subset_1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k3_tarski > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.28/1.57  
% 3.28/1.57  %Foreground sorts:
% 3.28/1.57  
% 3.28/1.57  
% 3.28/1.57  %Background operators:
% 3.28/1.57  
% 3.28/1.57  
% 3.28/1.57  %Foreground operators:
% 3.28/1.57  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.28/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.28/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.28/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.57  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.28/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.28/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.28/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.28/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.28/1.57  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.28/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.28/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.28/1.57  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.28/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.28/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.57  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.28/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.28/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.28/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.28/1.57  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.28/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.28/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.28/1.57  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.28/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.28/1.57  
% 3.28/1.59  tff(f_105, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relset_1)).
% 3.28/1.59  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.28/1.59  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.28/1.59  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.28/1.59  tff(f_84, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.28/1.59  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.28/1.59  tff(f_80, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.28/1.59  tff(f_76, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.28/1.59  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.28/1.59  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.28/1.59  tff(f_53, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.28/1.59  tff(f_51, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.28/1.59  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.28/1.59  tff(f_59, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.28/1.59  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k1_relat_1(A), k1_relat_1(B)), k1_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_relat_1)).
% 3.28/1.59  tff(f_43, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 3.28/1.59  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k2_relat_1(A), k2_relat_1(B)), k2_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_relat_1)).
% 3.28/1.59  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.28/1.59  tff(c_1328, plain, (![A_180, B_181, C_182]: (k2_relset_1(A_180, B_181, C_182)=k2_relat_1(C_182) | ~m1_subset_1(C_182, k1_zfmisc_1(k2_zfmisc_1(A_180, B_181))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.28/1.59  tff(c_1332, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_1328])).
% 3.28/1.59  tff(c_522, plain, (![A_111, B_112, C_113]: (k1_relset_1(A_111, B_112, C_113)=k1_relat_1(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.28/1.59  tff(c_526, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_522])).
% 3.28/1.59  tff(c_44, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4')) | ~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.28/1.59  tff(c_135, plain, (~r1_tarski('#skF_3', k1_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_44])).
% 3.28/1.59  tff(c_540, plain, (~r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_526, c_135])).
% 3.28/1.59  tff(c_4, plain, (![A_2]: (k2_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.28/1.59  tff(c_34, plain, (![A_28]: (v1_relat_1(k6_relat_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.28/1.59  tff(c_123, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.28/1.59  tff(c_127, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_123])).
% 3.28/1.59  tff(c_30, plain, (![A_27]: (k1_relat_1(k6_relat_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.28/1.59  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.28/1.59  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.28/1.59  tff(c_46, plain, (r1_tarski(k6_relat_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.28/1.59  tff(c_128, plain, (![A_59, C_60, B_61]: (r1_tarski(A_59, C_60) | ~r1_tarski(B_61, C_60) | ~r1_tarski(A_59, B_61))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.28/1.59  tff(c_136, plain, (![A_62]: (r1_tarski(A_62, '#skF_4') | ~r1_tarski(A_62, k6_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_46, c_128])).
% 3.28/1.59  tff(c_141, plain, (![B_7]: (r1_tarski(k4_xboole_0(k6_relat_1('#skF_3'), B_7), '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_136])).
% 3.28/1.59  tff(c_14, plain, (![A_13, B_14]: (r1_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.28/1.59  tff(c_118, plain, (![B_54, A_55]: (~r1_xboole_0(B_54, A_55) | ~r1_tarski(B_54, A_55) | v1_xboole_0(B_54))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.28/1.59  tff(c_398, plain, (![A_107, B_108]: (~r1_tarski(k4_xboole_0(A_107, B_108), B_108) | v1_xboole_0(k4_xboole_0(A_107, B_108)))), inference(resolution, [status(thm)], [c_14, c_118])).
% 3.28/1.59  tff(c_442, plain, (v1_xboole_0(k4_xboole_0(k6_relat_1('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_141, c_398])).
% 3.28/1.59  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.28/1.59  tff(c_608, plain, (k4_xboole_0(k6_relat_1('#skF_3'), '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_442, c_2])).
% 3.28/1.59  tff(c_20, plain, (![A_19, B_20]: (k6_subset_1(A_19, B_20)=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.28/1.59  tff(c_22, plain, (![A_21, B_23]: (r1_tarski(k6_subset_1(k1_relat_1(A_21), k1_relat_1(B_23)), k1_relat_1(k6_subset_1(A_21, B_23))) | ~v1_relat_1(B_23) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.28/1.59  tff(c_959, plain, (![A_132, B_133]: (r1_tarski(k4_xboole_0(k1_relat_1(A_132), k1_relat_1(B_133)), k1_relat_1(k4_xboole_0(A_132, B_133))) | ~v1_relat_1(B_133) | ~v1_relat_1(A_132))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_22])).
% 3.28/1.59  tff(c_973, plain, (r1_tarski(k4_xboole_0(k1_relat_1(k6_relat_1('#skF_3')), k1_relat_1('#skF_4')), k1_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_4') | ~v1_relat_1(k6_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_608, c_959])).
% 3.28/1.59  tff(c_1001, plain, (r1_tarski(k4_xboole_0('#skF_3', k1_relat_1('#skF_4')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_127, c_30, c_28, c_973])).
% 3.28/1.59  tff(c_10, plain, (![A_8, B_9, C_10]: (r1_tarski(A_8, k2_xboole_0(B_9, C_10)) | ~r1_tarski(k4_xboole_0(A_8, B_9), C_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.28/1.59  tff(c_1018, plain, (r1_tarski('#skF_3', k2_xboole_0(k1_relat_1('#skF_4'), k1_xboole_0))), inference(resolution, [status(thm)], [c_1001, c_10])).
% 3.28/1.59  tff(c_1023, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1018])).
% 3.28/1.59  tff(c_1025, plain, $false, inference(negUnitSimplification, [status(thm)], [c_540, c_1023])).
% 3.28/1.59  tff(c_1026, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_44])).
% 3.28/1.59  tff(c_1413, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1332, c_1026])).
% 3.28/1.59  tff(c_26, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.28/1.59  tff(c_32, plain, (![A_27]: (k2_relat_1(k6_relat_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.28/1.59  tff(c_1031, plain, (![A_134]: (r1_tarski(A_134, '#skF_4') | ~r1_tarski(A_134, k6_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_46, c_128])).
% 3.28/1.59  tff(c_1036, plain, (![B_7]: (r1_tarski(k4_xboole_0(k6_relat_1('#skF_3'), B_7), '#skF_4'))), inference(resolution, [status(thm)], [c_8, c_1031])).
% 3.28/1.59  tff(c_1277, plain, (![A_178, B_179]: (~r1_tarski(k4_xboole_0(A_178, B_179), B_179) | v1_xboole_0(k4_xboole_0(A_178, B_179)))), inference(resolution, [status(thm)], [c_14, c_118])).
% 3.28/1.59  tff(c_1326, plain, (v1_xboole_0(k4_xboole_0(k6_relat_1('#skF_3'), '#skF_4'))), inference(resolution, [status(thm)], [c_1036, c_1277])).
% 3.28/1.59  tff(c_1527, plain, (k4_xboole_0(k6_relat_1('#skF_3'), '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1326, c_2])).
% 3.28/1.59  tff(c_24, plain, (![A_24, B_26]: (r1_tarski(k6_subset_1(k2_relat_1(A_24), k2_relat_1(B_26)), k2_relat_1(k6_subset_1(A_24, B_26))) | ~v1_relat_1(B_26) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.28/1.59  tff(c_1738, plain, (![A_200, B_201]: (r1_tarski(k4_xboole_0(k2_relat_1(A_200), k2_relat_1(B_201)), k2_relat_1(k4_xboole_0(A_200, B_201))) | ~v1_relat_1(B_201) | ~v1_relat_1(A_200))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_24])).
% 3.28/1.59  tff(c_1749, plain, (r1_tarski(k4_xboole_0(k2_relat_1(k6_relat_1('#skF_3')), k2_relat_1('#skF_4')), k2_relat_1(k1_xboole_0)) | ~v1_relat_1('#skF_4') | ~v1_relat_1(k6_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1527, c_1738])).
% 3.28/1.59  tff(c_1776, plain, (r1_tarski(k4_xboole_0('#skF_3', k2_relat_1('#skF_4')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_127, c_26, c_32, c_1749])).
% 3.28/1.59  tff(c_1917, plain, (r1_tarski('#skF_3', k2_xboole_0(k2_relat_1('#skF_4'), k1_xboole_0))), inference(resolution, [status(thm)], [c_1776, c_10])).
% 3.28/1.59  tff(c_1922, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1917])).
% 3.28/1.59  tff(c_1924, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1413, c_1922])).
% 3.28/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.28/1.59  
% 3.28/1.59  Inference rules
% 3.28/1.59  ----------------------
% 3.28/1.59  #Ref     : 0
% 3.28/1.59  #Sup     : 432
% 3.28/1.59  #Fact    : 0
% 3.28/1.59  #Define  : 0
% 3.28/1.59  #Split   : 1
% 3.28/1.59  #Chain   : 0
% 3.28/1.59  #Close   : 0
% 3.28/1.59  
% 3.28/1.59  Ordering : KBO
% 3.28/1.59  
% 3.28/1.59  Simplification rules
% 3.28/1.59  ----------------------
% 3.28/1.59  #Subsume      : 23
% 3.28/1.59  #Demod        : 341
% 3.28/1.59  #Tautology    : 257
% 3.28/1.59  #SimpNegUnit  : 2
% 3.28/1.59  #BackRed      : 19
% 3.28/1.59  
% 3.28/1.59  #Partial instantiations: 0
% 3.28/1.59  #Strategies tried      : 1
% 3.28/1.59  
% 3.28/1.59  Timing (in seconds)
% 3.28/1.59  ----------------------
% 3.28/1.59  Preprocessing        : 0.32
% 3.28/1.59  Parsing              : 0.18
% 3.28/1.59  CNF conversion       : 0.02
% 3.28/1.59  Main loop            : 0.50
% 3.28/1.59  Inferencing          : 0.17
% 3.28/1.59  Reduction            : 0.18
% 3.28/1.60  Demodulation         : 0.14
% 3.28/1.60  BG Simplification    : 0.02
% 3.28/1.60  Subsumption          : 0.08
% 3.28/1.60  Abstraction          : 0.02
% 3.28/1.60  MUC search           : 0.00
% 3.28/1.60  Cooper               : 0.00
% 3.28/1.60  Total                : 0.86
% 3.28/1.60  Index Insertion      : 0.00
% 3.28/1.60  Index Deletion       : 0.00
% 3.28/1.60  Index Matching       : 0.00
% 3.28/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
