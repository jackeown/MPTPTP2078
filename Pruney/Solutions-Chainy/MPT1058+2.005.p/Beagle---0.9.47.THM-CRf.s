%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:22 EST 2020

% Result     : Theorem 6.50s
% Output     : CNFRefutation 6.50s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 105 expanded)
%              Number of leaves         :   41 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 135 expanded)
%              Number of equality atoms :   45 (  62 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_116,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_92,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_104,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_74,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_102,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_106,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_55,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_56,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_62,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_44,plain,(
    ! [A_54] : v1_relat_1(k6_relat_1(A_54)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_46,plain,(
    ! [A_54] : v1_funct_1(k6_relat_1(A_54)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_52,plain,(
    ! [A_59] : v2_funct_1(k6_relat_1(A_59)) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_36,plain,(
    ! [A_47] : k2_relat_1(k6_relat_1(A_47)) = A_47 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_403,plain,(
    ! [A_108,B_109] :
      ( k5_relat_1(k6_relat_1(A_108),B_109) = k7_relat_1(B_109,A_108)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_50,plain,(
    ! [B_58,A_57] : k5_relat_1(k6_relat_1(B_58),k6_relat_1(A_57)) = k6_relat_1(k3_xboole_0(A_57,B_58)) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_410,plain,(
    ! [A_57,A_108] :
      ( k7_relat_1(k6_relat_1(A_57),A_108) = k6_relat_1(k3_xboole_0(A_57,A_108))
      | ~ v1_relat_1(k6_relat_1(A_57)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_50])).

tff(c_423,plain,(
    ! [A_110,A_111] : k7_relat_1(k6_relat_1(A_110),A_111) = k6_relat_1(k3_xboole_0(A_110,A_111)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_410])).

tff(c_30,plain,(
    ! [B_42,A_41] :
      ( k2_relat_1(k7_relat_1(B_42,A_41)) = k9_relat_1(B_42,A_41)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_429,plain,(
    ! [A_110,A_111] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_110,A_111))) = k9_relat_1(k6_relat_1(A_110),A_111)
      | ~ v1_relat_1(k6_relat_1(A_110)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_30])).

tff(c_441,plain,(
    ! [A_110,A_111] : k9_relat_1(k6_relat_1(A_110),A_111) = k3_xboole_0(A_110,A_111) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_429])).

tff(c_54,plain,(
    ! [A_60] : k2_funct_1(k6_relat_1(A_60)) = k6_relat_1(A_60) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1129,plain,(
    ! [B_159,A_160] :
      ( k9_relat_1(k2_funct_1(B_159),A_160) = k10_relat_1(B_159,A_160)
      | ~ v2_funct_1(B_159)
      | ~ v1_funct_1(B_159)
      | ~ v1_relat_1(B_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1138,plain,(
    ! [A_60,A_160] :
      ( k9_relat_1(k6_relat_1(A_60),A_160) = k10_relat_1(k6_relat_1(A_60),A_160)
      | ~ v2_funct_1(k6_relat_1(A_60))
      | ~ v1_funct_1(k6_relat_1(A_60))
      | ~ v1_relat_1(k6_relat_1(A_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1129])).

tff(c_1142,plain,(
    ! [A_60,A_160] : k10_relat_1(k6_relat_1(A_60),A_160) = k3_xboole_0(A_60,A_160) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46,c_52,c_441,c_1138])).

tff(c_40,plain,(
    ! [A_50,B_51] :
      ( k5_relat_1(k6_relat_1(A_50),B_51) = k7_relat_1(B_51,A_50)
      | ~ v1_relat_1(B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1249,plain,(
    ! [B_170,C_171,A_172] :
      ( k10_relat_1(k5_relat_1(B_170,C_171),A_172) = k10_relat_1(B_170,k10_relat_1(C_171,A_172))
      | ~ v1_relat_1(C_171)
      | ~ v1_relat_1(B_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1258,plain,(
    ! [A_50,B_51,A_172] :
      ( k10_relat_1(k6_relat_1(A_50),k10_relat_1(B_51,A_172)) = k10_relat_1(k7_relat_1(B_51,A_50),A_172)
      | ~ v1_relat_1(B_51)
      | ~ v1_relat_1(k6_relat_1(A_50))
      | ~ v1_relat_1(B_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1249])).

tff(c_9084,plain,(
    ! [A_318,B_319,A_320] :
      ( k3_xboole_0(A_318,k10_relat_1(B_319,A_320)) = k10_relat_1(k7_relat_1(B_319,A_318),A_320)
      | ~ v1_relat_1(B_319) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1142,c_1258])).

tff(c_12,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_147,plain,(
    ! [A_78,B_79] : k1_setfam_1(k2_tarski(A_78,B_79)) = k3_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_175,plain,(
    ! [B_81,A_82] : k1_setfam_1(k2_tarski(B_81,A_82)) = k3_xboole_0(A_82,B_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_147])).

tff(c_26,plain,(
    ! [A_37,B_38] : k1_setfam_1(k2_tarski(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_181,plain,(
    ! [B_81,A_82] : k3_xboole_0(B_81,A_82) = k3_xboole_0(A_82,B_81) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_26])).

tff(c_58,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_419,plain,(
    ! [A_57,A_108] : k7_relat_1(k6_relat_1(A_57),A_108) = k6_relat_1(k3_xboole_0(A_57,A_108)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_410])).

tff(c_34,plain,(
    ! [A_47] : k1_relat_1(k6_relat_1(A_47)) = A_47 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_602,plain,(
    ! [B_121,A_122] :
      ( k7_relat_1(B_121,A_122) = B_121
      | ~ r1_tarski(k1_relat_1(B_121),A_122)
      | ~ v1_relat_1(B_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_616,plain,(
    ! [A_47,A_122] :
      ( k7_relat_1(k6_relat_1(A_47),A_122) = k6_relat_1(A_47)
      | ~ r1_tarski(A_47,A_122)
      | ~ v1_relat_1(k6_relat_1(A_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_602])).

tff(c_1747,plain,(
    ! [A_195,A_196] :
      ( k6_relat_1(k3_xboole_0(A_195,A_196)) = k6_relat_1(A_195)
      | ~ r1_tarski(A_195,A_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_419,c_616])).

tff(c_1774,plain,(
    ! [A_195,A_196] :
      ( k3_xboole_0(A_195,A_196) = k2_relat_1(k6_relat_1(A_195))
      | ~ r1_tarski(A_195,A_196) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1747,c_36])).

tff(c_1821,plain,(
    ! [A_204,A_205] :
      ( k3_xboole_0(A_204,A_205) = A_204
      | ~ r1_tarski(A_204,A_205) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1774])).

tff(c_1897,plain,(
    k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_1821])).

tff(c_2115,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_1897])).

tff(c_9217,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9084,c_2115])).

tff(c_9379,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_9217])).

tff(c_9381,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_9379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 16:11:04 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.50/2.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.50/2.53  
% 6.50/2.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.50/2.54  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k2_funct_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 6.50/2.54  
% 6.50/2.54  %Foreground sorts:
% 6.50/2.54  
% 6.50/2.54  
% 6.50/2.54  %Background operators:
% 6.50/2.54  
% 6.50/2.54  
% 6.50/2.54  %Foreground operators:
% 6.50/2.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.50/2.54  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.50/2.54  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.50/2.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.50/2.54  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.50/2.54  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.50/2.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.50/2.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.50/2.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.50/2.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.50/2.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.50/2.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.50/2.54  tff('#skF_2', type, '#skF_2': $i).
% 6.50/2.54  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.50/2.54  tff('#skF_3', type, '#skF_3': $i).
% 6.50/2.54  tff('#skF_1', type, '#skF_1': $i).
% 6.50/2.54  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.50/2.54  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.50/2.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.50/2.54  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.50/2.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.50/2.54  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.50/2.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.50/2.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.50/2.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.50/2.54  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.50/2.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.50/2.54  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.50/2.54  
% 6.50/2.55  tff(f_116, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 6.50/2.55  tff(f_92, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 6.50/2.55  tff(f_104, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 6.50/2.55  tff(f_74, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 6.50/2.55  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 6.50/2.55  tff(f_102, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 6.50/2.55  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 6.50/2.55  tff(f_106, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 6.50/2.55  tff(f_100, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 6.50/2.55  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 6.50/2.55  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.50/2.55  tff(f_55, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 6.50/2.55  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 6.50/2.55  tff(c_56, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.50/2.55  tff(c_62, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.50/2.55  tff(c_44, plain, (![A_54]: (v1_relat_1(k6_relat_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.50/2.55  tff(c_46, plain, (![A_54]: (v1_funct_1(k6_relat_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.50/2.55  tff(c_52, plain, (![A_59]: (v2_funct_1(k6_relat_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.50/2.55  tff(c_36, plain, (![A_47]: (k2_relat_1(k6_relat_1(A_47))=A_47)), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.50/2.55  tff(c_403, plain, (![A_108, B_109]: (k5_relat_1(k6_relat_1(A_108), B_109)=k7_relat_1(B_109, A_108) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.50/2.55  tff(c_50, plain, (![B_58, A_57]: (k5_relat_1(k6_relat_1(B_58), k6_relat_1(A_57))=k6_relat_1(k3_xboole_0(A_57, B_58)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 6.50/2.55  tff(c_410, plain, (![A_57, A_108]: (k7_relat_1(k6_relat_1(A_57), A_108)=k6_relat_1(k3_xboole_0(A_57, A_108)) | ~v1_relat_1(k6_relat_1(A_57)))), inference(superposition, [status(thm), theory('equality')], [c_403, c_50])).
% 6.50/2.55  tff(c_423, plain, (![A_110, A_111]: (k7_relat_1(k6_relat_1(A_110), A_111)=k6_relat_1(k3_xboole_0(A_110, A_111)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_410])).
% 6.50/2.55  tff(c_30, plain, (![B_42, A_41]: (k2_relat_1(k7_relat_1(B_42, A_41))=k9_relat_1(B_42, A_41) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.50/2.55  tff(c_429, plain, (![A_110, A_111]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_110, A_111)))=k9_relat_1(k6_relat_1(A_110), A_111) | ~v1_relat_1(k6_relat_1(A_110)))), inference(superposition, [status(thm), theory('equality')], [c_423, c_30])).
% 6.50/2.55  tff(c_441, plain, (![A_110, A_111]: (k9_relat_1(k6_relat_1(A_110), A_111)=k3_xboole_0(A_110, A_111))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_429])).
% 6.50/2.55  tff(c_54, plain, (![A_60]: (k2_funct_1(k6_relat_1(A_60))=k6_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_106])).
% 6.50/2.55  tff(c_1129, plain, (![B_159, A_160]: (k9_relat_1(k2_funct_1(B_159), A_160)=k10_relat_1(B_159, A_160) | ~v2_funct_1(B_159) | ~v1_funct_1(B_159) | ~v1_relat_1(B_159))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.50/2.55  tff(c_1138, plain, (![A_60, A_160]: (k9_relat_1(k6_relat_1(A_60), A_160)=k10_relat_1(k6_relat_1(A_60), A_160) | ~v2_funct_1(k6_relat_1(A_60)) | ~v1_funct_1(k6_relat_1(A_60)) | ~v1_relat_1(k6_relat_1(A_60)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1129])).
% 6.50/2.55  tff(c_1142, plain, (![A_60, A_160]: (k10_relat_1(k6_relat_1(A_60), A_160)=k3_xboole_0(A_60, A_160))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46, c_52, c_441, c_1138])).
% 6.50/2.55  tff(c_40, plain, (![A_50, B_51]: (k5_relat_1(k6_relat_1(A_50), B_51)=k7_relat_1(B_51, A_50) | ~v1_relat_1(B_51))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.50/2.55  tff(c_1249, plain, (![B_170, C_171, A_172]: (k10_relat_1(k5_relat_1(B_170, C_171), A_172)=k10_relat_1(B_170, k10_relat_1(C_171, A_172)) | ~v1_relat_1(C_171) | ~v1_relat_1(B_170))), inference(cnfTransformation, [status(thm)], [f_70])).
% 6.50/2.55  tff(c_1258, plain, (![A_50, B_51, A_172]: (k10_relat_1(k6_relat_1(A_50), k10_relat_1(B_51, A_172))=k10_relat_1(k7_relat_1(B_51, A_50), A_172) | ~v1_relat_1(B_51) | ~v1_relat_1(k6_relat_1(A_50)) | ~v1_relat_1(B_51))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1249])).
% 6.50/2.55  tff(c_9084, plain, (![A_318, B_319, A_320]: (k3_xboole_0(A_318, k10_relat_1(B_319, A_320))=k10_relat_1(k7_relat_1(B_319, A_318), A_320) | ~v1_relat_1(B_319))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1142, c_1258])).
% 6.50/2.55  tff(c_12, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.50/2.55  tff(c_147, plain, (![A_78, B_79]: (k1_setfam_1(k2_tarski(A_78, B_79))=k3_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.50/2.55  tff(c_175, plain, (![B_81, A_82]: (k1_setfam_1(k2_tarski(B_81, A_82))=k3_xboole_0(A_82, B_81))), inference(superposition, [status(thm), theory('equality')], [c_12, c_147])).
% 6.50/2.55  tff(c_26, plain, (![A_37, B_38]: (k1_setfam_1(k2_tarski(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.50/2.55  tff(c_181, plain, (![B_81, A_82]: (k3_xboole_0(B_81, A_82)=k3_xboole_0(A_82, B_81))), inference(superposition, [status(thm), theory('equality')], [c_175, c_26])).
% 6.50/2.55  tff(c_58, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.50/2.55  tff(c_419, plain, (![A_57, A_108]: (k7_relat_1(k6_relat_1(A_57), A_108)=k6_relat_1(k3_xboole_0(A_57, A_108)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_410])).
% 6.50/2.55  tff(c_34, plain, (![A_47]: (k1_relat_1(k6_relat_1(A_47))=A_47)), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.50/2.55  tff(c_602, plain, (![B_121, A_122]: (k7_relat_1(B_121, A_122)=B_121 | ~r1_tarski(k1_relat_1(B_121), A_122) | ~v1_relat_1(B_121))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.50/2.55  tff(c_616, plain, (![A_47, A_122]: (k7_relat_1(k6_relat_1(A_47), A_122)=k6_relat_1(A_47) | ~r1_tarski(A_47, A_122) | ~v1_relat_1(k6_relat_1(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_602])).
% 6.50/2.55  tff(c_1747, plain, (![A_195, A_196]: (k6_relat_1(k3_xboole_0(A_195, A_196))=k6_relat_1(A_195) | ~r1_tarski(A_195, A_196))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_419, c_616])).
% 6.50/2.55  tff(c_1774, plain, (![A_195, A_196]: (k3_xboole_0(A_195, A_196)=k2_relat_1(k6_relat_1(A_195)) | ~r1_tarski(A_195, A_196))), inference(superposition, [status(thm), theory('equality')], [c_1747, c_36])).
% 6.50/2.55  tff(c_1821, plain, (![A_204, A_205]: (k3_xboole_0(A_204, A_205)=A_204 | ~r1_tarski(A_204, A_205))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1774])).
% 6.50/2.55  tff(c_1897, plain, (k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_1821])).
% 6.50/2.55  tff(c_2115, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_181, c_1897])).
% 6.50/2.55  tff(c_9217, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9084, c_2115])).
% 6.50/2.55  tff(c_9379, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_9217])).
% 6.50/2.55  tff(c_9381, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_9379])).
% 6.50/2.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.50/2.55  
% 6.50/2.55  Inference rules
% 6.50/2.55  ----------------------
% 6.50/2.55  #Ref     : 0
% 6.50/2.55  #Sup     : 2313
% 6.50/2.55  #Fact    : 0
% 6.50/2.55  #Define  : 0
% 6.50/2.55  #Split   : 1
% 6.50/2.55  #Chain   : 0
% 6.50/2.55  #Close   : 0
% 6.50/2.55  
% 6.50/2.55  Ordering : KBO
% 6.50/2.55  
% 6.50/2.55  Simplification rules
% 6.50/2.55  ----------------------
% 6.50/2.55  #Subsume      : 140
% 6.50/2.55  #Demod        : 1786
% 6.50/2.55  #Tautology    : 1354
% 6.50/2.55  #SimpNegUnit  : 1
% 6.50/2.55  #BackRed      : 4
% 6.50/2.55  
% 6.50/2.55  #Partial instantiations: 0
% 6.50/2.55  #Strategies tried      : 1
% 6.50/2.55  
% 6.50/2.55  Timing (in seconds)
% 6.50/2.55  ----------------------
% 6.50/2.55  Preprocessing        : 0.35
% 6.50/2.55  Parsing              : 0.18
% 6.50/2.55  CNF conversion       : 0.02
% 6.50/2.55  Main loop            : 1.43
% 6.50/2.55  Inferencing          : 0.37
% 6.50/2.55  Reduction            : 0.69
% 6.50/2.55  Demodulation         : 0.58
% 6.50/2.55  BG Simplification    : 0.05
% 6.50/2.55  Subsumption          : 0.25
% 6.50/2.55  Abstraction          : 0.07
% 6.50/2.55  MUC search           : 0.00
% 6.50/2.55  Cooper               : 0.00
% 6.50/2.55  Total                : 1.81
% 6.50/2.55  Index Insertion      : 0.00
% 6.50/2.55  Index Deletion       : 0.00
% 6.50/2.55  Index Matching       : 0.00
% 6.50/2.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
