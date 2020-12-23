%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:30 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.42s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 108 expanded)
%              Number of leaves         :   32 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  106 ( 168 expanded)
%              Number of equality atoms :   26 (  50 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_60,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_86,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( r1_tarski(A,k1_relat_1(C))
          & r1_tarski(k9_relat_1(C,A),B) )
       => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_36,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_42,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_20,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    ! [B_27,A_26] : k5_relat_1(k6_relat_1(B_27),k6_relat_1(A_26)) = k6_relat_1(k3_xboole_0(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_492,plain,(
    ! [A_81,B_82] :
      ( k10_relat_1(A_81,k1_relat_1(B_82)) = k1_relat_1(k5_relat_1(A_81,B_82))
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_564,plain,(
    ! [A_81,A_16] :
      ( k1_relat_1(k5_relat_1(A_81,k6_relat_1(A_16))) = k10_relat_1(A_81,A_16)
      | ~ v1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(A_81) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_492])).

tff(c_1032,plain,(
    ! [A_120,A_121] :
      ( k1_relat_1(k5_relat_1(A_120,k6_relat_1(A_121))) = k10_relat_1(A_120,A_121)
      | ~ v1_relat_1(A_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_564])).

tff(c_1058,plain,(
    ! [A_26,B_27] :
      ( k1_relat_1(k6_relat_1(k3_xboole_0(A_26,B_27))) = k10_relat_1(k6_relat_1(B_27),A_26)
      | ~ v1_relat_1(k6_relat_1(B_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1032])).

tff(c_1066,plain,(
    ! [B_27,A_26] : k10_relat_1(k6_relat_1(B_27),A_26) = k3_xboole_0(A_26,B_27) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_1058])).

tff(c_26,plain,(
    ! [A_17] : v1_funct_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_16] : k2_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_90,plain,(
    ! [A_43] :
      ( k10_relat_1(A_43,k2_relat_1(A_43)) = k1_relat_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_106,plain,(
    ! [A_16] :
      ( k10_relat_1(k6_relat_1(A_16),A_16) = k1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_90])).

tff(c_113,plain,(
    ! [A_16] : k10_relat_1(k6_relat_1(A_16),A_16) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_106])).

tff(c_260,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(k9_relat_1(B_60,k10_relat_1(B_60,A_61)),A_61)
      | ~ v1_funct_1(B_60)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_275,plain,(
    ! [A_16] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_16),A_16),A_16)
      | ~ v1_funct_1(k6_relat_1(A_16))
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_260])).

tff(c_302,plain,(
    ! [A_65] : r1_tarski(k9_relat_1(k6_relat_1(A_65),A_65),A_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_275])).

tff(c_38,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_157,plain,(
    ! [A_49,C_50,B_51] :
      ( r1_tarski(A_49,C_50)
      | ~ r1_tarski(B_51,C_50)
      | ~ r1_tarski(A_49,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_168,plain,(
    ! [A_49] :
      ( r1_tarski(A_49,'#skF_2')
      | ~ r1_tarski(A_49,k10_relat_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_38,c_157])).

tff(c_316,plain,(
    r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')),k10_relat_1('#skF_1','#skF_3')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_302,c_168])).

tff(c_850,plain,(
    ! [A_101,C_102,B_103] :
      ( r1_tarski(A_101,k10_relat_1(C_102,B_103))
      | ~ r1_tarski(k9_relat_1(C_102,A_101),B_103)
      | ~ r1_tarski(A_101,k1_relat_1(C_102))
      | ~ v1_funct_1(C_102)
      | ~ v1_relat_1(C_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_853,plain,
    ( r1_tarski(k10_relat_1('#skF_1','#skF_3'),k10_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')),'#skF_2'))
    | ~ r1_tarski(k10_relat_1('#skF_1','#skF_3'),k1_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3'))))
    | ~ v1_funct_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')))
    | ~ v1_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_316,c_850])).

tff(c_866,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),k10_relat_1(k6_relat_1(k10_relat_1('#skF_1','#skF_3')),'#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_6,c_20,c_853])).

tff(c_1426,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1066,c_866])).

tff(c_83,plain,(
    ! [B_39,A_40] :
      ( r1_tarski(k10_relat_1(B_39,A_40),k1_relat_1(B_39))
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_86,plain,(
    ! [A_16,A_40] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_16),A_40),A_16)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_83])).

tff(c_88,plain,(
    ! [A_16,A_40] : r1_tarski(k10_relat_1(k6_relat_1(A_16),A_40),A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_86])).

tff(c_547,plain,(
    ! [A_16,B_82] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(A_16),B_82)),A_16)
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_88])).

tff(c_589,plain,(
    ! [A_83,B_84] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(A_83),B_84)),A_83)
      | ~ v1_relat_1(B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_547])).

tff(c_612,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(A_26,B_27))),B_27)
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_589])).

tff(c_621,plain,(
    ! [A_85,B_86] : r1_tarski(k3_xboole_0(A_85,B_86),B_86) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_20,c_612])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_650,plain,(
    ! [A_85,B_86] :
      ( k3_xboole_0(A_85,B_86) = B_86
      | ~ r1_tarski(B_86,k3_xboole_0(A_85,B_86)) ) ),
    inference(resolution,[status(thm)],[c_621,c_2])).

tff(c_1440,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_1426,c_650])).

tff(c_28,plain,(
    ! [A_18,C_20,B_19] :
      ( k3_xboole_0(A_18,k10_relat_1(C_20,B_19)) = k10_relat_1(k7_relat_1(C_20,A_18),B_19)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1479,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1440,c_28])).

tff(c_1496,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1479])).

tff(c_1498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1496])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.52  
% 3.17/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.52  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.17/1.52  
% 3.17/1.52  %Foreground sorts:
% 3.17/1.52  
% 3.17/1.52  
% 3.17/1.52  %Background operators:
% 3.17/1.52  
% 3.17/1.52  
% 3.17/1.52  %Foreground operators:
% 3.17/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.17/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.52  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.17/1.52  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.17/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.17/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.17/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.17/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.17/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.17/1.52  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.17/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.17/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.17/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.52  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.17/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.17/1.52  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.17/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.17/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.17/1.52  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.17/1.52  
% 3.42/1.53  tff(f_96, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 3.42/1.53  tff(f_64, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.42/1.53  tff(f_60, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.42/1.53  tff(f_86, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 3.42/1.53  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 3.42/1.53  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.42/1.53  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.42/1.53  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 3.42/1.53  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.42/1.53  tff(f_84, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t163_funct_1)).
% 3.42/1.53  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 3.42/1.53  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 3.42/1.53  tff(c_36, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.42/1.53  tff(c_42, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.42/1.53  tff(c_24, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.42/1.53  tff(c_20, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.42/1.53  tff(c_34, plain, (![B_27, A_26]: (k5_relat_1(k6_relat_1(B_27), k6_relat_1(A_26))=k6_relat_1(k3_xboole_0(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.42/1.53  tff(c_492, plain, (![A_81, B_82]: (k10_relat_1(A_81, k1_relat_1(B_82))=k1_relat_1(k5_relat_1(A_81, B_82)) | ~v1_relat_1(B_82) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.42/1.53  tff(c_564, plain, (![A_81, A_16]: (k1_relat_1(k5_relat_1(A_81, k6_relat_1(A_16)))=k10_relat_1(A_81, A_16) | ~v1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(A_81))), inference(superposition, [status(thm), theory('equality')], [c_20, c_492])).
% 3.42/1.53  tff(c_1032, plain, (![A_120, A_121]: (k1_relat_1(k5_relat_1(A_120, k6_relat_1(A_121)))=k10_relat_1(A_120, A_121) | ~v1_relat_1(A_120))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_564])).
% 3.42/1.53  tff(c_1058, plain, (![A_26, B_27]: (k1_relat_1(k6_relat_1(k3_xboole_0(A_26, B_27)))=k10_relat_1(k6_relat_1(B_27), A_26) | ~v1_relat_1(k6_relat_1(B_27)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1032])).
% 3.42/1.53  tff(c_1066, plain, (![B_27, A_26]: (k10_relat_1(k6_relat_1(B_27), A_26)=k3_xboole_0(A_26, B_27))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_1058])).
% 3.42/1.53  tff(c_26, plain, (![A_17]: (v1_funct_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.42/1.53  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.42/1.53  tff(c_22, plain, (![A_16]: (k2_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.42/1.53  tff(c_90, plain, (![A_43]: (k10_relat_1(A_43, k2_relat_1(A_43))=k1_relat_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.42/1.53  tff(c_106, plain, (![A_16]: (k10_relat_1(k6_relat_1(A_16), A_16)=k1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_90])).
% 3.42/1.53  tff(c_113, plain, (![A_16]: (k10_relat_1(k6_relat_1(A_16), A_16)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_106])).
% 3.42/1.53  tff(c_260, plain, (![B_60, A_61]: (r1_tarski(k9_relat_1(B_60, k10_relat_1(B_60, A_61)), A_61) | ~v1_funct_1(B_60) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.42/1.53  tff(c_275, plain, (![A_16]: (r1_tarski(k9_relat_1(k6_relat_1(A_16), A_16), A_16) | ~v1_funct_1(k6_relat_1(A_16)) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_260])).
% 3.42/1.53  tff(c_302, plain, (![A_65]: (r1_tarski(k9_relat_1(k6_relat_1(A_65), A_65), A_65))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_275])).
% 3.42/1.53  tff(c_38, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.42/1.53  tff(c_157, plain, (![A_49, C_50, B_51]: (r1_tarski(A_49, C_50) | ~r1_tarski(B_51, C_50) | ~r1_tarski(A_49, B_51))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.42/1.53  tff(c_168, plain, (![A_49]: (r1_tarski(A_49, '#skF_2') | ~r1_tarski(A_49, k10_relat_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_38, c_157])).
% 3.42/1.53  tff(c_316, plain, (r1_tarski(k9_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')), k10_relat_1('#skF_1', '#skF_3')), '#skF_2')), inference(resolution, [status(thm)], [c_302, c_168])).
% 3.42/1.53  tff(c_850, plain, (![A_101, C_102, B_103]: (r1_tarski(A_101, k10_relat_1(C_102, B_103)) | ~r1_tarski(k9_relat_1(C_102, A_101), B_103) | ~r1_tarski(A_101, k1_relat_1(C_102)) | ~v1_funct_1(C_102) | ~v1_relat_1(C_102))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.42/1.53  tff(c_853, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k10_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')), '#skF_2')) | ~r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k1_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')))) | ~v1_funct_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3'))) | ~v1_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_316, c_850])).
% 3.42/1.53  tff(c_866, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k10_relat_1(k6_relat_1(k10_relat_1('#skF_1', '#skF_3')), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_6, c_20, c_853])).
% 3.42/1.53  tff(c_1426, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1066, c_866])).
% 3.42/1.53  tff(c_83, plain, (![B_39, A_40]: (r1_tarski(k10_relat_1(B_39, A_40), k1_relat_1(B_39)) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.42/1.53  tff(c_86, plain, (![A_16, A_40]: (r1_tarski(k10_relat_1(k6_relat_1(A_16), A_40), A_16) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_83])).
% 3.42/1.53  tff(c_88, plain, (![A_16, A_40]: (r1_tarski(k10_relat_1(k6_relat_1(A_16), A_40), A_16))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_86])).
% 3.42/1.53  tff(c_547, plain, (![A_16, B_82]: (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(A_16), B_82)), A_16) | ~v1_relat_1(B_82) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_492, c_88])).
% 3.42/1.53  tff(c_589, plain, (![A_83, B_84]: (r1_tarski(k1_relat_1(k5_relat_1(k6_relat_1(A_83), B_84)), A_83) | ~v1_relat_1(B_84))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_547])).
% 3.42/1.53  tff(c_612, plain, (![A_26, B_27]: (r1_tarski(k1_relat_1(k6_relat_1(k3_xboole_0(A_26, B_27))), B_27) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_589])).
% 3.42/1.53  tff(c_621, plain, (![A_85, B_86]: (r1_tarski(k3_xboole_0(A_85, B_86), B_86))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_20, c_612])).
% 3.42/1.53  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.42/1.53  tff(c_650, plain, (![A_85, B_86]: (k3_xboole_0(A_85, B_86)=B_86 | ~r1_tarski(B_86, k3_xboole_0(A_85, B_86)))), inference(resolution, [status(thm)], [c_621, c_2])).
% 3.42/1.53  tff(c_1440, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_1426, c_650])).
% 3.42/1.53  tff(c_28, plain, (![A_18, C_20, B_19]: (k3_xboole_0(A_18, k10_relat_1(C_20, B_19))=k10_relat_1(k7_relat_1(C_20, A_18), B_19) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.42/1.53  tff(c_1479, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1440, c_28])).
% 3.42/1.53  tff(c_1496, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1479])).
% 3.42/1.53  tff(c_1498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_1496])).
% 3.42/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.42/1.53  
% 3.42/1.53  Inference rules
% 3.42/1.53  ----------------------
% 3.42/1.53  #Ref     : 0
% 3.42/1.53  #Sup     : 319
% 3.42/1.53  #Fact    : 0
% 3.42/1.53  #Define  : 0
% 3.42/1.53  #Split   : 1
% 3.42/1.53  #Chain   : 0
% 3.42/1.53  #Close   : 0
% 3.42/1.53  
% 3.42/1.53  Ordering : KBO
% 3.42/1.53  
% 3.42/1.53  Simplification rules
% 3.42/1.53  ----------------------
% 3.42/1.53  #Subsume      : 14
% 3.42/1.53  #Demod        : 237
% 3.42/1.53  #Tautology    : 115
% 3.42/1.53  #SimpNegUnit  : 1
% 3.42/1.53  #BackRed      : 10
% 3.42/1.53  
% 3.42/1.53  #Partial instantiations: 0
% 3.42/1.53  #Strategies tried      : 1
% 3.42/1.53  
% 3.42/1.53  Timing (in seconds)
% 3.42/1.53  ----------------------
% 3.42/1.54  Preprocessing        : 0.32
% 3.42/1.54  Parsing              : 0.18
% 3.42/1.54  CNF conversion       : 0.02
% 3.42/1.54  Main loop            : 0.44
% 3.42/1.54  Inferencing          : 0.15
% 3.42/1.54  Reduction            : 0.16
% 3.42/1.54  Demodulation         : 0.12
% 3.42/1.54  BG Simplification    : 0.02
% 3.42/1.54  Subsumption          : 0.08
% 3.42/1.54  Abstraction          : 0.03
% 3.42/1.54  MUC search           : 0.00
% 3.42/1.54  Cooper               : 0.00
% 3.42/1.54  Total                : 0.79
% 3.42/1.54  Index Insertion      : 0.00
% 3.42/1.54  Index Deletion       : 0.00
% 3.42/1.54  Index Matching       : 0.00
% 3.42/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
