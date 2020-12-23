%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:05 EST 2020

% Result     : Theorem 6.54s
% Output     : CNFRefutation 6.89s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 152 expanded)
%              Number of leaves         :   24 (  65 expanded)
%              Depth                    :   17
%              Number of atoms          :  145 ( 420 expanded)
%              Number of equality atoms :   16 (  33 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_26,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_512,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(k10_relat_1(B_58,k9_relat_1(B_58,A_59)),A_59)
      | ~ v2_funct_1(B_58)
      | ~ v1_funct_1(B_58)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_519,plain,(
    ! [B_58,A_59] :
      ( k2_xboole_0(k10_relat_1(B_58,k9_relat_1(B_58,A_59)),A_59) = A_59
      | ~ v2_funct_1(B_58)
      | ~ v1_funct_1(B_58)
      | ~ v1_relat_1(B_58) ) ),
    inference(resolution,[status(thm)],[c_512,c_10])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_37,plain,(
    ! [A_19,B_20] :
      ( k2_xboole_0(A_19,B_20) = B_20
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_47,plain,(
    k2_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k9_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_37])).

tff(c_331,plain,(
    ! [C_46,A_47,B_48] :
      ( r1_tarski(k9_relat_1(C_46,A_47),k9_relat_1(C_46,B_48))
      | ~ r1_tarski(A_47,B_48)
      | ~ v1_relat_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1644,plain,(
    ! [C_115,A_116,B_117] :
      ( k2_xboole_0(k9_relat_1(C_115,A_116),k9_relat_1(C_115,B_117)) = k9_relat_1(C_115,B_117)
      | ~ r1_tarski(A_116,B_117)
      | ~ v1_relat_1(C_115) ) ),
    inference(resolution,[status(thm)],[c_331,c_10])).

tff(c_65,plain,(
    ! [A_24,C_25,B_26] :
      ( r1_tarski(A_24,C_25)
      | ~ r1_tarski(k2_xboole_0(A_24,B_26),C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_77,plain,(
    ! [A_27,B_28] : r1_tarski(A_27,k2_xboole_0(A_27,B_28)) ),
    inference(resolution,[status(thm)],[c_6,c_65])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_91,plain,(
    ! [A_3,B_4,B_28] : r1_tarski(A_3,k2_xboole_0(k2_xboole_0(A_3,B_4),B_28)) ),
    inference(resolution,[status(thm)],[c_77,c_8])).

tff(c_2571,plain,(
    ! [C_142,A_143,B_144,B_145] :
      ( r1_tarski(k9_relat_1(C_142,A_143),k2_xboole_0(k9_relat_1(C_142,B_144),B_145))
      | ~ r1_tarski(A_143,B_144)
      | ~ v1_relat_1(C_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1644,c_91])).

tff(c_2613,plain,(
    ! [A_143] :
      ( r1_tarski(k9_relat_1('#skF_3',A_143),k9_relat_1('#skF_3','#skF_2'))
      | ~ r1_tarski(A_143,'#skF_1')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_2571])).

tff(c_2631,plain,(
    ! [A_143] :
      ( r1_tarski(k9_relat_1('#skF_3',A_143),k9_relat_1('#skF_3','#skF_2'))
      | ~ r1_tarski(A_143,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2613])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( k9_relat_1(k2_funct_1(B_17),A_16) = k10_relat_1(B_17,A_16)
      | ~ v2_funct_1(B_17)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,k10_relat_1(B_13,k9_relat_1(B_13,A_12)))
      | ~ r1_tarski(A_12,k1_relat_1(B_13))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3362,plain,(
    ! [B_170,A_171] :
      ( k10_relat_1(B_170,k9_relat_1(B_170,A_171)) = A_171
      | ~ r1_tarski(A_171,k10_relat_1(B_170,k9_relat_1(B_170,A_171)))
      | ~ v2_funct_1(B_170)
      | ~ v1_funct_1(B_170)
      | ~ v1_relat_1(B_170) ) ),
    inference(resolution,[status(thm)],[c_512,c_2])).

tff(c_5295,plain,(
    ! [B_257,A_258] :
      ( k10_relat_1(B_257,k9_relat_1(B_257,A_258)) = A_258
      | ~ v2_funct_1(B_257)
      | ~ v1_funct_1(B_257)
      | ~ r1_tarski(A_258,k1_relat_1(B_257))
      | ~ v1_relat_1(B_257) ) ),
    inference(resolution,[status(thm)],[c_18,c_3362])).

tff(c_5303,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_5295])).

tff(c_5311,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_5303])).

tff(c_1188,plain,(
    ! [B_94,A_95] :
      ( k9_relat_1(k2_funct_1(B_94),A_95) = k10_relat_1(B_94,A_95)
      | ~ v2_funct_1(B_94)
      | ~ v1_funct_1(B_94)
      | ~ v1_relat_1(B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12,plain,(
    ! [C_10,A_8,B_9] :
      ( r1_tarski(k9_relat_1(C_10,A_8),k9_relat_1(C_10,B_9))
      | ~ r1_tarski(A_8,B_9)
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1200,plain,(
    ! [B_94,A_95,B_9] :
      ( r1_tarski(k10_relat_1(B_94,A_95),k9_relat_1(k2_funct_1(B_94),B_9))
      | ~ r1_tarski(A_95,B_9)
      | ~ v1_relat_1(k2_funct_1(B_94))
      | ~ v2_funct_1(B_94)
      | ~ v1_funct_1(B_94)
      | ~ v1_relat_1(B_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1188,c_12])).

tff(c_5322,plain,(
    ! [B_9] :
      ( r1_tarski('#skF_1',k9_relat_1(k2_funct_1('#skF_3'),B_9))
      | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),B_9)
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5311,c_1200])).

tff(c_5351,plain,(
    ! [B_9] :
      ( r1_tarski('#skF_1',k9_relat_1(k2_funct_1('#skF_3'),B_9))
      | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),B_9)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_5322])).

tff(c_5625,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5351])).

tff(c_5628,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_5625])).

tff(c_5632,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_5628])).

tff(c_5708,plain,(
    ! [B_276] :
      ( r1_tarski('#skF_1',k9_relat_1(k2_funct_1('#skF_3'),B_276))
      | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),B_276) ) ),
    inference(splitRight,[status(thm)],[c_5351])).

tff(c_5721,plain,(
    ! [A_16] :
      ( r1_tarski('#skF_1',k10_relat_1('#skF_3',A_16))
      | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),A_16)
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_5708])).

tff(c_5729,plain,(
    ! [A_277] :
      ( r1_tarski('#skF_1',k10_relat_1('#skF_3',A_277))
      | ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),A_277) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_5721])).

tff(c_5765,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')))
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_2631,c_5729])).

tff(c_5855,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5765])).

tff(c_5894,plain,(
    k2_xboole_0('#skF_1',k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2'))) = k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_5855,c_10])).

tff(c_7417,plain,(
    ! [B_318] : r1_tarski('#skF_1',k2_xboole_0(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')),B_318)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5894,c_91])).

tff(c_7438,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_7417])).

tff(c_7458,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_7438])).

tff(c_7460,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_7458])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:42:52 EST 2020
% 0.19/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.54/2.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.54/2.41  
% 6.54/2.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.89/2.41  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_funct_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 6.89/2.41  
% 6.89/2.41  %Foreground sorts:
% 6.89/2.41  
% 6.89/2.41  
% 6.89/2.41  %Background operators:
% 6.89/2.41  
% 6.89/2.41  
% 6.89/2.41  %Foreground operators:
% 6.89/2.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.89/2.41  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.89/2.41  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.89/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.89/2.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.89/2.41  tff('#skF_2', type, '#skF_2': $i).
% 6.89/2.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.89/2.41  tff('#skF_3', type, '#skF_3': $i).
% 6.89/2.41  tff('#skF_1', type, '#skF_1': $i).
% 6.89/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.89/2.41  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.89/2.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.89/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.89/2.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.89/2.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.89/2.41  
% 6.89/2.43  tff(f_88, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t157_funct_1)).
% 6.89/2.43  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_funct_1)).
% 6.89/2.43  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.89/2.43  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.89/2.43  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 6.89/2.43  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 6.89/2.43  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 6.89/2.43  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 6.89/2.43  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 6.89/2.43  tff(c_24, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.89/2.43  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.89/2.43  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.89/2.43  tff(c_26, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.89/2.43  tff(c_512, plain, (![B_58, A_59]: (r1_tarski(k10_relat_1(B_58, k9_relat_1(B_58, A_59)), A_59) | ~v2_funct_1(B_58) | ~v1_funct_1(B_58) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.89/2.43  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.89/2.43  tff(c_519, plain, (![B_58, A_59]: (k2_xboole_0(k10_relat_1(B_58, k9_relat_1(B_58, A_59)), A_59)=A_59 | ~v2_funct_1(B_58) | ~v1_funct_1(B_58) | ~v1_relat_1(B_58))), inference(resolution, [status(thm)], [c_512, c_10])).
% 6.89/2.43  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.89/2.43  tff(c_30, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.89/2.43  tff(c_37, plain, (![A_19, B_20]: (k2_xboole_0(A_19, B_20)=B_20 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.89/2.43  tff(c_47, plain, (k2_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k9_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_37])).
% 6.89/2.43  tff(c_331, plain, (![C_46, A_47, B_48]: (r1_tarski(k9_relat_1(C_46, A_47), k9_relat_1(C_46, B_48)) | ~r1_tarski(A_47, B_48) | ~v1_relat_1(C_46))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.89/2.43  tff(c_1644, plain, (![C_115, A_116, B_117]: (k2_xboole_0(k9_relat_1(C_115, A_116), k9_relat_1(C_115, B_117))=k9_relat_1(C_115, B_117) | ~r1_tarski(A_116, B_117) | ~v1_relat_1(C_115))), inference(resolution, [status(thm)], [c_331, c_10])).
% 6.89/2.43  tff(c_65, plain, (![A_24, C_25, B_26]: (r1_tarski(A_24, C_25) | ~r1_tarski(k2_xboole_0(A_24, B_26), C_25))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.89/2.43  tff(c_77, plain, (![A_27, B_28]: (r1_tarski(A_27, k2_xboole_0(A_27, B_28)))), inference(resolution, [status(thm)], [c_6, c_65])).
% 6.89/2.43  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.89/2.43  tff(c_91, plain, (![A_3, B_4, B_28]: (r1_tarski(A_3, k2_xboole_0(k2_xboole_0(A_3, B_4), B_28)))), inference(resolution, [status(thm)], [c_77, c_8])).
% 6.89/2.43  tff(c_2571, plain, (![C_142, A_143, B_144, B_145]: (r1_tarski(k9_relat_1(C_142, A_143), k2_xboole_0(k9_relat_1(C_142, B_144), B_145)) | ~r1_tarski(A_143, B_144) | ~v1_relat_1(C_142))), inference(superposition, [status(thm), theory('equality')], [c_1644, c_91])).
% 6.89/2.43  tff(c_2613, plain, (![A_143]: (r1_tarski(k9_relat_1('#skF_3', A_143), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(A_143, '#skF_1') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_47, c_2571])).
% 6.89/2.43  tff(c_2631, plain, (![A_143]: (r1_tarski(k9_relat_1('#skF_3', A_143), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(A_143, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2613])).
% 6.89/2.43  tff(c_22, plain, (![B_17, A_16]: (k9_relat_1(k2_funct_1(B_17), A_16)=k10_relat_1(B_17, A_16) | ~v2_funct_1(B_17) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.89/2.43  tff(c_16, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.89/2.43  tff(c_28, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.89/2.43  tff(c_18, plain, (![A_12, B_13]: (r1_tarski(A_12, k10_relat_1(B_13, k9_relat_1(B_13, A_12))) | ~r1_tarski(A_12, k1_relat_1(B_13)) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.89/2.43  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.89/2.43  tff(c_3362, plain, (![B_170, A_171]: (k10_relat_1(B_170, k9_relat_1(B_170, A_171))=A_171 | ~r1_tarski(A_171, k10_relat_1(B_170, k9_relat_1(B_170, A_171))) | ~v2_funct_1(B_170) | ~v1_funct_1(B_170) | ~v1_relat_1(B_170))), inference(resolution, [status(thm)], [c_512, c_2])).
% 6.89/2.43  tff(c_5295, plain, (![B_257, A_258]: (k10_relat_1(B_257, k9_relat_1(B_257, A_258))=A_258 | ~v2_funct_1(B_257) | ~v1_funct_1(B_257) | ~r1_tarski(A_258, k1_relat_1(B_257)) | ~v1_relat_1(B_257))), inference(resolution, [status(thm)], [c_18, c_3362])).
% 6.89/2.43  tff(c_5303, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_5295])).
% 6.89/2.43  tff(c_5311, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_5303])).
% 6.89/2.43  tff(c_1188, plain, (![B_94, A_95]: (k9_relat_1(k2_funct_1(B_94), A_95)=k10_relat_1(B_94, A_95) | ~v2_funct_1(B_94) | ~v1_funct_1(B_94) | ~v1_relat_1(B_94))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.89/2.43  tff(c_12, plain, (![C_10, A_8, B_9]: (r1_tarski(k9_relat_1(C_10, A_8), k9_relat_1(C_10, B_9)) | ~r1_tarski(A_8, B_9) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.89/2.43  tff(c_1200, plain, (![B_94, A_95, B_9]: (r1_tarski(k10_relat_1(B_94, A_95), k9_relat_1(k2_funct_1(B_94), B_9)) | ~r1_tarski(A_95, B_9) | ~v1_relat_1(k2_funct_1(B_94)) | ~v2_funct_1(B_94) | ~v1_funct_1(B_94) | ~v1_relat_1(B_94))), inference(superposition, [status(thm), theory('equality')], [c_1188, c_12])).
% 6.89/2.43  tff(c_5322, plain, (![B_9]: (r1_tarski('#skF_1', k9_relat_1(k2_funct_1('#skF_3'), B_9)) | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), B_9) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5311, c_1200])).
% 6.89/2.43  tff(c_5351, plain, (![B_9]: (r1_tarski('#skF_1', k9_relat_1(k2_funct_1('#skF_3'), B_9)) | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), B_9) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_5322])).
% 6.89/2.43  tff(c_5625, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5351])).
% 6.89/2.43  tff(c_5628, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_5625])).
% 6.89/2.43  tff(c_5632, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_5628])).
% 6.89/2.43  tff(c_5708, plain, (![B_276]: (r1_tarski('#skF_1', k9_relat_1(k2_funct_1('#skF_3'), B_276)) | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), B_276))), inference(splitRight, [status(thm)], [c_5351])).
% 6.89/2.43  tff(c_5721, plain, (![A_16]: (r1_tarski('#skF_1', k10_relat_1('#skF_3', A_16)) | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), A_16) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_5708])).
% 6.89/2.43  tff(c_5729, plain, (![A_277]: (r1_tarski('#skF_1', k10_relat_1('#skF_3', A_277)) | ~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), A_277))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_5721])).
% 6.89/2.43  tff(c_5765, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))) | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_2631, c_5729])).
% 6.89/2.43  tff(c_5855, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_5765])).
% 6.89/2.43  tff(c_5894, plain, (k2_xboole_0('#skF_1', k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2')))=k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_5855, c_10])).
% 6.89/2.43  tff(c_7417, plain, (![B_318]: (r1_tarski('#skF_1', k2_xboole_0(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2')), B_318)))), inference(superposition, [status(thm), theory('equality')], [c_5894, c_91])).
% 6.89/2.43  tff(c_7438, plain, (r1_tarski('#skF_1', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_519, c_7417])).
% 6.89/2.43  tff(c_7458, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_7438])).
% 6.89/2.43  tff(c_7460, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_7458])).
% 6.89/2.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.89/2.43  
% 6.89/2.43  Inference rules
% 6.89/2.43  ----------------------
% 6.89/2.43  #Ref     : 0
% 6.89/2.43  #Sup     : 1754
% 6.89/2.43  #Fact    : 0
% 6.89/2.43  #Define  : 0
% 6.89/2.43  #Split   : 6
% 6.89/2.43  #Chain   : 0
% 6.89/2.43  #Close   : 0
% 6.89/2.43  
% 6.89/2.43  Ordering : KBO
% 6.89/2.43  
% 6.89/2.43  Simplification rules
% 6.89/2.43  ----------------------
% 6.89/2.43  #Subsume      : 349
% 6.89/2.43  #Demod        : 728
% 6.89/2.43  #Tautology    : 434
% 6.89/2.43  #SimpNegUnit  : 3
% 6.89/2.43  #BackRed      : 0
% 6.89/2.43  
% 6.89/2.43  #Partial instantiations: 0
% 6.89/2.43  #Strategies tried      : 1
% 6.89/2.43  
% 6.89/2.43  Timing (in seconds)
% 6.89/2.43  ----------------------
% 6.89/2.43  Preprocessing        : 0.28
% 6.89/2.43  Parsing              : 0.16
% 6.89/2.43  CNF conversion       : 0.02
% 6.89/2.43  Main loop            : 1.39
% 6.89/2.43  Inferencing          : 0.41
% 6.89/2.43  Reduction            : 0.52
% 6.89/2.43  Demodulation         : 0.40
% 6.89/2.43  BG Simplification    : 0.05
% 6.89/2.43  Subsumption          : 0.32
% 6.89/2.43  Abstraction          : 0.06
% 6.89/2.43  MUC search           : 0.00
% 6.89/2.43  Cooper               : 0.00
% 6.89/2.43  Total                : 1.70
% 6.89/2.43  Index Insertion      : 0.00
% 6.89/2.43  Index Deletion       : 0.00
% 6.89/2.43  Index Matching       : 0.00
% 6.89/2.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
