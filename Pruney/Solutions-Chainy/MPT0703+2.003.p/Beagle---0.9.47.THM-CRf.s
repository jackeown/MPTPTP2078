%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:09 EST 2020

% Result     : Theorem 20.19s
% Output     : CNFRefutation 20.19s
% Verified   : 
% Statistics : Number of formulae       :   57 (  94 expanded)
%              Number of leaves         :   23 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :   71 ( 160 expanded)
%              Number of equality atoms :   21 (  40 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_30,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_38,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_36,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    ! [A_21] :
      ( k9_relat_1(A_21,k1_relat_1(A_21)) = k2_relat_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1472,plain,(
    ! [A_79,B_80] :
      ( k3_xboole_0(A_79,k9_relat_1(B_80,k1_relat_1(B_80))) = k9_relat_1(B_80,k10_relat_1(B_80,A_79))
      | ~ v1_funct_1(B_80)
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1576,plain,(
    ! [A_21,A_79] :
      ( k9_relat_1(A_21,k10_relat_1(A_21,A_79)) = k3_xboole_0(A_79,k2_relat_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1472])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_176,plain,(
    ! [A_41,B_42] :
      ( k3_xboole_0(A_41,B_42) = A_41
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_195,plain,(
    k3_xboole_0('#skF_1',k2_relat_1('#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_176])).

tff(c_34,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_193,plain,(
    k3_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) = k10_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_176])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_711,plain,(
    ! [A_57,B_58,C_59] : k3_xboole_0(k3_xboole_0(A_57,B_58),C_59) = k3_xboole_0(A_57,k3_xboole_0(B_58,C_59)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_831,plain,(
    ! [A_57,B_58,A_3] : k3_xboole_0(A_57,k3_xboole_0(B_58,A_3)) = k3_xboole_0(A_3,k3_xboole_0(A_57,B_58)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_711])).

tff(c_2235,plain,(
    ! [C_95,A_96,B_97] :
      ( r1_tarski(k9_relat_1(C_95,k3_xboole_0(A_96,B_97)),k3_xboole_0(k9_relat_1(C_95,A_96),k9_relat_1(C_95,B_97)))
      | ~ v1_relat_1(C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( k3_xboole_0(A_16,B_17) = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2307,plain,(
    ! [C_95,A_96,B_97] :
      ( k3_xboole_0(k9_relat_1(C_95,k3_xboole_0(A_96,B_97)),k3_xboole_0(k9_relat_1(C_95,A_96),k9_relat_1(C_95,B_97))) = k9_relat_1(C_95,k3_xboole_0(A_96,B_97))
      | ~ v1_relat_1(C_95) ) ),
    inference(resolution,[status(thm)],[c_2235,c_20])).

tff(c_28960,plain,(
    ! [C_300,B_301,A_302] :
      ( k3_xboole_0(k9_relat_1(C_300,B_301),k3_xboole_0(k9_relat_1(C_300,A_302),k9_relat_1(C_300,k3_xboole_0(A_302,B_301)))) = k9_relat_1(C_300,k3_xboole_0(A_302,B_301))
      | ~ v1_relat_1(C_300) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_831,c_2307])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_tarski(k3_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_73561,plain,(
    ! [C_541,A_542,B_543] :
      ( r1_tarski(k9_relat_1(C_541,k3_xboole_0(A_542,B_543)),k9_relat_1(C_541,B_543))
      | ~ v1_relat_1(C_541) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28960,c_16])).

tff(c_74575,plain,(
    ! [C_548] :
      ( r1_tarski(k9_relat_1(C_548,k10_relat_1('#skF_3','#skF_1')),k9_relat_1(C_548,k10_relat_1('#skF_3','#skF_2')))
      | ~ v1_relat_1(C_548) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_73561])).

tff(c_74584,plain,
    ( r1_tarski(k3_xboole_0('#skF_1',k2_relat_1('#skF_3')),k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1576,c_74575])).

tff(c_74592,plain,(
    r1_tarski('#skF_1',k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_36,c_38,c_195,c_74584])).

tff(c_74602,plain,
    ( r1_tarski('#skF_1',k3_xboole_0('#skF_2',k2_relat_1('#skF_3')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1576,c_74592])).

tff(c_74606,plain,(
    r1_tarski('#skF_1',k3_xboole_0('#skF_2',k2_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_36,c_74602])).

tff(c_74613,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',k2_relat_1('#skF_3'))) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_74606,c_20])).

tff(c_312,plain,(
    ! [A_47,B_48] : k3_xboole_0(k3_xboole_0(A_47,B_48),A_47) = k3_xboole_0(A_47,B_48) ),
    inference(resolution,[status(thm)],[c_16,c_176])).

tff(c_354,plain,(
    ! [B_4,A_3] : k3_xboole_0(k3_xboole_0(B_4,A_3),A_3) = k3_xboole_0(A_3,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_312])).

tff(c_84,plain,(
    ! [B_33,A_34] : k3_xboole_0(B_33,A_34) = k3_xboole_0(A_34,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_99,plain,(
    ! [B_33,A_34] : r1_tarski(k3_xboole_0(B_33,A_34),A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_16])).

tff(c_850,plain,(
    ! [A_60,B_61,C_62] : r1_tarski(k3_xboole_0(A_60,k3_xboole_0(B_61,C_62)),C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_711,c_99])).

tff(c_871,plain,(
    ! [A_60,A_3,B_4] : r1_tarski(k3_xboole_0(A_60,k3_xboole_0(A_3,B_4)),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_850])).

tff(c_75015,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_74613,c_871])).

tff(c_75169,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_75015])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:31:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.19/13.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.19/13.28  
% 20.19/13.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.19/13.28  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 20.19/13.28  
% 20.19/13.28  %Foreground sorts:
% 20.19/13.28  
% 20.19/13.28  
% 20.19/13.28  %Background operators:
% 20.19/13.28  
% 20.19/13.28  
% 20.19/13.28  %Foreground operators:
% 20.19/13.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 20.19/13.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 20.19/13.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 20.19/13.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 20.19/13.28  tff('#skF_2', type, '#skF_2': $i).
% 20.19/13.28  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 20.19/13.28  tff('#skF_3', type, '#skF_3': $i).
% 20.19/13.28  tff('#skF_1', type, '#skF_1': $i).
% 20.19/13.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 20.19/13.28  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 20.19/13.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 20.19/13.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 20.19/13.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 20.19/13.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 20.19/13.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 20.19/13.28  
% 20.19/13.30  tff(f_74, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t158_funct_1)).
% 20.19/13.30  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 20.19/13.30  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_funct_1)).
% 20.19/13.30  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 20.19/13.30  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 20.19/13.30  tff(f_39, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 20.19/13.30  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_relat_1)).
% 20.19/13.30  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 20.19/13.30  tff(c_30, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 20.19/13.30  tff(c_38, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 20.19/13.30  tff(c_36, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 20.19/13.30  tff(c_24, plain, (![A_21]: (k9_relat_1(A_21, k1_relat_1(A_21))=k2_relat_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_53])).
% 20.19/13.30  tff(c_1472, plain, (![A_79, B_80]: (k3_xboole_0(A_79, k9_relat_1(B_80, k1_relat_1(B_80)))=k9_relat_1(B_80, k10_relat_1(B_80, A_79)) | ~v1_funct_1(B_80) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_63])).
% 20.19/13.30  tff(c_1576, plain, (![A_21, A_79]: (k9_relat_1(A_21, k10_relat_1(A_21, A_79))=k3_xboole_0(A_79, k2_relat_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21) | ~v1_relat_1(A_21))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1472])).
% 20.19/13.30  tff(c_32, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 20.19/13.30  tff(c_176, plain, (![A_41, B_42]: (k3_xboole_0(A_41, B_42)=A_41 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_47])).
% 20.19/13.30  tff(c_195, plain, (k3_xboole_0('#skF_1', k2_relat_1('#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_32, c_176])).
% 20.19/13.30  tff(c_34, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 20.19/13.30  tff(c_193, plain, (k3_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))=k10_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_176])).
% 20.19/13.30  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 20.19/13.30  tff(c_711, plain, (![A_57, B_58, C_59]: (k3_xboole_0(k3_xboole_0(A_57, B_58), C_59)=k3_xboole_0(A_57, k3_xboole_0(B_58, C_59)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 20.19/13.30  tff(c_831, plain, (![A_57, B_58, A_3]: (k3_xboole_0(A_57, k3_xboole_0(B_58, A_3))=k3_xboole_0(A_3, k3_xboole_0(A_57, B_58)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_711])).
% 20.19/13.30  tff(c_2235, plain, (![C_95, A_96, B_97]: (r1_tarski(k9_relat_1(C_95, k3_xboole_0(A_96, B_97)), k3_xboole_0(k9_relat_1(C_95, A_96), k9_relat_1(C_95, B_97))) | ~v1_relat_1(C_95))), inference(cnfTransformation, [status(thm)], [f_57])).
% 20.19/13.30  tff(c_20, plain, (![A_16, B_17]: (k3_xboole_0(A_16, B_17)=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 20.19/13.30  tff(c_2307, plain, (![C_95, A_96, B_97]: (k3_xboole_0(k9_relat_1(C_95, k3_xboole_0(A_96, B_97)), k3_xboole_0(k9_relat_1(C_95, A_96), k9_relat_1(C_95, B_97)))=k9_relat_1(C_95, k3_xboole_0(A_96, B_97)) | ~v1_relat_1(C_95))), inference(resolution, [status(thm)], [c_2235, c_20])).
% 20.19/13.30  tff(c_28960, plain, (![C_300, B_301, A_302]: (k3_xboole_0(k9_relat_1(C_300, B_301), k3_xboole_0(k9_relat_1(C_300, A_302), k9_relat_1(C_300, k3_xboole_0(A_302, B_301))))=k9_relat_1(C_300, k3_xboole_0(A_302, B_301)) | ~v1_relat_1(C_300))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_831, c_2307])).
% 20.19/13.30  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(k3_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 20.19/13.30  tff(c_73561, plain, (![C_541, A_542, B_543]: (r1_tarski(k9_relat_1(C_541, k3_xboole_0(A_542, B_543)), k9_relat_1(C_541, B_543)) | ~v1_relat_1(C_541))), inference(superposition, [status(thm), theory('equality')], [c_28960, c_16])).
% 20.19/13.30  tff(c_74575, plain, (![C_548]: (r1_tarski(k9_relat_1(C_548, k10_relat_1('#skF_3', '#skF_1')), k9_relat_1(C_548, k10_relat_1('#skF_3', '#skF_2'))) | ~v1_relat_1(C_548))), inference(superposition, [status(thm), theory('equality')], [c_193, c_73561])).
% 20.19/13.30  tff(c_74584, plain, (r1_tarski(k3_xboole_0('#skF_1', k2_relat_1('#skF_3')), k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))) | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1576, c_74575])).
% 20.19/13.30  tff(c_74592, plain, (r1_tarski('#skF_1', k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_36, c_38, c_195, c_74584])).
% 20.19/13.30  tff(c_74602, plain, (r1_tarski('#skF_1', k3_xboole_0('#skF_2', k2_relat_1('#skF_3'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1576, c_74592])).
% 20.19/13.30  tff(c_74606, plain, (r1_tarski('#skF_1', k3_xboole_0('#skF_2', k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_36, c_74602])).
% 20.19/13.30  tff(c_74613, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', k2_relat_1('#skF_3')))='#skF_1'), inference(resolution, [status(thm)], [c_74606, c_20])).
% 20.19/13.30  tff(c_312, plain, (![A_47, B_48]: (k3_xboole_0(k3_xboole_0(A_47, B_48), A_47)=k3_xboole_0(A_47, B_48))), inference(resolution, [status(thm)], [c_16, c_176])).
% 20.19/13.30  tff(c_354, plain, (![B_4, A_3]: (k3_xboole_0(k3_xboole_0(B_4, A_3), A_3)=k3_xboole_0(A_3, B_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_312])).
% 20.19/13.30  tff(c_84, plain, (![B_33, A_34]: (k3_xboole_0(B_33, A_34)=k3_xboole_0(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_29])).
% 20.19/13.30  tff(c_99, plain, (![B_33, A_34]: (r1_tarski(k3_xboole_0(B_33, A_34), A_34))), inference(superposition, [status(thm), theory('equality')], [c_84, c_16])).
% 20.19/13.30  tff(c_850, plain, (![A_60, B_61, C_62]: (r1_tarski(k3_xboole_0(A_60, k3_xboole_0(B_61, C_62)), C_62))), inference(superposition, [status(thm), theory('equality')], [c_711, c_99])).
% 20.19/13.30  tff(c_871, plain, (![A_60, A_3, B_4]: (r1_tarski(k3_xboole_0(A_60, k3_xboole_0(A_3, B_4)), A_3))), inference(superposition, [status(thm), theory('equality')], [c_354, c_850])).
% 20.19/13.30  tff(c_75015, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_74613, c_871])).
% 20.19/13.30  tff(c_75169, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_75015])).
% 20.19/13.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.19/13.30  
% 20.19/13.30  Inference rules
% 20.19/13.30  ----------------------
% 20.19/13.30  #Ref     : 0
% 20.19/13.30  #Sup     : 18920
% 20.19/13.30  #Fact    : 0
% 20.19/13.30  #Define  : 0
% 20.19/13.30  #Split   : 2
% 20.19/13.30  #Chain   : 0
% 20.19/13.30  #Close   : 0
% 20.19/13.30  
% 20.19/13.30  Ordering : KBO
% 20.19/13.30  
% 20.19/13.30  Simplification rules
% 20.19/13.30  ----------------------
% 20.19/13.30  #Subsume      : 539
% 20.19/13.30  #Demod        : 19935
% 20.19/13.30  #Tautology    : 9579
% 20.19/13.30  #SimpNegUnit  : 1
% 20.19/13.30  #BackRed      : 1
% 20.19/13.30  
% 20.19/13.30  #Partial instantiations: 0
% 20.19/13.30  #Strategies tried      : 1
% 20.19/13.30  
% 20.19/13.30  Timing (in seconds)
% 20.19/13.30  ----------------------
% 20.19/13.30  Preprocessing        : 0.29
% 20.19/13.30  Parsing              : 0.16
% 20.19/13.30  CNF conversion       : 0.02
% 20.19/13.30  Main loop            : 12.26
% 20.19/13.30  Inferencing          : 1.17
% 20.19/13.30  Reduction            : 8.21
% 20.19/13.30  Demodulation         : 7.66
% 20.19/13.30  BG Simplification    : 0.19
% 20.19/13.30  Subsumption          : 2.25
% 20.19/13.30  Abstraction          : 0.27
% 20.19/13.30  MUC search           : 0.00
% 20.19/13.30  Cooper               : 0.00
% 20.19/13.30  Total                : 12.58
% 20.19/13.30  Index Insertion      : 0.00
% 20.19/13.30  Index Deletion       : 0.00
% 20.19/13.30  Index Matching       : 0.00
% 20.19/13.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
