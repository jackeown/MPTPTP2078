%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:15 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 127 expanded)
%              Number of leaves         :   20 (  56 expanded)
%              Depth                    :   15
%              Number of atoms          :   80 ( 309 expanded)
%              Number of equality atoms :   17 (  47 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B))
            & r1_tarski(A,k2_relat_1(C)) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(c_12,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_16,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_18,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_21,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_25,plain,(
    k3_xboole_0('#skF_1',k2_relat_1('#skF_3')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_14,c_21])).

tff(c_6,plain,(
    ! [A_6] :
      ( k9_relat_1(A_6,k1_relat_1(A_6)) = k2_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_96,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,k9_relat_1(B_28,k1_relat_1(B_28))) = k9_relat_1(B_28,k10_relat_1(B_28,A_27))
      | ~ v1_funct_1(B_28)
      | ~ v1_relat_1(B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_116,plain,(
    ! [A_6,A_27] :
      ( k9_relat_1(A_6,k10_relat_1(A_6,A_27)) = k3_xboole_0(A_27,k2_relat_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_96])).

tff(c_8,plain,(
    ! [C_9,A_7,B_8] :
      ( r1_tarski(k9_relat_1(C_9,A_7),k9_relat_1(C_9,B_8))
      | ~ r1_tarski(A_7,B_8)
      | ~ v1_relat_1(C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] :
      ( r1_tarski(A_1,B_2)
      | ~ r1_tarski(A_1,k3_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_119,plain,(
    ! [A_29,A_30,B_31] :
      ( r1_tarski(A_29,A_30)
      | ~ r1_tarski(A_29,k9_relat_1(B_31,k10_relat_1(B_31,A_30)))
      | ~ v1_funct_1(B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_2])).

tff(c_131,plain,(
    ! [C_34,A_35,A_36] :
      ( r1_tarski(k9_relat_1(C_34,A_35),A_36)
      | ~ v1_funct_1(C_34)
      | ~ r1_tarski(A_35,k10_relat_1(C_34,A_36))
      | ~ v1_relat_1(C_34) ) ),
    inference(resolution,[status(thm)],[c_8,c_119])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k3_xboole_0(A_4,B_5) = A_4
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_259,plain,(
    ! [C_50,A_51,A_52] :
      ( k3_xboole_0(k9_relat_1(C_50,A_51),A_52) = k9_relat_1(C_50,A_51)
      | ~ v1_funct_1(C_50)
      | ~ r1_tarski(A_51,k10_relat_1(C_50,A_52))
      | ~ v1_relat_1(C_50) ) ),
    inference(resolution,[status(thm)],[c_131,c_4])).

tff(c_266,plain,
    ( k3_xboole_0(k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')),'#skF_2') = k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_259])).

tff(c_270,plain,(
    k3_xboole_0(k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')),'#skF_2') = k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_266])).

tff(c_281,plain,
    ( k3_xboole_0(k3_xboole_0('#skF_1',k2_relat_1('#skF_3')),'#skF_2') = k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_270])).

tff(c_285,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_18,c_25,c_281])).

tff(c_299,plain,
    ( k3_xboole_0('#skF_1',k2_relat_1('#skF_3')) = k3_xboole_0('#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_116])).

tff(c_333,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_18,c_25,c_299])).

tff(c_351,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_285])).

tff(c_129,plain,(
    ! [C_9,A_7,A_30] :
      ( r1_tarski(k9_relat_1(C_9,A_7),A_30)
      | ~ v1_funct_1(C_9)
      | ~ r1_tarski(A_7,k10_relat_1(C_9,A_30))
      | ~ v1_relat_1(C_9) ) ),
    inference(resolution,[status(thm)],[c_8,c_119])).

tff(c_378,plain,(
    ! [A_30] :
      ( r1_tarski('#skF_1',A_30)
      | ~ v1_funct_1('#skF_3')
      | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3',A_30))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_129])).

tff(c_428,plain,(
    ! [A_53] :
      ( r1_tarski('#skF_1',A_53)
      | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3',A_53)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_378])).

tff(c_431,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_428])).

tff(c_435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_431])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:51:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.29  
% 2.23/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.29  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.23/1.29  
% 2.23/1.29  %Foreground sorts:
% 2.23/1.29  
% 2.23/1.29  
% 2.23/1.29  %Background operators:
% 2.23/1.29  
% 2.23/1.29  
% 2.23/1.29  %Foreground operators:
% 2.23/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.23/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.23/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.23/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.29  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.23/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.23/1.29  
% 2.23/1.30  tff(f_60, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B)) & r1_tarski(A, k2_relat_1(C))) => r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_funct_1)).
% 2.23/1.30  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.23/1.30  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.23/1.30  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 2.23/1.30  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 2.23/1.30  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 2.23/1.30  tff(c_12, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.23/1.30  tff(c_16, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.23/1.30  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.23/1.30  tff(c_18, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.23/1.30  tff(c_14, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.23/1.30  tff(c_21, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.23/1.30  tff(c_25, plain, (k3_xboole_0('#skF_1', k2_relat_1('#skF_3'))='#skF_1'), inference(resolution, [status(thm)], [c_14, c_21])).
% 2.23/1.30  tff(c_6, plain, (![A_6]: (k9_relat_1(A_6, k1_relat_1(A_6))=k2_relat_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.23/1.30  tff(c_96, plain, (![A_27, B_28]: (k3_xboole_0(A_27, k9_relat_1(B_28, k1_relat_1(B_28)))=k9_relat_1(B_28, k10_relat_1(B_28, A_27)) | ~v1_funct_1(B_28) | ~v1_relat_1(B_28))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.23/1.30  tff(c_116, plain, (![A_6, A_27]: (k9_relat_1(A_6, k10_relat_1(A_6, A_27))=k3_xboole_0(A_27, k2_relat_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(superposition, [status(thm), theory('equality')], [c_6, c_96])).
% 2.23/1.30  tff(c_8, plain, (![C_9, A_7, B_8]: (r1_tarski(k9_relat_1(C_9, A_7), k9_relat_1(C_9, B_8)) | ~r1_tarski(A_7, B_8) | ~v1_relat_1(C_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.23/1.30  tff(c_2, plain, (![A_1, B_2, C_3]: (r1_tarski(A_1, B_2) | ~r1_tarski(A_1, k3_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.30  tff(c_119, plain, (![A_29, A_30, B_31]: (r1_tarski(A_29, A_30) | ~r1_tarski(A_29, k9_relat_1(B_31, k10_relat_1(B_31, A_30))) | ~v1_funct_1(B_31) | ~v1_relat_1(B_31))), inference(superposition, [status(thm), theory('equality')], [c_96, c_2])).
% 2.23/1.30  tff(c_131, plain, (![C_34, A_35, A_36]: (r1_tarski(k9_relat_1(C_34, A_35), A_36) | ~v1_funct_1(C_34) | ~r1_tarski(A_35, k10_relat_1(C_34, A_36)) | ~v1_relat_1(C_34))), inference(resolution, [status(thm)], [c_8, c_119])).
% 2.23/1.30  tff(c_4, plain, (![A_4, B_5]: (k3_xboole_0(A_4, B_5)=A_4 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.23/1.30  tff(c_259, plain, (![C_50, A_51, A_52]: (k3_xboole_0(k9_relat_1(C_50, A_51), A_52)=k9_relat_1(C_50, A_51) | ~v1_funct_1(C_50) | ~r1_tarski(A_51, k10_relat_1(C_50, A_52)) | ~v1_relat_1(C_50))), inference(resolution, [status(thm)], [c_131, c_4])).
% 2.23/1.30  tff(c_266, plain, (k3_xboole_0(k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1')), '#skF_2')=k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_259])).
% 2.23/1.30  tff(c_270, plain, (k3_xboole_0(k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1')), '#skF_2')=k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_266])).
% 2.23/1.30  tff(c_281, plain, (k3_xboole_0(k3_xboole_0('#skF_1', k2_relat_1('#skF_3')), '#skF_2')=k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_116, c_270])).
% 2.23/1.30  tff(c_285, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))=k3_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_18, c_25, c_281])).
% 2.23/1.30  tff(c_299, plain, (k3_xboole_0('#skF_1', k2_relat_1('#skF_3'))=k3_xboole_0('#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_285, c_116])).
% 2.23/1.30  tff(c_333, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_18, c_25, c_299])).
% 2.23/1.30  tff(c_351, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_333, c_285])).
% 2.23/1.30  tff(c_129, plain, (![C_9, A_7, A_30]: (r1_tarski(k9_relat_1(C_9, A_7), A_30) | ~v1_funct_1(C_9) | ~r1_tarski(A_7, k10_relat_1(C_9, A_30)) | ~v1_relat_1(C_9))), inference(resolution, [status(thm)], [c_8, c_119])).
% 2.23/1.30  tff(c_378, plain, (![A_30]: (r1_tarski('#skF_1', A_30) | ~v1_funct_1('#skF_3') | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', A_30)) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_351, c_129])).
% 2.23/1.30  tff(c_428, plain, (![A_53]: (r1_tarski('#skF_1', A_53) | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', A_53)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_378])).
% 2.23/1.30  tff(c_431, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_16, c_428])).
% 2.23/1.30  tff(c_435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_431])).
% 2.23/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.30  
% 2.23/1.30  Inference rules
% 2.23/1.30  ----------------------
% 2.23/1.30  #Ref     : 0
% 2.23/1.30  #Sup     : 104
% 2.23/1.30  #Fact    : 0
% 2.23/1.30  #Define  : 0
% 2.23/1.30  #Split   : 0
% 2.23/1.30  #Chain   : 0
% 2.23/1.30  #Close   : 0
% 2.23/1.30  
% 2.23/1.30  Ordering : KBO
% 2.23/1.30  
% 2.23/1.30  Simplification rules
% 2.23/1.30  ----------------------
% 2.23/1.30  #Subsume      : 13
% 2.23/1.30  #Demod        : 61
% 2.23/1.30  #Tautology    : 38
% 2.23/1.30  #SimpNegUnit  : 1
% 2.23/1.30  #BackRed      : 2
% 2.23/1.30  
% 2.23/1.30  #Partial instantiations: 0
% 2.23/1.30  #Strategies tried      : 1
% 2.23/1.30  
% 2.23/1.30  Timing (in seconds)
% 2.23/1.30  ----------------------
% 2.23/1.31  Preprocessing        : 0.26
% 2.23/1.31  Parsing              : 0.15
% 2.23/1.31  CNF conversion       : 0.02
% 2.23/1.31  Main loop            : 0.28
% 2.23/1.31  Inferencing          : 0.12
% 2.23/1.31  Reduction            : 0.08
% 2.23/1.31  Demodulation         : 0.05
% 2.23/1.31  BG Simplification    : 0.02
% 2.23/1.31  Subsumption          : 0.05
% 2.23/1.31  Abstraction          : 0.01
% 2.23/1.31  MUC search           : 0.00
% 2.23/1.31  Cooper               : 0.00
% 2.23/1.31  Total                : 0.57
% 2.23/1.31  Index Insertion      : 0.00
% 2.23/1.31  Index Deletion       : 0.00
% 2.23/1.31  Index Matching       : 0.00
% 2.23/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
