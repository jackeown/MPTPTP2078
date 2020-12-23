%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:40 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   46 (  65 expanded)
%              Number of leaves         :   21 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 ( 102 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( v1_relat_1(k3_xboole_0(A_19,B_20))
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [A_33,B_34] :
      ( k2_xboole_0(A_33,B_34) = B_34
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_38])).

tff(c_232,plain,(
    ! [A_53,B_54,C_55] : r1_tarski(k2_xboole_0(k3_xboole_0(A_53,B_54),k3_xboole_0(A_53,C_55)),k2_xboole_0(B_54,C_55)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_259,plain,(
    ! [A_53,B_54] : r1_tarski(k3_xboole_0(A_53,B_54),k2_xboole_0(B_54,B_54)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_232])).

tff(c_266,plain,(
    ! [A_53,B_54] : r1_tarski(k3_xboole_0(A_53,B_54),B_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_259])).

tff(c_1181,plain,(
    ! [A_94,B_95] :
      ( r1_tarski(k3_relat_1(A_94),k3_relat_1(B_95))
      | ~ r1_tarski(A_94,B_95)
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_748,plain,(
    ! [A_79,B_80] :
      ( r1_tarski(k3_relat_1(A_79),k3_relat_1(B_80))
      | ~ r1_tarski(A_79,B_80)
      | ~ v1_relat_1(B_80)
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_337,plain,(
    ! [A_63,B_64,C_65] :
      ( r1_tarski(A_63,k3_xboole_0(B_64,C_65))
      | ~ r1_tarski(A_63,C_65)
      | ~ r1_tarski(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_28,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k3_relat_1('#skF_1'),k3_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_369,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_337,c_28])).

tff(c_491,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_369])).

tff(c_754,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_748,c_491])).

tff(c_766,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_12,c_754])).

tff(c_772,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_766])).

tff(c_776,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_772])).

tff(c_777,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_369])).

tff(c_1187,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1181,c_777])).

tff(c_1199,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_266,c_1187])).

tff(c_1205,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_1199])).

tff(c_1209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1205])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.51  
% 2.82/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.52  %$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.82/1.52  
% 2.82/1.52  %Foreground sorts:
% 2.82/1.52  
% 2.82/1.52  
% 2.82/1.52  %Background operators:
% 2.82/1.52  
% 2.82/1.52  
% 2.82/1.52  %Foreground operators:
% 2.82/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.52  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.82/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.82/1.52  tff('#skF_2', type, '#skF_2': $i).
% 2.82/1.52  tff('#skF_1', type, '#skF_1': $i).
% 2.82/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.82/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.82/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.82/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.82/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.82/1.52  
% 2.82/1.53  tff(f_80, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relat_1)).
% 2.82/1.53  tff(f_59, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.82/1.53  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.82/1.53  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.82/1.53  tff(f_49, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.82/1.53  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 2.82/1.53  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.82/1.53  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.82/1.53  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.82/1.53  tff(c_22, plain, (![A_19, B_20]: (v1_relat_1(k3_xboole_0(A_19, B_20)) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.82/1.53  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.82/1.53  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.82/1.53  tff(c_38, plain, (![A_33, B_34]: (k2_xboole_0(A_33, B_34)=B_34 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.82/1.53  tff(c_50, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_38])).
% 2.82/1.53  tff(c_232, plain, (![A_53, B_54, C_55]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_53, B_54), k3_xboole_0(A_53, C_55)), k2_xboole_0(B_54, C_55)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.82/1.53  tff(c_259, plain, (![A_53, B_54]: (r1_tarski(k3_xboole_0(A_53, B_54), k2_xboole_0(B_54, B_54)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_232])).
% 2.82/1.53  tff(c_266, plain, (![A_53, B_54]: (r1_tarski(k3_xboole_0(A_53, B_54), B_54))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_259])).
% 2.82/1.53  tff(c_1181, plain, (![A_94, B_95]: (r1_tarski(k3_relat_1(A_94), k3_relat_1(B_95)) | ~r1_tarski(A_94, B_95) | ~v1_relat_1(B_95) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.82/1.53  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.82/1.53  tff(c_748, plain, (![A_79, B_80]: (r1_tarski(k3_relat_1(A_79), k3_relat_1(B_80)) | ~r1_tarski(A_79, B_80) | ~v1_relat_1(B_80) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.82/1.53  tff(c_337, plain, (![A_63, B_64, C_65]: (r1_tarski(A_63, k3_xboole_0(B_64, C_65)) | ~r1_tarski(A_63, C_65) | ~r1_tarski(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.82/1.53  tff(c_28, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k3_relat_1('#skF_1'), k3_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.82/1.53  tff(c_369, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_337, c_28])).
% 2.82/1.53  tff(c_491, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_369])).
% 2.82/1.53  tff(c_754, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_748, c_491])).
% 2.82/1.53  tff(c_766, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_12, c_754])).
% 2.82/1.53  tff(c_772, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_766])).
% 2.82/1.53  tff(c_776, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_772])).
% 2.82/1.53  tff(c_777, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_369])).
% 2.82/1.53  tff(c_1187, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1181, c_777])).
% 2.82/1.53  tff(c_1199, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_266, c_1187])).
% 2.82/1.53  tff(c_1205, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_1199])).
% 2.82/1.53  tff(c_1209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_1205])).
% 2.82/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.53  
% 2.82/1.53  Inference rules
% 2.82/1.53  ----------------------
% 2.82/1.53  #Ref     : 0
% 2.82/1.53  #Sup     : 294
% 2.82/1.53  #Fact    : 0
% 2.82/1.53  #Define  : 0
% 2.82/1.53  #Split   : 1
% 2.82/1.53  #Chain   : 0
% 2.82/1.53  #Close   : 0
% 2.82/1.53  
% 2.82/1.53  Ordering : KBO
% 2.82/1.53  
% 2.82/1.53  Simplification rules
% 2.82/1.53  ----------------------
% 2.82/1.53  #Subsume      : 8
% 2.82/1.53  #Demod        : 134
% 2.82/1.53  #Tautology    : 151
% 2.82/1.53  #SimpNegUnit  : 0
% 2.82/1.53  #BackRed      : 0
% 2.82/1.53  
% 2.82/1.53  #Partial instantiations: 0
% 2.82/1.53  #Strategies tried      : 1
% 2.82/1.53  
% 2.82/1.53  Timing (in seconds)
% 2.82/1.53  ----------------------
% 3.11/1.53  Preprocessing        : 0.31
% 3.11/1.53  Parsing              : 0.17
% 3.11/1.53  CNF conversion       : 0.02
% 3.11/1.53  Main loop            : 0.39
% 3.11/1.53  Inferencing          : 0.15
% 3.11/1.53  Reduction            : 0.12
% 3.11/1.53  Demodulation         : 0.09
% 3.11/1.53  BG Simplification    : 0.02
% 3.11/1.53  Subsumption          : 0.07
% 3.11/1.53  Abstraction          : 0.02
% 3.11/1.53  MUC search           : 0.00
% 3.11/1.53  Cooper               : 0.00
% 3.11/1.53  Total                : 0.72
% 3.11/1.53  Index Insertion      : 0.00
% 3.11/1.53  Index Deletion       : 0.00
% 3.11/1.53  Index Matching       : 0.00
% 3.11/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
