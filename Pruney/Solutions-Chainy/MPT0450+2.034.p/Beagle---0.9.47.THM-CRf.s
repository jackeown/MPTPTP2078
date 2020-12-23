%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:40 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  69 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   55 (  94 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    ! [A_35,B_36] :
      ( v1_relat_1(k3_xboole_0(A_35,B_36))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_51,plain,(
    ! [A_47,B_48] : k2_xboole_0(A_47,k3_xboole_0(A_47,B_48)) = A_47 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_60,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_51])).

tff(c_108,plain,(
    ! [A_61,B_62,C_63] : r1_tarski(k2_xboole_0(k3_xboole_0(A_61,B_62),k3_xboole_0(A_61,C_63)),k2_xboole_0(B_62,C_63)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_112,plain,(
    ! [A_61,B_62] : r1_tarski(k3_xboole_0(A_61,B_62),k2_xboole_0(B_62,B_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_108])).

tff(c_125,plain,(
    ! [A_61,B_62] : r1_tarski(k3_xboole_0(A_61,B_62),B_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_112])).

tff(c_212,plain,(
    ! [A_85,B_86] :
      ( r1_tarski(k3_relat_1(A_85),k3_relat_1(B_86))
      | ~ r1_tarski(A_85,B_86)
      | ~ v1_relat_1(B_86)
      | ~ v1_relat_1(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_187,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(k3_relat_1(A_78),k3_relat_1(B_79))
      | ~ r1_tarski(A_78,B_79)
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_137,plain,(
    ! [A_66,B_67,C_68] :
      ( r1_tarski(A_66,k3_xboole_0(B_67,C_68))
      | ~ r1_tarski(A_66,C_68)
      | ~ r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k3_relat_1('#skF_1'),k3_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_144,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_137,c_28])).

tff(c_163,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_144])).

tff(c_190,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_187,c_163])).

tff(c_193,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4,c_190])).

tff(c_205,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_193])).

tff(c_209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_205])).

tff(c_210,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_144])).

tff(c_215,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_212,c_210])).

tff(c_218,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_125,c_215])).

tff(c_221,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_218])).

tff(c_225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:06:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.31  
% 1.97/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.31  %$ r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_relat_1 > k1_setfam_1 > #skF_2 > #skF_1
% 1.97/1.31  
% 1.97/1.31  %Foreground sorts:
% 1.97/1.31  
% 1.97/1.31  
% 1.97/1.31  %Background operators:
% 1.97/1.31  
% 1.97/1.31  
% 1.97/1.31  %Foreground operators:
% 1.97/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.97/1.31  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.97/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.31  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.31  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.97/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.97/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.97/1.31  
% 2.21/1.33  tff(f_72, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relat_1)).
% 2.21/1.33  tff(f_55, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.21/1.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.21/1.33  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.21/1.33  tff(f_39, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.21/1.33  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relat_1)).
% 2.21/1.33  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.21/1.33  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.21/1.33  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.21/1.33  tff(c_24, plain, (![A_35, B_36]: (v1_relat_1(k3_xboole_0(A_35, B_36)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.21/1.33  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.21/1.33  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.33  tff(c_51, plain, (![A_47, B_48]: (k2_xboole_0(A_47, k3_xboole_0(A_47, B_48))=A_47)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.21/1.33  tff(c_60, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_51])).
% 2.21/1.33  tff(c_108, plain, (![A_61, B_62, C_63]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_61, B_62), k3_xboole_0(A_61, C_63)), k2_xboole_0(B_62, C_63)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.21/1.33  tff(c_112, plain, (![A_61, B_62]: (r1_tarski(k3_xboole_0(A_61, B_62), k2_xboole_0(B_62, B_62)))), inference(superposition, [status(thm), theory('equality')], [c_60, c_108])).
% 2.21/1.33  tff(c_125, plain, (![A_61, B_62]: (r1_tarski(k3_xboole_0(A_61, B_62), B_62))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_112])).
% 2.21/1.33  tff(c_212, plain, (![A_85, B_86]: (r1_tarski(k3_relat_1(A_85), k3_relat_1(B_86)) | ~r1_tarski(A_85, B_86) | ~v1_relat_1(B_86) | ~v1_relat_1(A_85))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.21/1.33  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.33  tff(c_187, plain, (![A_78, B_79]: (r1_tarski(k3_relat_1(A_78), k3_relat_1(B_79)) | ~r1_tarski(A_78, B_79) | ~v1_relat_1(B_79) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.21/1.33  tff(c_137, plain, (![A_66, B_67, C_68]: (r1_tarski(A_66, k3_xboole_0(B_67, C_68)) | ~r1_tarski(A_66, C_68) | ~r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.21/1.33  tff(c_28, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k3_relat_1('#skF_1'), k3_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.21/1.33  tff(c_144, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_137, c_28])).
% 2.21/1.33  tff(c_163, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_144])).
% 2.21/1.33  tff(c_190, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_187, c_163])).
% 2.21/1.33  tff(c_193, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4, c_190])).
% 2.21/1.33  tff(c_205, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_193])).
% 2.21/1.33  tff(c_209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_205])).
% 2.21/1.33  tff(c_210, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_144])).
% 2.21/1.33  tff(c_215, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_212, c_210])).
% 2.21/1.33  tff(c_218, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_125, c_215])).
% 2.21/1.33  tff(c_221, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_24, c_218])).
% 2.21/1.33  tff(c_225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_221])).
% 2.21/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.33  
% 2.21/1.33  Inference rules
% 2.21/1.33  ----------------------
% 2.21/1.33  #Ref     : 0
% 2.21/1.33  #Sup     : 41
% 2.21/1.33  #Fact    : 0
% 2.21/1.33  #Define  : 0
% 2.21/1.33  #Split   : 1
% 2.21/1.33  #Chain   : 0
% 2.21/1.33  #Close   : 0
% 2.21/1.33  
% 2.21/1.33  Ordering : KBO
% 2.21/1.33  
% 2.21/1.33  Simplification rules
% 2.21/1.33  ----------------------
% 2.21/1.33  #Subsume      : 0
% 2.21/1.33  #Demod        : 30
% 2.21/1.33  #Tautology    : 29
% 2.21/1.33  #SimpNegUnit  : 0
% 2.21/1.33  #BackRed      : 0
% 2.21/1.33  
% 2.21/1.33  #Partial instantiations: 0
% 2.21/1.33  #Strategies tried      : 1
% 2.21/1.33  
% 2.21/1.33  Timing (in seconds)
% 2.21/1.33  ----------------------
% 2.21/1.33  Preprocessing        : 0.36
% 2.21/1.33  Parsing              : 0.17
% 2.21/1.33  CNF conversion       : 0.03
% 2.21/1.33  Main loop            : 0.20
% 2.21/1.33  Inferencing          : 0.08
% 2.21/1.33  Reduction            : 0.07
% 2.21/1.33  Demodulation         : 0.05
% 2.21/1.33  BG Simplification    : 0.01
% 2.21/1.33  Subsumption          : 0.04
% 2.21/1.33  Abstraction          : 0.01
% 2.21/1.33  MUC search           : 0.00
% 2.21/1.33  Cooper               : 0.00
% 2.21/1.33  Total                : 0.59
% 2.21/1.33  Index Insertion      : 0.00
% 2.21/1.33  Index Deletion       : 0.00
% 2.21/1.33  Index Matching       : 0.00
% 2.21/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
