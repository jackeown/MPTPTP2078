%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:48 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   52 (  83 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 164 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( k2_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = B_20
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_405,plain,(
    ! [A_85,B_86,C_87] : r1_tarski(k2_xboole_0(k3_xboole_0(A_85,B_86),k3_xboole_0(A_85,C_87)),k2_xboole_0(B_86,C_87)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_447,plain,(
    ! [A_88,B_89,C_90] : r1_tarski(k3_xboole_0(A_88,B_89),k2_xboole_0(B_89,C_90)) ),
    inference(resolution,[status(thm)],[c_405,c_8])).

tff(c_469,plain,(
    ! [A_88,A_19,B_20] :
      ( r1_tarski(k3_xboole_0(A_88,A_19),B_20)
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_447])).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_24,plain,(
    ! [A_23,B_24] :
      ( v1_relat_1(k3_xboole_0(A_23,B_24))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_846,plain,(
    ! [C_121,A_122,B_123] :
      ( r1_tarski(k5_relat_1(C_121,A_122),k5_relat_1(C_121,B_123))
      | ~ r1_tarski(A_122,B_123)
      | ~ v1_relat_1(C_121)
      | ~ v1_relat_1(B_123)
      | ~ v1_relat_1(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_623,plain,(
    ! [C_106,A_107,B_108] :
      ( r1_tarski(k5_relat_1(C_106,A_107),k5_relat_1(C_106,B_108))
      | ~ r1_tarski(A_107,B_108)
      | ~ v1_relat_1(C_106)
      | ~ v1_relat_1(B_108)
      | ~ v1_relat_1(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_172,plain,(
    ! [A_72,B_73,C_74] :
      ( r1_tarski(A_72,k3_xboole_0(B_73,C_74))
      | ~ r1_tarski(A_72,C_74)
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_197,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_172,c_28])).

tff(c_543,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_197])).

tff(c_626,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_623,c_543])).

tff(c_636,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_10,c_626])).

tff(c_642,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_636])).

tff(c_646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_642])).

tff(c_647,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_849,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_846,c_647])).

tff(c_859,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_849])).

tff(c_863,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_859])).

tff(c_866,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_863])).

tff(c_870,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_866])).

tff(c_871,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_859])).

tff(c_917,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_469,c_871])).

tff(c_922,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_917])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.39  
% 2.64/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.39  %$ r1_tarski > v1_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.64/1.39  
% 2.64/1.39  %Foreground sorts:
% 2.64/1.39  
% 2.64/1.39  
% 2.64/1.39  %Background operators:
% 2.64/1.39  
% 2.64/1.39  
% 2.64/1.39  %Foreground operators:
% 2.64/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.64/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.64/1.39  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.64/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.64/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.64/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.64/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.64/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.64/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.64/1.39  
% 2.95/1.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.95/1.40  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.95/1.40  tff(f_45, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.95/1.40  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.95/1.40  tff(f_86, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relat_1)).
% 2.95/1.40  tff(f_63, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.95/1.40  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_relat_1)).
% 2.95/1.40  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.95/1.40  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.95/1.40  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.95/1.40  tff(c_20, plain, (![A_19, B_20]: (k2_xboole_0(A_19, k4_xboole_0(B_20, A_19))=B_20 | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.95/1.40  tff(c_405, plain, (![A_85, B_86, C_87]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_85, B_86), k3_xboole_0(A_85, C_87)), k2_xboole_0(B_86, C_87)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.95/1.40  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.95/1.40  tff(c_447, plain, (![A_88, B_89, C_90]: (r1_tarski(k3_xboole_0(A_88, B_89), k2_xboole_0(B_89, C_90)))), inference(resolution, [status(thm)], [c_405, c_8])).
% 2.95/1.40  tff(c_469, plain, (![A_88, A_19, B_20]: (r1_tarski(k3_xboole_0(A_88, A_19), B_20) | ~r1_tarski(A_19, B_20))), inference(superposition, [status(thm), theory('equality')], [c_20, c_447])).
% 2.95/1.40  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.95/1.40  tff(c_24, plain, (![A_23, B_24]: (v1_relat_1(k3_xboole_0(A_23, B_24)) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.95/1.40  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.95/1.40  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.95/1.40  tff(c_846, plain, (![C_121, A_122, B_123]: (r1_tarski(k5_relat_1(C_121, A_122), k5_relat_1(C_121, B_123)) | ~r1_tarski(A_122, B_123) | ~v1_relat_1(C_121) | ~v1_relat_1(B_123) | ~v1_relat_1(A_122))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.95/1.40  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.95/1.40  tff(c_623, plain, (![C_106, A_107, B_108]: (r1_tarski(k5_relat_1(C_106, A_107), k5_relat_1(C_106, B_108)) | ~r1_tarski(A_107, B_108) | ~v1_relat_1(C_106) | ~v1_relat_1(B_108) | ~v1_relat_1(A_107))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.95/1.40  tff(c_172, plain, (![A_72, B_73, C_74]: (r1_tarski(A_72, k3_xboole_0(B_73, C_74)) | ~r1_tarski(A_72, C_74) | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.95/1.40  tff(c_28, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.95/1.40  tff(c_197, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_3')) | ~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_172, c_28])).
% 2.95/1.40  tff(c_543, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_197])).
% 2.95/1.40  tff(c_626, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_623, c_543])).
% 2.95/1.40  tff(c_636, plain, (~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_10, c_626])).
% 2.95/1.40  tff(c_642, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_636])).
% 2.95/1.40  tff(c_646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_642])).
% 2.95/1.40  tff(c_647, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_197])).
% 2.95/1.40  tff(c_849, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_846, c_647])).
% 2.95/1.40  tff(c_859, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34, c_849])).
% 2.95/1.40  tff(c_863, plain, (~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_859])).
% 2.95/1.40  tff(c_866, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_863])).
% 2.95/1.40  tff(c_870, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_866])).
% 2.95/1.40  tff(c_871, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_859])).
% 2.95/1.40  tff(c_917, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_469, c_871])).
% 2.95/1.40  tff(c_922, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_917])).
% 2.95/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.40  
% 2.95/1.40  Inference rules
% 2.95/1.40  ----------------------
% 2.95/1.40  #Ref     : 0
% 2.95/1.40  #Sup     : 215
% 2.95/1.40  #Fact    : 0
% 2.95/1.40  #Define  : 0
% 2.95/1.40  #Split   : 2
% 2.95/1.40  #Chain   : 0
% 2.95/1.40  #Close   : 0
% 2.95/1.40  
% 2.95/1.40  Ordering : KBO
% 2.95/1.40  
% 2.95/1.40  Simplification rules
% 2.95/1.40  ----------------------
% 2.95/1.40  #Subsume      : 9
% 2.95/1.40  #Demod        : 62
% 2.95/1.40  #Tautology    : 84
% 2.95/1.40  #SimpNegUnit  : 0
% 2.95/1.40  #BackRed      : 0
% 2.95/1.40  
% 2.95/1.40  #Partial instantiations: 0
% 2.95/1.40  #Strategies tried      : 1
% 2.95/1.40  
% 2.95/1.40  Timing (in seconds)
% 2.95/1.40  ----------------------
% 2.95/1.40  Preprocessing        : 0.29
% 2.95/1.40  Parsing              : 0.16
% 2.95/1.40  CNF conversion       : 0.02
% 2.95/1.40  Main loop            : 0.35
% 2.95/1.40  Inferencing          : 0.13
% 2.95/1.40  Reduction            : 0.10
% 2.95/1.40  Demodulation         : 0.08
% 2.95/1.40  BG Simplification    : 0.02
% 2.95/1.40  Subsumption          : 0.08
% 2.95/1.41  Abstraction          : 0.02
% 2.95/1.41  MUC search           : 0.00
% 2.95/1.41  Cooper               : 0.00
% 2.95/1.41  Total                : 0.67
% 2.95/1.41  Index Insertion      : 0.00
% 2.95/1.41  Index Deletion       : 0.00
% 2.95/1.41  Index Matching       : 0.00
% 2.95/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
