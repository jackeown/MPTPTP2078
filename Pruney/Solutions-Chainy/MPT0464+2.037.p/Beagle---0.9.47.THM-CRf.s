%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:48 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   47 (  70 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   61 ( 124 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ! [C] :
                ( v1_relat_1(C)
               => r1_tarski(k5_relat_1(A,k3_xboole_0(B,C)),k3_xboole_0(k5_relat_1(A,B),k5_relat_1(A,C))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( r1_tarski(A,B)
               => r1_tarski(k5_relat_1(C,A),k5_relat_1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k3_xboole_0(A_13,B_14))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_33,plain,(
    ! [A_32,B_33] :
      ( k2_xboole_0(A_32,B_33) = B_33
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_41,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_33])).

tff(c_96,plain,(
    ! [A_42,B_43,C_44] : r1_tarski(k2_xboole_0(k3_xboole_0(A_42,B_43),k3_xboole_0(A_42,C_44)),k2_xboole_0(B_43,C_44)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_114,plain,(
    ! [A_42,B_43] : r1_tarski(k3_xboole_0(A_42,B_43),k2_xboole_0(B_43,B_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_41,c_96])).

tff(c_121,plain,(
    ! [A_42,B_43] : r1_tarski(k3_xboole_0(A_42,B_43),B_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_114])).

tff(c_20,plain,(
    ! [C_22,A_16,B_20] :
      ( r1_tarski(k5_relat_1(C_22,A_16),k5_relat_1(C_22,B_20))
      | ~ r1_tarski(A_16,B_20)
      | ~ v1_relat_1(C_22)
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_134,plain,(
    ! [A_47,B_48,C_49] :
      ( r1_tarski(A_47,k3_xboole_0(B_48,C_49))
      | ~ r1_tarski(A_47,C_49)
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k3_xboole_0(k5_relat_1('#skF_1','#skF_2'),k5_relat_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_154,plain,
    ( ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_3'))
    | ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_134,c_22])).

tff(c_208,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_154])).

tff(c_614,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_208])).

tff(c_617,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_10,c_614])).

tff(c_620,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_617])).

tff(c_624,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_620])).

tff(c_625,plain,(
    ~ r1_tarski(k5_relat_1('#skF_1',k3_xboole_0('#skF_2','#skF_3')),k5_relat_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_154])).

tff(c_1192,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_2','#skF_3'),'#skF_3')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_625])).

tff(c_1195,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28,c_121,c_1192])).

tff(c_1198,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_1195])).

tff(c_1202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:50:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.41  
% 2.72/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.41  %$ r1_tarski > v1_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.72/1.41  
% 2.72/1.41  %Foreground sorts:
% 2.72/1.41  
% 2.72/1.41  
% 2.72/1.41  %Background operators:
% 2.72/1.41  
% 2.72/1.41  
% 2.72/1.41  %Foreground operators:
% 2.72/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.41  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.72/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.72/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.72/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.72/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.72/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.72/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.72/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.72/1.41  
% 2.72/1.42  tff(f_76, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => r1_tarski(k5_relat_1(A, k3_xboole_0(B, C)), k3_xboole_0(k5_relat_1(A, B), k5_relat_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relat_1)).
% 2.72/1.42  tff(f_49, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.72/1.42  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.72/1.42  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.72/1.42  tff(f_45, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.72/1.42  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k5_relat_1(C, A), k5_relat_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_relat_1)).
% 2.72/1.42  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.72/1.42  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.72/1.42  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.72/1.42  tff(c_16, plain, (![A_13, B_14]: (v1_relat_1(k3_xboole_0(A_13, B_14)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.72/1.42  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.72/1.42  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.72/1.42  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.42  tff(c_33, plain, (![A_32, B_33]: (k2_xboole_0(A_32, B_33)=B_33 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.72/1.42  tff(c_41, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_33])).
% 2.72/1.42  tff(c_96, plain, (![A_42, B_43, C_44]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_42, B_43), k3_xboole_0(A_42, C_44)), k2_xboole_0(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.72/1.42  tff(c_114, plain, (![A_42, B_43]: (r1_tarski(k3_xboole_0(A_42, B_43), k2_xboole_0(B_43, B_43)))), inference(superposition, [status(thm), theory('equality')], [c_41, c_96])).
% 2.72/1.42  tff(c_121, plain, (![A_42, B_43]: (r1_tarski(k3_xboole_0(A_42, B_43), B_43))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_114])).
% 2.72/1.42  tff(c_20, plain, (![C_22, A_16, B_20]: (r1_tarski(k5_relat_1(C_22, A_16), k5_relat_1(C_22, B_20)) | ~r1_tarski(A_16, B_20) | ~v1_relat_1(C_22) | ~v1_relat_1(B_20) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.72/1.42  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.72/1.42  tff(c_134, plain, (![A_47, B_48, C_49]: (r1_tarski(A_47, k3_xboole_0(B_48, C_49)) | ~r1_tarski(A_47, C_49) | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.72/1.42  tff(c_22, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k3_xboole_0(k5_relat_1('#skF_1', '#skF_2'), k5_relat_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.72/1.42  tff(c_154, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_3')) | ~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_134, c_22])).
% 2.72/1.42  tff(c_208, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_154])).
% 2.72/1.42  tff(c_614, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_2') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_208])).
% 2.72/1.42  tff(c_617, plain, (~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_10, c_614])).
% 2.72/1.42  tff(c_620, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_617])).
% 2.72/1.42  tff(c_624, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_620])).
% 2.72/1.42  tff(c_625, plain, (~r1_tarski(k5_relat_1('#skF_1', k3_xboole_0('#skF_2', '#skF_3')), k5_relat_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_154])).
% 2.72/1.42  tff(c_1192, plain, (~r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), '#skF_3') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_625])).
% 2.72/1.42  tff(c_1195, plain, (~v1_relat_1(k3_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28, c_121, c_1192])).
% 2.72/1.42  tff(c_1198, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_1195])).
% 2.72/1.42  tff(c_1202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1198])).
% 2.72/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.42  
% 2.72/1.42  Inference rules
% 2.72/1.42  ----------------------
% 2.72/1.42  #Ref     : 0
% 2.72/1.42  #Sup     : 287
% 2.72/1.42  #Fact    : 0
% 2.72/1.42  #Define  : 0
% 2.72/1.42  #Split   : 1
% 2.72/1.42  #Chain   : 0
% 2.72/1.42  #Close   : 0
% 2.72/1.42  
% 2.72/1.42  Ordering : KBO
% 2.72/1.42  
% 2.72/1.42  Simplification rules
% 2.72/1.42  ----------------------
% 2.72/1.42  #Subsume      : 3
% 2.72/1.42  #Demod        : 214
% 2.72/1.42  #Tautology    : 201
% 2.72/1.42  #SimpNegUnit  : 0
% 2.72/1.42  #BackRed      : 0
% 2.72/1.42  
% 2.72/1.42  #Partial instantiations: 0
% 2.72/1.42  #Strategies tried      : 1
% 2.72/1.42  
% 2.72/1.42  Timing (in seconds)
% 2.72/1.42  ----------------------
% 2.72/1.43  Preprocessing        : 0.29
% 2.72/1.43  Parsing              : 0.17
% 2.72/1.43  CNF conversion       : 0.02
% 2.72/1.43  Main loop            : 0.37
% 2.72/1.43  Inferencing          : 0.14
% 2.72/1.43  Reduction            : 0.12
% 2.72/1.43  Demodulation         : 0.09
% 2.72/1.43  BG Simplification    : 0.02
% 2.72/1.43  Subsumption          : 0.06
% 2.72/1.43  Abstraction          : 0.02
% 2.72/1.43  MUC search           : 0.00
% 2.72/1.43  Cooper               : 0.00
% 2.72/1.43  Total                : 0.69
% 2.72/1.43  Index Insertion      : 0.00
% 2.72/1.43  Index Deletion       : 0.00
% 2.72/1.43  Index Matching       : 0.00
% 2.72/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
