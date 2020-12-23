%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:56 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   38 (  98 expanded)
%              Number of leaves         :   17 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   57 ( 196 expanded)
%              Number of equality atoms :   15 (  62 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => k9_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k2_relat_1(A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_relat_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( v1_relat_1(k7_relat_1(A_3,B_4))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [C_7,A_5,B_6] :
      ( k2_xboole_0(k7_relat_1(C_7,A_5),k7_relat_1(C_7,B_6)) = k7_relat_1(C_7,k2_xboole_0(A_5,B_6))
      | ~ v1_relat_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( k2_xboole_0(k2_relat_1(A_19),k2_relat_1(B_20)) = k2_relat_1(k2_xboole_0(A_19,B_20))
      | ~ v1_relat_1(B_20)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_54,plain,(
    ! [A_24,B_25,A_26] :
      ( k2_xboole_0(k2_relat_1(A_24),k9_relat_1(B_25,A_26)) = k2_relat_1(k2_xboole_0(A_24,k7_relat_1(B_25,A_26)))
      | ~ v1_relat_1(k7_relat_1(B_25,A_26))
      | ~ v1_relat_1(A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_30])).

tff(c_78,plain,(
    ! [B_30,A_31,B_32,A_33] :
      ( k2_relat_1(k2_xboole_0(k7_relat_1(B_30,A_31),k7_relat_1(B_32,A_33))) = k2_xboole_0(k9_relat_1(B_30,A_31),k9_relat_1(B_32,A_33))
      | ~ v1_relat_1(k7_relat_1(B_32,A_33))
      | ~ v1_relat_1(k7_relat_1(B_30,A_31))
      | ~ v1_relat_1(B_32)
      | ~ v1_relat_1(B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_54])).

tff(c_102,plain,(
    ! [C_34,A_35,B_36] :
      ( k2_xboole_0(k9_relat_1(C_34,A_35),k9_relat_1(C_34,B_36)) = k2_relat_1(k7_relat_1(C_34,k2_xboole_0(A_35,B_36)))
      | ~ v1_relat_1(k7_relat_1(C_34,B_36))
      | ~ v1_relat_1(k7_relat_1(C_34,A_35))
      | ~ v1_relat_1(C_34)
      | ~ v1_relat_1(C_34)
      | ~ v1_relat_1(C_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_78])).

tff(c_12,plain,(
    k2_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) != k9_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_108,plain,
    ( k2_relat_1(k7_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2'))) != k9_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_12])).

tff(c_114,plain,
    ( k2_relat_1(k7_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2'))) != k9_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_14,c_108])).

tff(c_116,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_114])).

tff(c_119,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_116])).

tff(c_123,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_119])).

tff(c_124,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | k2_relat_1(k7_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2'))) != k9_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_114])).

tff(c_144,plain,(
    k2_relat_1(k7_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2'))) != k9_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_147,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_144])).

tff(c_151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_147])).

tff(c_152,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_156,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_152])).

tff(c_160,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:03:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.17  
% 1.91/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.17  %$ v1_relat_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.91/1.17  
% 1.91/1.17  %Foreground sorts:
% 1.91/1.17  
% 1.91/1.17  
% 1.91/1.17  %Background operators:
% 1.91/1.17  
% 1.91/1.17  
% 1.91/1.17  %Foreground operators:
% 1.91/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.91/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.91/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.91/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.91/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.91/1.17  
% 1.91/1.18  tff(f_53, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (k9_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t153_relat_1)).
% 1.91/1.18  tff(f_33, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.91/1.18  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.91/1.18  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_relat_1)).
% 1.91/1.18  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_relat_1)).
% 1.91/1.18  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.91/1.18  tff(c_4, plain, (![A_3, B_4]: (v1_relat_1(k7_relat_1(A_3, B_4)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.91/1.18  tff(c_8, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.91/1.18  tff(c_6, plain, (![C_7, A_5, B_6]: (k2_xboole_0(k7_relat_1(C_7, A_5), k7_relat_1(C_7, B_6))=k7_relat_1(C_7, k2_xboole_0(A_5, B_6)) | ~v1_relat_1(C_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.91/1.18  tff(c_30, plain, (![A_19, B_20]: (k2_xboole_0(k2_relat_1(A_19), k2_relat_1(B_20))=k2_relat_1(k2_xboole_0(A_19, B_20)) | ~v1_relat_1(B_20) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.91/1.18  tff(c_54, plain, (![A_24, B_25, A_26]: (k2_xboole_0(k2_relat_1(A_24), k9_relat_1(B_25, A_26))=k2_relat_1(k2_xboole_0(A_24, k7_relat_1(B_25, A_26))) | ~v1_relat_1(k7_relat_1(B_25, A_26)) | ~v1_relat_1(A_24) | ~v1_relat_1(B_25))), inference(superposition, [status(thm), theory('equality')], [c_8, c_30])).
% 1.91/1.18  tff(c_78, plain, (![B_30, A_31, B_32, A_33]: (k2_relat_1(k2_xboole_0(k7_relat_1(B_30, A_31), k7_relat_1(B_32, A_33)))=k2_xboole_0(k9_relat_1(B_30, A_31), k9_relat_1(B_32, A_33)) | ~v1_relat_1(k7_relat_1(B_32, A_33)) | ~v1_relat_1(k7_relat_1(B_30, A_31)) | ~v1_relat_1(B_32) | ~v1_relat_1(B_30))), inference(superposition, [status(thm), theory('equality')], [c_8, c_54])).
% 1.91/1.18  tff(c_102, plain, (![C_34, A_35, B_36]: (k2_xboole_0(k9_relat_1(C_34, A_35), k9_relat_1(C_34, B_36))=k2_relat_1(k7_relat_1(C_34, k2_xboole_0(A_35, B_36))) | ~v1_relat_1(k7_relat_1(C_34, B_36)) | ~v1_relat_1(k7_relat_1(C_34, A_35)) | ~v1_relat_1(C_34) | ~v1_relat_1(C_34) | ~v1_relat_1(C_34))), inference(superposition, [status(thm), theory('equality')], [c_6, c_78])).
% 1.91/1.18  tff(c_12, plain, (k2_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))!=k9_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.91/1.18  tff(c_108, plain, (k2_relat_1(k7_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2')))!=k9_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_102, c_12])).
% 1.91/1.18  tff(c_114, plain, (k2_relat_1(k7_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2')))!=k9_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_14, c_108])).
% 1.91/1.18  tff(c_116, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_114])).
% 1.91/1.18  tff(c_119, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_116])).
% 1.91/1.18  tff(c_123, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_119])).
% 1.91/1.18  tff(c_124, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | k2_relat_1(k7_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2')))!=k9_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_114])).
% 1.91/1.18  tff(c_144, plain, (k2_relat_1(k7_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2')))!=k9_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_124])).
% 1.91/1.18  tff(c_147, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_144])).
% 1.91/1.18  tff(c_151, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_147])).
% 1.91/1.18  tff(c_152, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_124])).
% 1.91/1.18  tff(c_156, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_152])).
% 1.91/1.18  tff(c_160, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_156])).
% 1.91/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.18  
% 1.91/1.18  Inference rules
% 1.91/1.18  ----------------------
% 1.91/1.18  #Ref     : 1
% 1.91/1.18  #Sup     : 32
% 1.91/1.18  #Fact    : 0
% 1.91/1.18  #Define  : 0
% 1.91/1.18  #Split   : 2
% 1.91/1.18  #Chain   : 0
% 1.91/1.18  #Close   : 0
% 1.91/1.18  
% 1.91/1.18  Ordering : KBO
% 1.91/1.18  
% 1.91/1.18  Simplification rules
% 1.91/1.18  ----------------------
% 1.91/1.18  #Subsume      : 1
% 1.91/1.18  #Demod        : 6
% 1.91/1.18  #Tautology    : 17
% 1.91/1.18  #SimpNegUnit  : 0
% 1.91/1.18  #BackRed      : 0
% 1.91/1.18  
% 1.91/1.18  #Partial instantiations: 0
% 1.91/1.18  #Strategies tried      : 1
% 1.91/1.18  
% 1.91/1.18  Timing (in seconds)
% 1.91/1.19  ----------------------
% 1.91/1.19  Preprocessing        : 0.26
% 1.91/1.19  Parsing              : 0.14
% 1.91/1.19  CNF conversion       : 0.02
% 1.91/1.19  Main loop            : 0.18
% 1.91/1.19  Inferencing          : 0.08
% 1.91/1.19  Reduction            : 0.04
% 1.91/1.19  Demodulation         : 0.03
% 1.91/1.19  BG Simplification    : 0.01
% 1.91/1.19  Subsumption          : 0.04
% 1.91/1.19  Abstraction          : 0.01
% 1.91/1.19  MUC search           : 0.00
% 1.91/1.19  Cooper               : 0.00
% 1.91/1.19  Total                : 0.46
% 1.91/1.19  Index Insertion      : 0.00
% 1.91/1.19  Index Deletion       : 0.00
% 1.91/1.19  Index Matching       : 0.00
% 1.91/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
