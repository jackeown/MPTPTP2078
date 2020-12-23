%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:24 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   45 (  64 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 ( 104 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_49,axiom,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k3_xboole_0(A_13,B_14))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_35,plain,(
    ! [A_28,B_29] :
      ( k2_xboole_0(A_28,B_29) = B_29
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_43,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_35])).

tff(c_98,plain,(
    ! [A_38,B_39,C_40] : r1_tarski(k2_xboole_0(k3_xboole_0(A_38,B_39),k3_xboole_0(A_38,C_40)),k2_xboole_0(B_39,C_40)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_116,plain,(
    ! [A_38,B_39] : r1_tarski(k3_xboole_0(A_38,B_39),k2_xboole_0(B_39,B_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_98])).

tff(c_123,plain,(
    ! [A_38,B_39] : r1_tarski(k3_xboole_0(A_38,B_39),B_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_116])).

tff(c_1100,plain,(
    ! [A_93,B_94] :
      ( r1_tarski(k2_relat_1(A_93),k2_relat_1(B_94))
      | ~ r1_tarski(A_93,B_94)
      | ~ v1_relat_1(B_94)
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_614,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(k2_relat_1(A_70),k2_relat_1(B_71))
      | ~ r1_tarski(A_70,B_71)
      | ~ v1_relat_1(B_71)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_137,plain,(
    ! [A_43,B_44,C_45] :
      ( r1_tarski(A_43,k3_xboole_0(B_44,C_45))
      | ~ r1_tarski(A_43,C_45)
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_156,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_137,c_26])).

tff(c_253,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_156])).

tff(c_617,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_614,c_253])).

tff(c_628,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_10,c_617])).

tff(c_634,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_628])).

tff(c_638,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_634])).

tff(c_639,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_156])).

tff(c_1103,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1100,c_639])).

tff(c_1114,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_123,c_1103])).

tff(c_1120,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_16,c_1114])).

tff(c_1124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:40:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.36  
% 2.49/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.36  %$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.49/1.36  
% 2.49/1.36  %Foreground sorts:
% 2.49/1.36  
% 2.49/1.36  
% 2.49/1.36  %Background operators:
% 2.49/1.36  
% 2.49/1.36  
% 2.49/1.36  %Foreground operators:
% 2.49/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.49/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.49/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.49/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.49/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.49/1.36  
% 2.72/1.37  tff(f_79, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_relat_1)).
% 2.72/1.37  tff(f_49, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.72/1.37  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.72/1.37  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.72/1.37  tff(f_45, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.72/1.37  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.72/1.37  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.72/1.37  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.72/1.37  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.72/1.37  tff(c_16, plain, (![A_13, B_14]: (v1_relat_1(k3_xboole_0(A_13, B_14)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.72/1.37  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.72/1.37  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.37  tff(c_35, plain, (![A_28, B_29]: (k2_xboole_0(A_28, B_29)=B_29 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.72/1.37  tff(c_43, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_35])).
% 2.72/1.37  tff(c_98, plain, (![A_38, B_39, C_40]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_38, B_39), k3_xboole_0(A_38, C_40)), k2_xboole_0(B_39, C_40)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.72/1.37  tff(c_116, plain, (![A_38, B_39]: (r1_tarski(k3_xboole_0(A_38, B_39), k2_xboole_0(B_39, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_43, c_98])).
% 2.72/1.37  tff(c_123, plain, (![A_38, B_39]: (r1_tarski(k3_xboole_0(A_38, B_39), B_39))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_116])).
% 2.72/1.37  tff(c_1100, plain, (![A_93, B_94]: (r1_tarski(k2_relat_1(A_93), k2_relat_1(B_94)) | ~r1_tarski(A_93, B_94) | ~v1_relat_1(B_94) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.72/1.37  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.72/1.37  tff(c_614, plain, (![A_70, B_71]: (r1_tarski(k2_relat_1(A_70), k2_relat_1(B_71)) | ~r1_tarski(A_70, B_71) | ~v1_relat_1(B_71) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.72/1.37  tff(c_137, plain, (![A_43, B_44, C_45]: (r1_tarski(A_43, k3_xboole_0(B_44, C_45)) | ~r1_tarski(A_43, C_45) | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.72/1.37  tff(c_26, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.72/1.37  tff(c_156, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_137, c_26])).
% 2.72/1.37  tff(c_253, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_156])).
% 2.72/1.37  tff(c_617, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_614, c_253])).
% 2.72/1.37  tff(c_628, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_10, c_617])).
% 2.72/1.37  tff(c_634, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_628])).
% 2.72/1.37  tff(c_638, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_634])).
% 2.72/1.37  tff(c_639, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_156])).
% 2.72/1.37  tff(c_1103, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1100, c_639])).
% 2.72/1.37  tff(c_1114, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_123, c_1103])).
% 2.72/1.37  tff(c_1120, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_16, c_1114])).
% 2.72/1.37  tff(c_1124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_1120])).
% 2.72/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.37  
% 2.72/1.37  Inference rules
% 2.72/1.37  ----------------------
% 2.72/1.37  #Ref     : 0
% 2.72/1.37  #Sup     : 268
% 2.72/1.37  #Fact    : 0
% 2.72/1.37  #Define  : 0
% 2.72/1.37  #Split   : 1
% 2.72/1.37  #Chain   : 0
% 2.72/1.37  #Close   : 0
% 2.72/1.37  
% 2.72/1.37  Ordering : KBO
% 2.72/1.37  
% 2.72/1.37  Simplification rules
% 2.72/1.37  ----------------------
% 2.72/1.37  #Subsume      : 3
% 2.72/1.37  #Demod        : 193
% 2.72/1.37  #Tautology    : 181
% 2.72/1.37  #SimpNegUnit  : 0
% 2.72/1.37  #BackRed      : 0
% 2.72/1.37  
% 2.72/1.37  #Partial instantiations: 0
% 2.72/1.37  #Strategies tried      : 1
% 2.72/1.37  
% 2.72/1.37  Timing (in seconds)
% 2.72/1.37  ----------------------
% 2.72/1.37  Preprocessing        : 0.28
% 2.72/1.37  Parsing              : 0.16
% 2.72/1.37  CNF conversion       : 0.02
% 2.72/1.37  Main loop            : 0.33
% 2.72/1.37  Inferencing          : 0.13
% 2.72/1.37  Reduction            : 0.11
% 2.72/1.37  Demodulation         : 0.08
% 2.72/1.37  BG Simplification    : 0.02
% 2.72/1.37  Subsumption          : 0.06
% 2.72/1.37  Abstraction          : 0.02
% 2.72/1.37  MUC search           : 0.00
% 2.72/1.37  Cooper               : 0.00
% 2.72/1.37  Total                : 0.63
% 2.72/1.37  Index Insertion      : 0.00
% 2.72/1.37  Index Deletion       : 0.00
% 2.72/1.37  Index Matching       : 0.00
% 2.72/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
