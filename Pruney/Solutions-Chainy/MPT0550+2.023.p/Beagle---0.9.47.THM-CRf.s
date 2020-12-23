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
% DateTime   : Thu Dec  3 10:00:54 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   51 (  95 expanded)
%              Number of leaves         :   20 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   67 ( 183 expanded)
%              Number of equality atoms :   36 (  89 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k1_relat_1(B))
            & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( k2_relat_1(k7_relat_1(B_5,A_4)) = k9_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( v1_relat_1(k7_relat_1(A_2,B_3))
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_134,plain,(
    ! [B_22,A_23] :
      ( k1_relat_1(k7_relat_1(B_22,A_23)) = A_23
      | ~ r1_tarski(A_23,k1_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_140,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_134])).

tff(c_145,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_140])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( k1_relat_1(k7_relat_1(B_9,A_8)) = A_8
      | ~ r1_tarski(A_8,k1_relat_1(B_9))
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_149,plain,(
    ! [A_8] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_8)) = A_8
      | ~ r1_tarski(A_8,'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_16])).

tff(c_238,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_241,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_238])).

tff(c_245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_241])).

tff(c_247,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_8,plain,(
    ! [A_6] :
      ( k2_relat_1(A_6) != k1_xboole_0
      | k1_xboole_0 = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_256,plain,
    ( k2_relat_1(k7_relat_1('#skF_2','#skF_1')) != k1_xboole_0
    | k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_247,c_8])).

tff(c_257,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_260,plain,
    ( k9_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_257])).

tff(c_263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_260])).

tff(c_264,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_267,plain,(
    k1_relat_1(k1_xboole_0) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_145])).

tff(c_14,plain,(
    ! [A_7] : k2_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_49,plain,(
    ! [A_15] :
      ( k2_relat_1(A_15) != k1_xboole_0
      | k1_xboole_0 = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_55,plain,(
    ! [A_1] :
      ( k2_relat_1(k6_relat_1(A_1)) != k1_xboole_0
      | k6_relat_1(A_1) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_49])).

tff(c_65,plain,(
    ! [A_16] :
      ( k1_xboole_0 != A_16
      | k6_relat_1(A_16) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_55])).

tff(c_12,plain,(
    ! [A_7] : k1_relat_1(k6_relat_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_71,plain,(
    ! [A_16] :
      ( k1_relat_1(k1_xboole_0) = A_16
      | k1_xboole_0 != A_16 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_12])).

tff(c_321,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_71])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_340,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:01:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.22  
% 1.97/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.22  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.97/1.22  
% 1.97/1.22  %Foreground sorts:
% 1.97/1.22  
% 1.97/1.22  
% 1.97/1.22  %Background operators:
% 1.97/1.22  
% 1.97/1.22  
% 1.97/1.22  %Foreground operators:
% 1.97/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.97/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.97/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.97/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.97/1.22  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.97/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.97/1.22  
% 2.10/1.23  tff(f_64, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 2.10/1.23  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.10/1.23  tff(f_31, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.10/1.23  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 2.10/1.23  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.10/1.23  tff(f_47, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.10/1.23  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.10/1.23  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.10/1.23  tff(c_18, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.10/1.23  tff(c_6, plain, (![B_5, A_4]: (k2_relat_1(k7_relat_1(B_5, A_4))=k9_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.10/1.23  tff(c_4, plain, (![A_2, B_3]: (v1_relat_1(k7_relat_1(A_2, B_3)) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.23  tff(c_20, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.10/1.23  tff(c_134, plain, (![B_22, A_23]: (k1_relat_1(k7_relat_1(B_22, A_23))=A_23 | ~r1_tarski(A_23, k1_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.10/1.23  tff(c_140, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_20, c_134])).
% 2.10/1.23  tff(c_145, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_140])).
% 2.10/1.23  tff(c_16, plain, (![B_9, A_8]: (k1_relat_1(k7_relat_1(B_9, A_8))=A_8 | ~r1_tarski(A_8, k1_relat_1(B_9)) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.10/1.23  tff(c_149, plain, (![A_8]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_8))=A_8 | ~r1_tarski(A_8, '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_145, c_16])).
% 2.10/1.23  tff(c_238, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_149])).
% 2.10/1.23  tff(c_241, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4, c_238])).
% 2.10/1.23  tff(c_245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_241])).
% 2.10/1.23  tff(c_247, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_149])).
% 2.10/1.23  tff(c_8, plain, (![A_6]: (k2_relat_1(A_6)!=k1_xboole_0 | k1_xboole_0=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.10/1.23  tff(c_256, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))!=k1_xboole_0 | k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_247, c_8])).
% 2.10/1.23  tff(c_257, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_256])).
% 2.10/1.23  tff(c_260, plain, (k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6, c_257])).
% 2.10/1.23  tff(c_263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_260])).
% 2.10/1.23  tff(c_264, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_256])).
% 2.10/1.23  tff(c_267, plain, (k1_relat_1(k1_xboole_0)='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_264, c_145])).
% 2.10/1.23  tff(c_14, plain, (![A_7]: (k2_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.10/1.23  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.23  tff(c_49, plain, (![A_15]: (k2_relat_1(A_15)!=k1_xboole_0 | k1_xboole_0=A_15 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.10/1.23  tff(c_55, plain, (![A_1]: (k2_relat_1(k6_relat_1(A_1))!=k1_xboole_0 | k6_relat_1(A_1)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_49])).
% 2.10/1.23  tff(c_65, plain, (![A_16]: (k1_xboole_0!=A_16 | k6_relat_1(A_16)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_55])).
% 2.10/1.23  tff(c_12, plain, (![A_7]: (k1_relat_1(k6_relat_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.10/1.23  tff(c_71, plain, (![A_16]: (k1_relat_1(k1_xboole_0)=A_16 | k1_xboole_0!=A_16)), inference(superposition, [status(thm), theory('equality')], [c_65, c_12])).
% 2.10/1.23  tff(c_321, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_267, c_71])).
% 2.10/1.23  tff(c_22, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.10/1.23  tff(c_340, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_321, c_22])).
% 2.10/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.23  
% 2.10/1.23  Inference rules
% 2.10/1.23  ----------------------
% 2.10/1.23  #Ref     : 2
% 2.10/1.23  #Sup     : 62
% 2.10/1.23  #Fact    : 0
% 2.10/1.23  #Define  : 0
% 2.10/1.23  #Split   : 5
% 2.10/1.23  #Chain   : 0
% 2.10/1.23  #Close   : 0
% 2.10/1.23  
% 2.10/1.23  Ordering : KBO
% 2.10/1.23  
% 2.10/1.23  Simplification rules
% 2.10/1.23  ----------------------
% 2.10/1.23  #Subsume      : 11
% 2.10/1.23  #Demod        : 65
% 2.10/1.23  #Tautology    : 35
% 2.10/1.23  #SimpNegUnit  : 3
% 2.10/1.23  #BackRed      : 21
% 2.10/1.23  
% 2.10/1.23  #Partial instantiations: 0
% 2.10/1.23  #Strategies tried      : 1
% 2.10/1.23  
% 2.10/1.23  Timing (in seconds)
% 2.10/1.23  ----------------------
% 2.12/1.24  Preprocessing        : 0.27
% 2.12/1.24  Parsing              : 0.15
% 2.12/1.24  CNF conversion       : 0.02
% 2.12/1.24  Main loop            : 0.20
% 2.12/1.24  Inferencing          : 0.07
% 2.12/1.24  Reduction            : 0.06
% 2.12/1.24  Demodulation         : 0.05
% 2.12/1.24  BG Simplification    : 0.01
% 2.12/1.24  Subsumption          : 0.03
% 2.12/1.24  Abstraction          : 0.01
% 2.12/1.24  MUC search           : 0.00
% 2.12/1.24  Cooper               : 0.00
% 2.12/1.24  Total                : 0.49
% 2.12/1.24  Index Insertion      : 0.00
% 2.12/1.24  Index Deletion       : 0.00
% 2.12/1.24  Index Matching       : 0.00
% 2.12/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
