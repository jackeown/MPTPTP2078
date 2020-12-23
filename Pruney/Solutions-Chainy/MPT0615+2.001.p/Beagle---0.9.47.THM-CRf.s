%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:48 EST 2020

% Result     : Theorem 4.82s
% Output     : CNFRefutation 4.82s
% Verified   : 
% Statistics : Number of formulae       :   49 (  61 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 110 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
            <=> r1_tarski(A,k7_relat_1(B,k1_relat_1(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t219_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_relat_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_40,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_73,plain,(
    r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_34,plain,
    ( ~ r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1')))
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_103,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_34])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_181,plain,(
    ! [A_72,B_73,C_74] :
      ( r1_tarski(A_72,k2_xboole_0(B_73,C_74))
      | ~ r1_tarski(k4_xboole_0(A_72,B_73),C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_207,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(B_7,A_6)) ),
    inference(resolution,[status(thm)],[c_10,c_181])).

tff(c_297,plain,(
    ! [B_92,A_93] :
      ( k7_relat_1(B_92,A_93) = B_92
      | ~ r1_tarski(k1_relat_1(B_92),A_93)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_333,plain,(
    ! [B_92,B_7] :
      ( k7_relat_1(B_92,k2_xboole_0(B_7,k1_relat_1(B_92))) = B_92
      | ~ v1_relat_1(B_92) ) ),
    inference(resolution,[status(thm)],[c_207,c_297])).

tff(c_1039,plain,(
    ! [C_196,A_197,B_198] :
      ( k2_xboole_0(k7_relat_1(C_196,A_197),k7_relat_1(C_196,B_198)) = k7_relat_1(C_196,k2_xboole_0(A_197,B_198))
      | ~ v1_relat_1(C_196) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1438,plain,(
    ! [C_259,A_260,B_261] :
      ( r1_tarski(k7_relat_1(C_259,A_260),k7_relat_1(C_259,k2_xboole_0(A_260,B_261)))
      | ~ v1_relat_1(C_259) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1039,c_14])).

tff(c_1473,plain,(
    ! [B_262,B_263] :
      ( r1_tarski(k7_relat_1(B_262,B_263),B_262)
      | ~ v1_relat_1(B_262)
      | ~ v1_relat_1(B_262) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_1438])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1650,plain,(
    ! [A_268,B_269,B_270] :
      ( r1_tarski(A_268,B_269)
      | ~ r1_tarski(A_268,k7_relat_1(B_269,B_270))
      | ~ v1_relat_1(B_269) ) ),
    inference(resolution,[status(thm)],[c_1473,c_8])).

tff(c_1683,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_73,c_1650])).

tff(c_1705,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1683])).

tff(c_1707,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_1705])).

tff(c_1708,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_28,plain,(
    ! [A_27] :
      ( k7_relat_1(A_27,k1_relat_1(A_27)) = A_27
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2070,plain,(
    ! [B_328,A_329,C_330] :
      ( r1_tarski(k7_relat_1(B_328,A_329),k7_relat_1(C_330,A_329))
      | ~ r1_tarski(B_328,C_330)
      | ~ v1_relat_1(C_330)
      | ~ v1_relat_1(B_328) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2814,plain,(
    ! [A_405,C_406] :
      ( r1_tarski(A_405,k7_relat_1(C_406,k1_relat_1(A_405)))
      | ~ r1_tarski(A_405,C_406)
      | ~ v1_relat_1(C_406)
      | ~ v1_relat_1(A_405)
      | ~ v1_relat_1(A_405) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2070])).

tff(c_1709,plain,(
    ~ r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_2839,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_2814,c_1709])).

tff(c_2859,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_1708,c_2839])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:38:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.82/1.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.96  
% 4.82/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.96  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.82/1.96  
% 4.82/1.96  %Foreground sorts:
% 4.82/1.96  
% 4.82/1.96  
% 4.82/1.96  %Background operators:
% 4.82/1.96  
% 4.82/1.96  
% 4.82/1.96  %Foreground operators:
% 4.82/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.82/1.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.82/1.96  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.82/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.82/1.96  tff('#skF_2', type, '#skF_2': $i).
% 4.82/1.96  tff('#skF_1', type, '#skF_1': $i).
% 4.82/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.82/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.82/1.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.82/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.82/1.96  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.82/1.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.82/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.82/1.96  
% 4.82/1.97  tff(f_89, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) <=> r1_tarski(A, k7_relat_1(B, k1_relat_1(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t219_relat_1)).
% 4.82/1.97  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.82/1.97  tff(f_43, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 4.82/1.97  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 4.82/1.97  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_relat_1)).
% 4.82/1.97  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.82/1.97  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.82/1.97  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 4.82/1.97  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_relat_1)).
% 4.82/1.97  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.82/1.97  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.82/1.97  tff(c_40, plain, (r1_tarski('#skF_1', '#skF_2') | r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.82/1.97  tff(c_73, plain, (r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(splitLeft, [status(thm)], [c_40])).
% 4.82/1.97  tff(c_34, plain, (~r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1'))) | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.82/1.97  tff(c_103, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_34])).
% 4.82/1.97  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.82/1.97  tff(c_181, plain, (![A_72, B_73, C_74]: (r1_tarski(A_72, k2_xboole_0(B_73, C_74)) | ~r1_tarski(k4_xboole_0(A_72, B_73), C_74))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.82/1.97  tff(c_207, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(B_7, A_6)))), inference(resolution, [status(thm)], [c_10, c_181])).
% 4.82/1.97  tff(c_297, plain, (![B_92, A_93]: (k7_relat_1(B_92, A_93)=B_92 | ~r1_tarski(k1_relat_1(B_92), A_93) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.82/1.97  tff(c_333, plain, (![B_92, B_7]: (k7_relat_1(B_92, k2_xboole_0(B_7, k1_relat_1(B_92)))=B_92 | ~v1_relat_1(B_92))), inference(resolution, [status(thm)], [c_207, c_297])).
% 4.82/1.97  tff(c_1039, plain, (![C_196, A_197, B_198]: (k2_xboole_0(k7_relat_1(C_196, A_197), k7_relat_1(C_196, B_198))=k7_relat_1(C_196, k2_xboole_0(A_197, B_198)) | ~v1_relat_1(C_196))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.82/1.97  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.82/1.97  tff(c_1438, plain, (![C_259, A_260, B_261]: (r1_tarski(k7_relat_1(C_259, A_260), k7_relat_1(C_259, k2_xboole_0(A_260, B_261))) | ~v1_relat_1(C_259))), inference(superposition, [status(thm), theory('equality')], [c_1039, c_14])).
% 4.82/1.97  tff(c_1473, plain, (![B_262, B_263]: (r1_tarski(k7_relat_1(B_262, B_263), B_262) | ~v1_relat_1(B_262) | ~v1_relat_1(B_262))), inference(superposition, [status(thm), theory('equality')], [c_333, c_1438])).
% 4.82/1.97  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.82/1.97  tff(c_1650, plain, (![A_268, B_269, B_270]: (r1_tarski(A_268, B_269) | ~r1_tarski(A_268, k7_relat_1(B_269, B_270)) | ~v1_relat_1(B_269))), inference(resolution, [status(thm)], [c_1473, c_8])).
% 4.82/1.97  tff(c_1683, plain, (r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_73, c_1650])).
% 4.82/1.97  tff(c_1705, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1683])).
% 4.82/1.97  tff(c_1707, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_1705])).
% 4.82/1.97  tff(c_1708, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_40])).
% 4.82/1.97  tff(c_28, plain, (![A_27]: (k7_relat_1(A_27, k1_relat_1(A_27))=A_27 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.82/1.97  tff(c_2070, plain, (![B_328, A_329, C_330]: (r1_tarski(k7_relat_1(B_328, A_329), k7_relat_1(C_330, A_329)) | ~r1_tarski(B_328, C_330) | ~v1_relat_1(C_330) | ~v1_relat_1(B_328))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.82/1.97  tff(c_2814, plain, (![A_405, C_406]: (r1_tarski(A_405, k7_relat_1(C_406, k1_relat_1(A_405))) | ~r1_tarski(A_405, C_406) | ~v1_relat_1(C_406) | ~v1_relat_1(A_405) | ~v1_relat_1(A_405))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2070])).
% 4.82/1.97  tff(c_1709, plain, (~r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(splitRight, [status(thm)], [c_40])).
% 4.82/1.97  tff(c_2839, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_2814, c_1709])).
% 4.82/1.97  tff(c_2859, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_1708, c_2839])).
% 4.82/1.97  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.82/1.97  
% 4.82/1.97  Inference rules
% 4.82/1.97  ----------------------
% 4.82/1.97  #Ref     : 0
% 4.82/1.97  #Sup     : 677
% 4.82/1.97  #Fact    : 0
% 4.82/1.97  #Define  : 0
% 4.82/1.97  #Split   : 5
% 4.82/1.97  #Chain   : 0
% 4.82/1.97  #Close   : 0
% 4.82/1.97  
% 4.82/1.97  Ordering : KBO
% 4.82/1.97  
% 4.82/1.97  Simplification rules
% 4.82/1.97  ----------------------
% 4.82/1.97  #Subsume      : 34
% 4.82/1.97  #Demod        : 123
% 4.82/1.97  #Tautology    : 105
% 4.82/1.97  #SimpNegUnit  : 1
% 4.82/1.97  #BackRed      : 0
% 4.82/1.97  
% 4.82/1.97  #Partial instantiations: 0
% 4.82/1.97  #Strategies tried      : 1
% 4.82/1.97  
% 4.82/1.97  Timing (in seconds)
% 4.82/1.97  ----------------------
% 4.82/1.97  Preprocessing        : 0.31
% 4.82/1.97  Parsing              : 0.17
% 4.82/1.97  CNF conversion       : 0.02
% 4.82/1.97  Main loop            : 0.84
% 4.82/1.97  Inferencing          : 0.28
% 4.82/1.97  Reduction            : 0.25
% 4.82/1.97  Demodulation         : 0.18
% 4.82/1.97  BG Simplification    : 0.03
% 4.82/1.97  Subsumption          : 0.21
% 4.82/1.97  Abstraction          : 0.04
% 4.82/1.97  MUC search           : 0.00
% 4.82/1.97  Cooper               : 0.00
% 4.82/1.97  Total                : 1.18
% 4.82/1.97  Index Insertion      : 0.00
% 5.12/1.97  Index Deletion       : 0.00
% 5.12/1.97  Index Matching       : 0.00
% 5.12/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
