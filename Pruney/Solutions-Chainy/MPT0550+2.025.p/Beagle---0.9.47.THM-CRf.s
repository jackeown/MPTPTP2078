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
% DateTime   : Thu Dec  3 10:00:55 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 104 expanded)
%              Number of leaves         :   22 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   71 ( 175 expanded)
%              Number of equality atoms :   26 (  69 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k1_relat_1(B))
            & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_50,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_37,plain,(
    ! [A_9] :
      ( k1_xboole_0 = A_9
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_37])).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_46,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_22])).

tff(c_14,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_45,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_41,c_14])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( v1_relat_1(k7_relat_1(A_2,B_3))
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_88,plain,(
    ! [B_16,A_17] :
      ( k1_relat_1(k7_relat_1(B_16,A_17)) = A_17
      | ~ r1_tarski(A_17,k1_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_94,plain,
    ( k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_88])).

tff(c_97,plain,(
    k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_94])).

tff(c_16,plain,(
    ! [B_8,A_7] :
      ( k1_relat_1(k7_relat_1(B_8,A_7)) = A_7
      | ~ r1_tarski(A_7,k1_relat_1(B_8))
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_101,plain,(
    ! [A_7] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_3','#skF_2'),A_7)) = A_7
      | ~ r1_tarski(A_7,'#skF_2')
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_16])).

tff(c_105,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_108,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_105])).

tff(c_112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_108])).

tff(c_114,plain,(
    v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_18,plain,(
    k9_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_43,plain,(
    k9_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_18])).

tff(c_76,plain,(
    ! [B_14,A_15] :
      ( k2_relat_1(k7_relat_1(B_14,A_15)) = k9_relat_1(B_14,A_15)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_4] :
      ( ~ v1_xboole_0(k2_relat_1(A_4))
      | ~ v1_relat_1(A_4)
      | v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_171,plain,(
    ! [B_23,A_24] :
      ( ~ v1_xboole_0(k9_relat_1(B_23,A_24))
      | ~ v1_relat_1(k7_relat_1(B_23,A_24))
      | v1_xboole_0(k7_relat_1(B_23,A_24))
      | ~ v1_relat_1(B_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_8])).

tff(c_174,plain,
    ( ~ v1_xboole_0('#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | v1_xboole_0(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_171])).

tff(c_176,plain,(
    v1_xboole_0(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_114,c_4,c_174])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_2])).

tff(c_180,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_176,c_42])).

tff(c_184,plain,(
    k1_relat_1('#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_97])).

tff(c_187,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_184])).

tff(c_189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_187])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:29:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.25  
% 1.91/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.25  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.91/1.25  
% 1.91/1.25  %Foreground sorts:
% 1.91/1.25  
% 1.91/1.25  
% 1.91/1.25  %Background operators:
% 1.91/1.25  
% 1.91/1.25  
% 1.91/1.25  %Foreground operators:
% 1.91/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.91/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.91/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.91/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.25  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.91/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.91/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.91/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.91/1.25  
% 2.00/1.26  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.00/1.26  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.00/1.26  tff(f_67, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 2.00/1.26  tff(f_50, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.00/1.26  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.00/1.26  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 2.00/1.26  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.00/1.26  tff(f_43, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.00/1.26  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.00/1.26  tff(c_37, plain, (![A_9]: (k1_xboole_0=A_9 | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.26  tff(c_41, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_37])).
% 2.00/1.26  tff(c_22, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.00/1.26  tff(c_46, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_41, c_22])).
% 2.00/1.26  tff(c_14, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.00/1.26  tff(c_45, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_41, c_41, c_14])).
% 2.00/1.26  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.00/1.26  tff(c_6, plain, (![A_2, B_3]: (v1_relat_1(k7_relat_1(A_2, B_3)) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.00/1.26  tff(c_20, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.00/1.26  tff(c_88, plain, (![B_16, A_17]: (k1_relat_1(k7_relat_1(B_16, A_17))=A_17 | ~r1_tarski(A_17, k1_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.00/1.26  tff(c_94, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_20, c_88])).
% 2.00/1.26  tff(c_97, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_94])).
% 2.00/1.26  tff(c_16, plain, (![B_8, A_7]: (k1_relat_1(k7_relat_1(B_8, A_7))=A_7 | ~r1_tarski(A_7, k1_relat_1(B_8)) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.00/1.26  tff(c_101, plain, (![A_7]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), A_7))=A_7 | ~r1_tarski(A_7, '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_97, c_16])).
% 2.00/1.26  tff(c_105, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_101])).
% 2.00/1.26  tff(c_108, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_105])).
% 2.00/1.26  tff(c_112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_108])).
% 2.00/1.26  tff(c_114, plain, (v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_101])).
% 2.00/1.26  tff(c_18, plain, (k9_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.00/1.26  tff(c_43, plain, (k9_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_41, c_18])).
% 2.00/1.26  tff(c_76, plain, (![B_14, A_15]: (k2_relat_1(k7_relat_1(B_14, A_15))=k9_relat_1(B_14, A_15) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.00/1.26  tff(c_8, plain, (![A_4]: (~v1_xboole_0(k2_relat_1(A_4)) | ~v1_relat_1(A_4) | v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.00/1.26  tff(c_171, plain, (![B_23, A_24]: (~v1_xboole_0(k9_relat_1(B_23, A_24)) | ~v1_relat_1(k7_relat_1(B_23, A_24)) | v1_xboole_0(k7_relat_1(B_23, A_24)) | ~v1_relat_1(B_23))), inference(superposition, [status(thm), theory('equality')], [c_76, c_8])).
% 2.00/1.26  tff(c_174, plain, (~v1_xboole_0('#skF_1') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | v1_xboole_0(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_43, c_171])).
% 2.00/1.26  tff(c_176, plain, (v1_xboole_0(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_114, c_4, c_174])).
% 2.00/1.26  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.26  tff(c_42, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_2])).
% 2.00/1.26  tff(c_180, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_176, c_42])).
% 2.00/1.26  tff(c_184, plain, (k1_relat_1('#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_180, c_97])).
% 2.00/1.26  tff(c_187, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_45, c_184])).
% 2.00/1.26  tff(c_189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_187])).
% 2.00/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.26  
% 2.00/1.26  Inference rules
% 2.00/1.26  ----------------------
% 2.00/1.26  #Ref     : 0
% 2.00/1.26  #Sup     : 39
% 2.00/1.26  #Fact    : 0
% 2.00/1.26  #Define  : 0
% 2.00/1.26  #Split   : 2
% 2.00/1.26  #Chain   : 0
% 2.00/1.26  #Close   : 0
% 2.00/1.26  
% 2.00/1.26  Ordering : KBO
% 2.00/1.26  
% 2.00/1.26  Simplification rules
% 2.00/1.26  ----------------------
% 2.00/1.26  #Subsume      : 0
% 2.00/1.26  #Demod        : 29
% 2.00/1.26  #Tautology    : 29
% 2.00/1.26  #SimpNegUnit  : 2
% 2.00/1.26  #BackRed      : 13
% 2.00/1.26  
% 2.00/1.26  #Partial instantiations: 0
% 2.00/1.26  #Strategies tried      : 1
% 2.00/1.26  
% 2.00/1.26  Timing (in seconds)
% 2.00/1.26  ----------------------
% 2.00/1.27  Preprocessing        : 0.29
% 2.00/1.27  Parsing              : 0.16
% 2.00/1.27  CNF conversion       : 0.02
% 2.00/1.27  Main loop            : 0.16
% 2.00/1.27  Inferencing          : 0.06
% 2.00/1.27  Reduction            : 0.05
% 2.00/1.27  Demodulation         : 0.04
% 2.00/1.27  BG Simplification    : 0.01
% 2.00/1.27  Subsumption          : 0.03
% 2.00/1.27  Abstraction          : 0.01
% 2.00/1.27  MUC search           : 0.00
% 2.00/1.27  Cooper               : 0.00
% 2.00/1.27  Total                : 0.48
% 2.00/1.27  Index Insertion      : 0.00
% 2.00/1.27  Index Deletion       : 0.00
% 2.00/1.27  Index Matching       : 0.00
% 2.00/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
