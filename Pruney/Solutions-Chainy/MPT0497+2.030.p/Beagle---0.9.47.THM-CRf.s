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
% DateTime   : Thu Dec  3 09:59:43 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 126 expanded)
%              Number of leaves         :   18 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :   75 ( 212 expanded)
%              Number of equality atoms :   38 (  92 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_58,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_18,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_69,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_18])).

tff(c_70,plain,(
    ! [B_18,A_19] :
      ( k3_xboole_0(k1_relat_1(B_18),A_19) = k1_relat_1(k7_relat_1(B_18,A_19))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_62,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_2])).

tff(c_76,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_62])).

tff(c_93,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_76])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k7_relat_1(A_4,B_5))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( k3_xboole_0(k1_relat_1(B_8),A_7) = k1_relat_1(k7_relat_1(B_8,A_7))
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_100,plain,(
    ! [A_7] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_7)) = k3_xboole_0(k1_xboole_0,A_7)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_14])).

tff(c_117,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_120,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_117])).

tff(c_124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_120])).

tff(c_126,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_12,plain,(
    ! [A_6] :
      ( k1_relat_1(A_6) != k1_xboole_0
      | k1_xboole_0 = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_132,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) != k1_xboole_0
    | k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_126,c_12])).

tff(c_138,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_132])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_138])).

tff(c_141,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_169,plain,(
    ! [B_21,A_22] :
      ( k3_xboole_0(k1_relat_1(B_21),A_22) = k1_relat_1(k7_relat_1(B_21,A_22))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_142,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_165,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_142])).

tff(c_175,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_165])).

tff(c_189,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_141,c_175])).

tff(c_146,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_8])).

tff(c_150,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_146])).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_186,plain,(
    ! [B_21] :
      ( k1_relat_1(k7_relat_1(B_21,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_169])).

tff(c_33,plain,(
    ! [A_12] :
      ( k1_relat_1(A_12) != k1_xboole_0
      | k1_xboole_0 = A_12
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_209,plain,(
    ! [A_26,B_27] :
      ( k1_relat_1(k7_relat_1(A_26,B_27)) != k1_xboole_0
      | k7_relat_1(A_26,B_27) = k1_xboole_0
      | ~ v1_relat_1(A_26) ) ),
    inference(resolution,[status(thm)],[c_8,c_33])).

tff(c_219,plain,(
    ! [B_28] :
      ( k7_relat_1(B_28,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_209])).

tff(c_229,plain,(
    k7_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_150,c_219])).

tff(c_241,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_186])).

tff(c_252,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_241])).

tff(c_254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_189,c_252])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.18  
% 1.80/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.18  %$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.80/1.18  
% 1.80/1.18  %Foreground sorts:
% 1.80/1.18  
% 1.80/1.18  
% 1.80/1.18  %Background operators:
% 1.80/1.18  
% 1.80/1.18  
% 1.80/1.18  %Foreground operators:
% 1.80/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.80/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.80/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.80/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.80/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.80/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.80/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.80/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.80/1.18  
% 1.80/1.19  tff(f_54, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 1.80/1.19  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 1.80/1.19  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.80/1.19  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.80/1.19  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 1.80/1.19  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.80/1.19  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.80/1.19  tff(c_24, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.80/1.19  tff(c_58, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_24])).
% 1.80/1.19  tff(c_18, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.80/1.19  tff(c_69, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_58, c_18])).
% 1.80/1.19  tff(c_70, plain, (![B_18, A_19]: (k3_xboole_0(k1_relat_1(B_18), A_19)=k1_relat_1(k7_relat_1(B_18, A_19)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.80/1.19  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.80/1.19  tff(c_62, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_2])).
% 1.80/1.19  tff(c_76, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_70, c_62])).
% 1.80/1.19  tff(c_93, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_76])).
% 1.80/1.19  tff(c_8, plain, (![A_4, B_5]: (v1_relat_1(k7_relat_1(A_4, B_5)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.80/1.19  tff(c_14, plain, (![B_8, A_7]: (k3_xboole_0(k1_relat_1(B_8), A_7)=k1_relat_1(k7_relat_1(B_8, A_7)) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.80/1.19  tff(c_100, plain, (![A_7]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_7))=k3_xboole_0(k1_xboole_0, A_7) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_93, c_14])).
% 1.80/1.19  tff(c_117, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_100])).
% 1.80/1.19  tff(c_120, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_117])).
% 1.80/1.19  tff(c_124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_120])).
% 1.80/1.19  tff(c_126, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_100])).
% 1.80/1.19  tff(c_12, plain, (![A_6]: (k1_relat_1(A_6)!=k1_xboole_0 | k1_xboole_0=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.80/1.19  tff(c_132, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))!=k1_xboole_0 | k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_126, c_12])).
% 1.80/1.19  tff(c_138, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_93, c_132])).
% 1.80/1.19  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_138])).
% 1.80/1.19  tff(c_141, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_24])).
% 1.80/1.19  tff(c_169, plain, (![B_21, A_22]: (k3_xboole_0(k1_relat_1(B_21), A_22)=k1_relat_1(k7_relat_1(B_21, A_22)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.80/1.19  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.80/1.19  tff(c_142, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_24])).
% 1.80/1.19  tff(c_165, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_142])).
% 1.80/1.19  tff(c_175, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_169, c_165])).
% 1.80/1.19  tff(c_189, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_141, c_175])).
% 1.80/1.19  tff(c_146, plain, (v1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_141, c_8])).
% 1.80/1.19  tff(c_150, plain, (v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_146])).
% 1.80/1.19  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.80/1.19  tff(c_186, plain, (![B_21]: (k1_relat_1(k7_relat_1(B_21, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_21))), inference(superposition, [status(thm), theory('equality')], [c_6, c_169])).
% 1.80/1.19  tff(c_33, plain, (![A_12]: (k1_relat_1(A_12)!=k1_xboole_0 | k1_xboole_0=A_12 | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.80/1.19  tff(c_209, plain, (![A_26, B_27]: (k1_relat_1(k7_relat_1(A_26, B_27))!=k1_xboole_0 | k7_relat_1(A_26, B_27)=k1_xboole_0 | ~v1_relat_1(A_26))), inference(resolution, [status(thm)], [c_8, c_33])).
% 1.80/1.19  tff(c_219, plain, (![B_28]: (k7_relat_1(B_28, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_28))), inference(superposition, [status(thm), theory('equality')], [c_186, c_209])).
% 1.80/1.19  tff(c_229, plain, (k7_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_150, c_219])).
% 1.80/1.19  tff(c_241, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_229, c_186])).
% 1.80/1.19  tff(c_252, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_150, c_241])).
% 1.80/1.19  tff(c_254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_189, c_252])).
% 1.80/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.19  
% 1.80/1.19  Inference rules
% 1.80/1.19  ----------------------
% 1.80/1.19  #Ref     : 0
% 1.80/1.19  #Sup     : 51
% 1.80/1.19  #Fact    : 0
% 1.80/1.19  #Define  : 0
% 1.80/1.19  #Split   : 5
% 1.80/1.19  #Chain   : 0
% 1.80/1.19  #Close   : 0
% 1.80/1.19  
% 1.80/1.19  Ordering : KBO
% 1.80/1.19  
% 1.80/1.19  Simplification rules
% 1.80/1.19  ----------------------
% 1.80/1.19  #Subsume      : 4
% 1.80/1.19  #Demod        : 19
% 1.80/1.19  #Tautology    : 25
% 1.80/1.19  #SimpNegUnit  : 3
% 1.80/1.19  #BackRed      : 0
% 1.80/1.19  
% 1.80/1.19  #Partial instantiations: 0
% 1.80/1.19  #Strategies tried      : 1
% 1.80/1.19  
% 1.80/1.19  Timing (in seconds)
% 1.80/1.19  ----------------------
% 1.80/1.20  Preprocessing        : 0.27
% 1.80/1.20  Parsing              : 0.14
% 1.80/1.20  CNF conversion       : 0.02
% 1.80/1.20  Main loop            : 0.16
% 1.80/1.20  Inferencing          : 0.06
% 1.80/1.20  Reduction            : 0.05
% 1.80/1.20  Demodulation         : 0.03
% 1.80/1.20  BG Simplification    : 0.01
% 1.80/1.20  Subsumption          : 0.03
% 1.80/1.20  Abstraction          : 0.01
% 1.80/1.20  MUC search           : 0.00
% 1.80/1.20  Cooper               : 0.00
% 1.80/1.20  Total                : 0.46
% 1.80/1.20  Index Insertion      : 0.00
% 1.80/1.20  Index Deletion       : 0.00
% 1.80/1.20  Index Matching       : 0.00
% 1.80/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
