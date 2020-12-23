%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:50 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   53 (  86 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 ( 147 expanded)
%              Number of equality atoms :   23 (  44 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k9_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_49,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_112,plain,(
    ! [B_21,A_22] :
      ( r1_xboole_0(k1_relat_1(B_21),A_22)
      | k7_relat_1(B_21,A_22) != k1_xboole_0
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k9_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_50,plain,(
    k9_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_12,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_51,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_28])).

tff(c_64,plain,(
    ! [B_15,A_16] :
      ( k7_relat_1(B_15,A_16) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_15),A_16)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_67,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_51,c_64])).

tff(c_73,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_67])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( k2_relat_1(k7_relat_1(B_6,A_5)) = k9_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_77,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_10])).

tff(c_84,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_12,c_77])).

tff(c_86,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_84])).

tff(c_87,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_118,plain,
    ( k7_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_112,c_87])).

tff(c_125,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_118])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( v1_relat_1(k7_relat_1(A_2,B_3))
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_88,plain,(
    k9_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_95,plain,(
    ! [B_17,A_18] :
      ( k2_relat_1(k7_relat_1(B_17,A_18)) = k9_relat_1(B_17,A_18)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [A_4] :
      ( ~ v1_xboole_0(k2_relat_1(A_4))
      | ~ v1_relat_1(A_4)
      | v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_126,plain,(
    ! [B_23,A_24] :
      ( ~ v1_xboole_0(k9_relat_1(B_23,A_24))
      | ~ v1_relat_1(k7_relat_1(B_23,A_24))
      | v1_xboole_0(k7_relat_1(B_23,A_24))
      | ~ v1_relat_1(B_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_8])).

tff(c_129,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | v1_xboole_0(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_126])).

tff(c_131,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | v1_xboole_0(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2,c_129])).

tff(c_132,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_135,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_132])).

tff(c_139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_135])).

tff(c_140,plain,(
    v1_xboole_0(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_144,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_140,c_4])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_144])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:28:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.17  
% 1.69/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.17  %$ r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.69/1.17  
% 1.69/1.17  %Foreground sorts:
% 1.69/1.17  
% 1.69/1.17  
% 1.69/1.17  %Background operators:
% 1.69/1.17  
% 1.69/1.17  
% 1.69/1.17  %Foreground operators:
% 1.69/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.17  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.69/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.69/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.69/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.69/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.69/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.69/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.69/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.69/1.17  
% 1.92/1.19  tff(f_62, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 1.92/1.19  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 1.92/1.19  tff(f_49, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.92/1.19  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.92/1.19  tff(f_34, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.92/1.19  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.92/1.19  tff(f_42, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 1.92/1.19  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 1.92/1.19  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.92/1.19  tff(c_112, plain, (![B_21, A_22]: (r1_xboole_0(k1_relat_1(B_21), A_22) | k7_relat_1(B_21, A_22)!=k1_xboole_0 | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.92/1.19  tff(c_22, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.92/1.19  tff(c_50, plain, (k9_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_22])).
% 1.92/1.19  tff(c_12, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.92/1.19  tff(c_28, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.92/1.19  tff(c_51, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_50, c_28])).
% 1.92/1.19  tff(c_64, plain, (![B_15, A_16]: (k7_relat_1(B_15, A_16)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_15), A_16) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.92/1.19  tff(c_67, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_51, c_64])).
% 1.92/1.19  tff(c_73, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_67])).
% 1.92/1.19  tff(c_10, plain, (![B_6, A_5]: (k2_relat_1(k7_relat_1(B_6, A_5))=k9_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.92/1.19  tff(c_77, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_73, c_10])).
% 1.92/1.19  tff(c_84, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_12, c_77])).
% 1.92/1.19  tff(c_86, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_84])).
% 1.92/1.19  tff(c_87, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_22])).
% 1.92/1.19  tff(c_118, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_112, c_87])).
% 1.92/1.19  tff(c_125, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_118])).
% 1.92/1.19  tff(c_6, plain, (![A_2, B_3]: (v1_relat_1(k7_relat_1(A_2, B_3)) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.92/1.19  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.92/1.19  tff(c_88, plain, (k9_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_22])).
% 1.92/1.19  tff(c_95, plain, (![B_17, A_18]: (k2_relat_1(k7_relat_1(B_17, A_18))=k9_relat_1(B_17, A_18) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.92/1.19  tff(c_8, plain, (![A_4]: (~v1_xboole_0(k2_relat_1(A_4)) | ~v1_relat_1(A_4) | v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.92/1.19  tff(c_126, plain, (![B_23, A_24]: (~v1_xboole_0(k9_relat_1(B_23, A_24)) | ~v1_relat_1(k7_relat_1(B_23, A_24)) | v1_xboole_0(k7_relat_1(B_23, A_24)) | ~v1_relat_1(B_23))), inference(superposition, [status(thm), theory('equality')], [c_95, c_8])).
% 1.92/1.19  tff(c_129, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | v1_xboole_0(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_88, c_126])).
% 1.92/1.19  tff(c_131, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | v1_xboole_0(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2, c_129])).
% 1.92/1.19  tff(c_132, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_131])).
% 1.92/1.19  tff(c_135, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6, c_132])).
% 1.92/1.19  tff(c_139, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_135])).
% 1.92/1.19  tff(c_140, plain, (v1_xboole_0(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_131])).
% 1.92/1.19  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.92/1.19  tff(c_144, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_140, c_4])).
% 1.92/1.19  tff(c_148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125, c_144])).
% 1.92/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.19  
% 1.92/1.19  Inference rules
% 1.92/1.19  ----------------------
% 1.92/1.19  #Ref     : 0
% 1.92/1.19  #Sup     : 27
% 1.92/1.19  #Fact    : 0
% 1.92/1.19  #Define  : 0
% 1.92/1.19  #Split   : 3
% 1.92/1.19  #Chain   : 0
% 1.92/1.19  #Close   : 0
% 1.92/1.19  
% 1.92/1.19  Ordering : KBO
% 1.92/1.19  
% 1.92/1.19  Simplification rules
% 1.92/1.19  ----------------------
% 1.92/1.19  #Subsume      : 1
% 1.92/1.19  #Demod        : 10
% 1.92/1.19  #Tautology    : 17
% 1.92/1.19  #SimpNegUnit  : 4
% 1.92/1.19  #BackRed      : 0
% 1.92/1.19  
% 1.92/1.19  #Partial instantiations: 0
% 1.92/1.19  #Strategies tried      : 1
% 1.92/1.19  
% 1.92/1.19  Timing (in seconds)
% 1.92/1.19  ----------------------
% 1.92/1.19  Preprocessing        : 0.27
% 1.92/1.19  Parsing              : 0.15
% 1.92/1.19  CNF conversion       : 0.02
% 1.92/1.19  Main loop            : 0.15
% 1.92/1.19  Inferencing          : 0.06
% 1.92/1.19  Reduction            : 0.04
% 1.92/1.19  Demodulation         : 0.03
% 1.92/1.19  BG Simplification    : 0.01
% 1.92/1.19  Subsumption          : 0.02
% 1.92/1.19  Abstraction          : 0.01
% 1.92/1.19  MUC search           : 0.00
% 1.92/1.19  Cooper               : 0.00
% 1.92/1.19  Total                : 0.45
% 1.92/1.19  Index Insertion      : 0.00
% 1.92/1.19  Index Deletion       : 0.00
% 1.92/1.19  Index Matching       : 0.00
% 1.92/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
