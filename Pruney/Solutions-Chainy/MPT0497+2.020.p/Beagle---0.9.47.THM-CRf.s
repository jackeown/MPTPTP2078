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
% DateTime   : Thu Dec  3 09:59:42 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   51 (  64 expanded)
%              Number of leaves         :   25 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 (  93 expanded)
%              Number of equality atoms :   27 (  38 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_40,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_37,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_xboole_0(k2_relat_1(A),k1_relat_1(B))
           => k5_relat_1(A,B) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_28,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1')
    | k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_73,plain,(
    k7_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_34,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_90,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_34])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_97,plain,(
    r1_xboole_0('#skF_1',k1_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_90,c_6])).

tff(c_10,plain,(
    ! [A_7] : v1_relat_1(k6_relat_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ! [A_11] : k2_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_182,plain,(
    ! [A_37,B_38] :
      ( k5_relat_1(A_37,B_38) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(A_37),k1_relat_1(B_38))
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_200,plain,(
    ! [A_11,B_38] :
      ( k5_relat_1(k6_relat_1(A_11),B_38) = k1_xboole_0
      | ~ r1_xboole_0(A_11,k1_relat_1(B_38))
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(k6_relat_1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_182])).

tff(c_285,plain,(
    ! [A_47,B_48] :
      ( k5_relat_1(k6_relat_1(A_47),B_48) = k1_xboole_0
      | ~ r1_xboole_0(A_47,k1_relat_1(B_48))
      | ~ v1_relat_1(B_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_200])).

tff(c_294,plain,
    ( k5_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_97,c_285])).

tff(c_311,plain,(
    k5_relat_1(k6_relat_1('#skF_1'),'#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_294])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( k5_relat_1(k6_relat_1(A_14),B_15) = k7_relat_1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_319,plain,
    ( k7_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_24])).

tff(c_326,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_319])).

tff(c_328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_326])).

tff(c_330,plain,(
    k7_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_371,plain,(
    ! [B_57,A_58] :
      ( k3_xboole_0(k1_relat_1(B_57),A_58) = k1_relat_1(k7_relat_1(B_57,A_58))
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_335,plain,(
    ! [A_49,B_50] :
      ( r1_xboole_0(A_49,B_50)
      | k3_xboole_0(A_49,B_50) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_329,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_344,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_335,c_329])).

tff(c_379,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_344])).

tff(c_392,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_14,c_330,c_379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:10:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.42  
% 2.23/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.42  %$ r1_xboole_0 > v1_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.23/1.42  
% 2.23/1.42  %Foreground sorts:
% 2.23/1.42  
% 2.23/1.42  
% 2.23/1.42  %Background operators:
% 2.23/1.42  
% 2.23/1.42  
% 2.23/1.42  %Foreground operators:
% 2.23/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.23/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.23/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.23/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.42  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.23/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.23/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.23/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.23/1.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.23/1.42  
% 2.23/1.43  tff(f_68, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 2.23/1.43  tff(f_40, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.23/1.43  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.23/1.43  tff(f_37, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.23/1.43  tff(f_53, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.23/1.43  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k1_relat_1(B)) => (k5_relat_1(A, B) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_relat_1)).
% 2.23/1.43  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.23/1.43  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.23/1.43  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.23/1.43  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.23/1.43  tff(c_14, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.23/1.43  tff(c_28, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1') | k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.23/1.43  tff(c_73, plain, (k7_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_28])).
% 2.23/1.43  tff(c_34, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.23/1.43  tff(c_90, plain, (r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_73, c_34])).
% 2.23/1.43  tff(c_6, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.23/1.43  tff(c_97, plain, (r1_xboole_0('#skF_1', k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_90, c_6])).
% 2.23/1.43  tff(c_10, plain, (![A_7]: (v1_relat_1(k6_relat_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.23/1.43  tff(c_20, plain, (![A_11]: (k2_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.23/1.43  tff(c_182, plain, (![A_37, B_38]: (k5_relat_1(A_37, B_38)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(A_37), k1_relat_1(B_38)) | ~v1_relat_1(B_38) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.23/1.43  tff(c_200, plain, (![A_11, B_38]: (k5_relat_1(k6_relat_1(A_11), B_38)=k1_xboole_0 | ~r1_xboole_0(A_11, k1_relat_1(B_38)) | ~v1_relat_1(B_38) | ~v1_relat_1(k6_relat_1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_182])).
% 2.23/1.43  tff(c_285, plain, (![A_47, B_48]: (k5_relat_1(k6_relat_1(A_47), B_48)=k1_xboole_0 | ~r1_xboole_0(A_47, k1_relat_1(B_48)) | ~v1_relat_1(B_48))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_200])).
% 2.23/1.43  tff(c_294, plain, (k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_97, c_285])).
% 2.23/1.43  tff(c_311, plain, (k5_relat_1(k6_relat_1('#skF_1'), '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_294])).
% 2.23/1.43  tff(c_24, plain, (![A_14, B_15]: (k5_relat_1(k6_relat_1(A_14), B_15)=k7_relat_1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.23/1.43  tff(c_319, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_311, c_24])).
% 2.23/1.43  tff(c_326, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_319])).
% 2.23/1.43  tff(c_328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_326])).
% 2.23/1.43  tff(c_330, plain, (k7_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 2.23/1.43  tff(c_371, plain, (![B_57, A_58]: (k3_xboole_0(k1_relat_1(B_57), A_58)=k1_relat_1(k7_relat_1(B_57, A_58)) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.23/1.43  tff(c_335, plain, (![A_49, B_50]: (r1_xboole_0(A_49, B_50) | k3_xboole_0(A_49, B_50)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.43  tff(c_329, plain, (~r1_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_28])).
% 2.23/1.43  tff(c_344, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_335, c_329])).
% 2.23/1.43  tff(c_379, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_371, c_344])).
% 2.23/1.43  tff(c_392, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_14, c_330, c_379])).
% 2.23/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.23/1.43  
% 2.23/1.43  Inference rules
% 2.23/1.43  ----------------------
% 2.23/1.43  #Ref     : 0
% 2.23/1.43  #Sup     : 89
% 2.23/1.43  #Fact    : 0
% 2.23/1.43  #Define  : 0
% 2.23/1.43  #Split   : 3
% 2.23/1.43  #Chain   : 0
% 2.23/1.43  #Close   : 0
% 2.23/1.43  
% 2.23/1.43  Ordering : KBO
% 2.23/1.43  
% 2.23/1.43  Simplification rules
% 2.23/1.43  ----------------------
% 2.23/1.43  #Subsume      : 10
% 2.23/1.43  #Demod        : 22
% 2.23/1.43  #Tautology    : 44
% 2.23/1.43  #SimpNegUnit  : 3
% 2.23/1.43  #BackRed      : 0
% 2.23/1.43  
% 2.23/1.43  #Partial instantiations: 0
% 2.23/1.43  #Strategies tried      : 1
% 2.23/1.43  
% 2.23/1.43  Timing (in seconds)
% 2.23/1.43  ----------------------
% 2.23/1.44  Preprocessing        : 0.36
% 2.23/1.44  Parsing              : 0.18
% 2.23/1.44  CNF conversion       : 0.02
% 2.23/1.44  Main loop            : 0.25
% 2.23/1.44  Inferencing          : 0.09
% 2.23/1.44  Reduction            : 0.08
% 2.23/1.44  Demodulation         : 0.05
% 2.23/1.44  BG Simplification    : 0.01
% 2.23/1.44  Subsumption          : 0.04
% 2.23/1.44  Abstraction          : 0.01
% 2.23/1.44  MUC search           : 0.00
% 2.23/1.44  Cooper               : 0.00
% 2.23/1.44  Total                : 0.65
% 2.23/1.44  Index Insertion      : 0.00
% 2.23/1.44  Index Deletion       : 0.00
% 2.23/1.44  Index Matching       : 0.00
% 2.23/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
