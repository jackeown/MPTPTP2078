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

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   51 (  82 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 ( 132 expanded)
%              Number of equality atoms :   18 (  43 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k1_relat_1(B))
            & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_27,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_31,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_27])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_20])).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( v1_relat_1(k7_relat_1(A_2,B_3))
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_112,plain,(
    ! [B_20,A_21] :
      ( k1_relat_1(k7_relat_1(B_20,A_21)) = A_21
      | ~ r1_tarski(A_21,k1_relat_1(B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_121,plain,
    ( k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = '#skF_2'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_112])).

tff(c_124,plain,(
    k1_relat_1(k7_relat_1('#skF_3','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_121])).

tff(c_8,plain,(
    ! [A_4] :
      ( v1_xboole_0(k1_relat_1(A_4))
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_134,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0(k7_relat_1('#skF_3','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_8])).

tff(c_138,plain,(
    ~ v1_xboole_0(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_16,plain,(
    k9_relat_1('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_33,plain,(
    k9_relat_1('#skF_3','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_16])).

tff(c_100,plain,(
    ! [B_18,A_19] :
      ( k2_relat_1(k7_relat_1(B_18,A_19)) = k9_relat_1(B_18,A_19)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(k2_relat_1(A_5))
      | ~ v1_relat_1(A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_140,plain,(
    ! [B_22,A_23] :
      ( ~ v1_xboole_0(k9_relat_1(B_22,A_23))
      | ~ v1_relat_1(k7_relat_1(B_22,A_23))
      | v1_xboole_0(k7_relat_1(B_22,A_23))
      | ~ v1_relat_1(B_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_10])).

tff(c_143,plain,
    ( ~ v1_xboole_0('#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | v1_xboole_0(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_140])).

tff(c_145,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | v1_xboole_0(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_4,c_143])).

tff(c_146,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_145])).

tff(c_149,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_146])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_149])).

tff(c_154,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_2])).

tff(c_161,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_154,c_32])).

tff(c_166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_161])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:00:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.14  
% 1.67/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.14  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.67/1.14  
% 1.67/1.14  %Foreground sorts:
% 1.67/1.14  
% 1.67/1.14  
% 1.67/1.14  %Background operators:
% 1.67/1.14  
% 1.67/1.14  
% 1.67/1.14  %Foreground operators:
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.67/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.67/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.67/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.67/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.14  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.67/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.67/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.67/1.14  
% 1.67/1.16  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 1.67/1.16  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.67/1.16  tff(f_68, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 1.67/1.16  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.67/1.16  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 1.67/1.16  tff(f_39, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 1.67/1.16  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.67/1.16  tff(f_47, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 1.67/1.16  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.16  tff(c_27, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.16  tff(c_31, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_27])).
% 1.67/1.16  tff(c_20, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.67/1.16  tff(c_34, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_31, c_20])).
% 1.67/1.16  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.67/1.16  tff(c_6, plain, (![A_2, B_3]: (v1_relat_1(k7_relat_1(A_2, B_3)) | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.67/1.16  tff(c_18, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.67/1.16  tff(c_112, plain, (![B_20, A_21]: (k1_relat_1(k7_relat_1(B_20, A_21))=A_21 | ~r1_tarski(A_21, k1_relat_1(B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.67/1.16  tff(c_121, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))='#skF_2' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_112])).
% 1.67/1.16  tff(c_124, plain, (k1_relat_1(k7_relat_1('#skF_3', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_121])).
% 1.67/1.16  tff(c_8, plain, (![A_4]: (v1_xboole_0(k1_relat_1(A_4)) | ~v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.67/1.16  tff(c_134, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0(k7_relat_1('#skF_3', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_124, c_8])).
% 1.67/1.16  tff(c_138, plain, (~v1_xboole_0(k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_134])).
% 1.67/1.16  tff(c_16, plain, (k9_relat_1('#skF_3', '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.67/1.16  tff(c_33, plain, (k9_relat_1('#skF_3', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_31, c_16])).
% 1.67/1.16  tff(c_100, plain, (![B_18, A_19]: (k2_relat_1(k7_relat_1(B_18, A_19))=k9_relat_1(B_18, A_19) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.67/1.16  tff(c_10, plain, (![A_5]: (~v1_xboole_0(k2_relat_1(A_5)) | ~v1_relat_1(A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.67/1.16  tff(c_140, plain, (![B_22, A_23]: (~v1_xboole_0(k9_relat_1(B_22, A_23)) | ~v1_relat_1(k7_relat_1(B_22, A_23)) | v1_xboole_0(k7_relat_1(B_22, A_23)) | ~v1_relat_1(B_22))), inference(superposition, [status(thm), theory('equality')], [c_100, c_10])).
% 1.67/1.16  tff(c_143, plain, (~v1_xboole_0('#skF_1') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | v1_xboole_0(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_33, c_140])).
% 1.67/1.16  tff(c_145, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | v1_xboole_0(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_4, c_143])).
% 1.67/1.16  tff(c_146, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_138, c_145])).
% 1.67/1.16  tff(c_149, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_146])).
% 1.67/1.16  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_149])).
% 1.67/1.16  tff(c_154, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_134])).
% 1.67/1.16  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.67/1.16  tff(c_32, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_2])).
% 1.67/1.16  tff(c_161, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_154, c_32])).
% 1.67/1.16  tff(c_166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_161])).
% 1.67/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.16  
% 1.67/1.16  Inference rules
% 1.67/1.16  ----------------------
% 1.67/1.16  #Ref     : 0
% 1.67/1.16  #Sup     : 35
% 1.67/1.16  #Fact    : 0
% 1.67/1.16  #Define  : 0
% 1.67/1.16  #Split   : 2
% 1.67/1.16  #Chain   : 0
% 1.67/1.16  #Close   : 0
% 1.67/1.16  
% 1.67/1.16  Ordering : KBO
% 1.67/1.16  
% 1.67/1.16  Simplification rules
% 1.67/1.16  ----------------------
% 1.67/1.16  #Subsume      : 1
% 1.67/1.16  #Demod        : 14
% 1.67/1.16  #Tautology    : 20
% 1.67/1.16  #SimpNegUnit  : 2
% 1.67/1.16  #BackRed      : 3
% 1.67/1.16  
% 1.67/1.16  #Partial instantiations: 0
% 1.67/1.16  #Strategies tried      : 1
% 1.67/1.16  
% 1.67/1.16  Timing (in seconds)
% 1.67/1.16  ----------------------
% 1.89/1.16  Preprocessing        : 0.27
% 1.89/1.16  Parsing              : 0.14
% 1.89/1.16  CNF conversion       : 0.02
% 1.89/1.16  Main loop            : 0.14
% 1.89/1.16  Inferencing          : 0.05
% 1.89/1.16  Reduction            : 0.04
% 1.89/1.16  Demodulation         : 0.03
% 1.89/1.16  BG Simplification    : 0.01
% 1.89/1.16  Subsumption          : 0.02
% 1.89/1.16  Abstraction          : 0.01
% 1.89/1.16  MUC search           : 0.00
% 1.89/1.16  Cooper               : 0.00
% 1.89/1.16  Total                : 0.43
% 1.89/1.16  Index Insertion      : 0.00
% 1.89/1.16  Index Deletion       : 0.00
% 1.89/1.16  Index Matching       : 0.00
% 1.89/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
