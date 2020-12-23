%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:48 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   46 (  65 expanded)
%              Number of leaves         :   18 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 ( 118 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r1_tarski > v1_relat_1 > k7_relat_1 > k2_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
            <=> r1_tarski(A,k7_relat_1(B,k1_relat_1(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t219_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( ( v1_relat_1(C)
            & v4_relat_1(C,A) )
         => ( r1_tarski(C,B)
           => r1_tarski(C,k7_relat_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t210_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_494,plain,(
    ! [B_59,A_60] :
      ( v4_relat_1(B_59,A_60)
      | ~ r1_tarski(k1_relat_1(B_59),A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_509,plain,(
    ! [B_59] :
      ( v4_relat_1(B_59,k1_relat_1(B_59))
      | ~ v1_relat_1(B_59) ) ),
    inference(resolution,[status(thm)],[c_6,c_494])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_24,plain,
    ( ~ r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1')))
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_88,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_47,plain,(
    ! [B_21,A_22] :
      ( r1_tarski(k7_relat_1(B_21,A_22),B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51,plain,(
    ! [B_21,A_22] :
      ( k2_xboole_0(k7_relat_1(B_21,A_22),B_21) = B_21
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_47,c_10])).

tff(c_30,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_170,plain,(
    r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_30])).

tff(c_177,plain,(
    k2_xboole_0('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) = k7_relat_1('#skF_2',k1_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_170,c_10])).

tff(c_62,plain,(
    ! [A_25,C_26,B_27] :
      ( r1_tarski(A_25,C_26)
      | ~ r1_tarski(k2_xboole_0(A_25,B_27),C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_71,plain,(
    ! [A_28,B_29] : r1_tarski(A_28,k2_xboole_0(A_28,B_29)) ),
    inference(resolution,[status(thm)],[c_6,c_62])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,(
    ! [A_3,B_4,B_29] : r1_tarski(A_3,k2_xboole_0(k2_xboole_0(A_3,B_4),B_29)) ),
    inference(resolution,[status(thm)],[c_71,c_8])).

tff(c_234,plain,(
    ! [B_44] : r1_tarski('#skF_1',k2_xboole_0(k7_relat_1('#skF_2',k1_relat_1('#skF_1')),B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_84])).

tff(c_247,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_234])).

tff(c_256,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_247])).

tff(c_258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_256])).

tff(c_260,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_696,plain,(
    ! [C_78,B_79,A_80] :
      ( r1_tarski(C_78,k7_relat_1(B_79,A_80))
      | ~ r1_tarski(C_78,B_79)
      | ~ v4_relat_1(C_78,A_80)
      | ~ v1_relat_1(C_78)
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_259,plain,(
    ~ r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_715,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v4_relat_1('#skF_1',k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_696,c_259])).

tff(c_733,plain,(
    ~ v4_relat_1('#skF_1',k1_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_260,c_715])).

tff(c_739,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_509,c_733])).

tff(c_743,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_739])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:54:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.38  
% 2.48/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.38  %$ v4_relat_1 > r1_tarski > v1_relat_1 > k7_relat_1 > k2_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 2.48/1.38  
% 2.48/1.38  %Foreground sorts:
% 2.48/1.38  
% 2.48/1.38  
% 2.48/1.38  %Background operators:
% 2.48/1.38  
% 2.48/1.38  
% 2.48/1.38  %Foreground operators:
% 2.48/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.48/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.48/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.48/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.48/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.48/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.48/1.38  
% 2.77/1.40  tff(f_70, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) <=> r1_tarski(A, k7_relat_1(B, k1_relat_1(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t219_relat_1)).
% 2.77/1.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.77/1.40  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.77/1.40  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 2.77/1.40  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.77/1.40  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.77/1.40  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (![C]: ((v1_relat_1(C) & v4_relat_1(C, A)) => (r1_tarski(C, B) => r1_tarski(C, k7_relat_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t210_relat_1)).
% 2.77/1.40  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.77/1.40  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.77/1.40  tff(c_494, plain, (![B_59, A_60]: (v4_relat_1(B_59, A_60) | ~r1_tarski(k1_relat_1(B_59), A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.77/1.40  tff(c_509, plain, (![B_59]: (v4_relat_1(B_59, k1_relat_1(B_59)) | ~v1_relat_1(B_59))), inference(resolution, [status(thm)], [c_6, c_494])).
% 2.77/1.40  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.77/1.40  tff(c_24, plain, (~r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1'))) | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.77/1.40  tff(c_88, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_24])).
% 2.77/1.40  tff(c_47, plain, (![B_21, A_22]: (r1_tarski(k7_relat_1(B_21, A_22), B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.77/1.40  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.77/1.40  tff(c_51, plain, (![B_21, A_22]: (k2_xboole_0(k7_relat_1(B_21, A_22), B_21)=B_21 | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_47, c_10])).
% 2.77/1.40  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_2') | r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.77/1.40  tff(c_170, plain, (r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_88, c_30])).
% 2.77/1.40  tff(c_177, plain, (k2_xboole_0('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))=k7_relat_1('#skF_2', k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_170, c_10])).
% 2.77/1.40  tff(c_62, plain, (![A_25, C_26, B_27]: (r1_tarski(A_25, C_26) | ~r1_tarski(k2_xboole_0(A_25, B_27), C_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.77/1.40  tff(c_71, plain, (![A_28, B_29]: (r1_tarski(A_28, k2_xboole_0(A_28, B_29)))), inference(resolution, [status(thm)], [c_6, c_62])).
% 2.77/1.40  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.77/1.40  tff(c_84, plain, (![A_3, B_4, B_29]: (r1_tarski(A_3, k2_xboole_0(k2_xboole_0(A_3, B_4), B_29)))), inference(resolution, [status(thm)], [c_71, c_8])).
% 2.77/1.40  tff(c_234, plain, (![B_44]: (r1_tarski('#skF_1', k2_xboole_0(k7_relat_1('#skF_2', k1_relat_1('#skF_1')), B_44)))), inference(superposition, [status(thm), theory('equality')], [c_177, c_84])).
% 2.77/1.40  tff(c_247, plain, (r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_51, c_234])).
% 2.77/1.40  tff(c_256, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_247])).
% 2.77/1.40  tff(c_258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_256])).
% 2.77/1.40  tff(c_260, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_24])).
% 2.77/1.40  tff(c_696, plain, (![C_78, B_79, A_80]: (r1_tarski(C_78, k7_relat_1(B_79, A_80)) | ~r1_tarski(C_78, B_79) | ~v4_relat_1(C_78, A_80) | ~v1_relat_1(C_78) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.77/1.40  tff(c_259, plain, (~r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(splitRight, [status(thm)], [c_24])).
% 2.77/1.40  tff(c_715, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v4_relat_1('#skF_1', k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_696, c_259])).
% 2.77/1.40  tff(c_733, plain, (~v4_relat_1('#skF_1', k1_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_260, c_715])).
% 2.77/1.40  tff(c_739, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_509, c_733])).
% 2.77/1.40  tff(c_743, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_739])).
% 2.77/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.40  
% 2.77/1.40  Inference rules
% 2.77/1.40  ----------------------
% 2.77/1.40  #Ref     : 0
% 2.77/1.40  #Sup     : 164
% 2.77/1.40  #Fact    : 0
% 2.77/1.40  #Define  : 0
% 2.77/1.40  #Split   : 2
% 2.77/1.40  #Chain   : 0
% 2.77/1.40  #Close   : 0
% 2.77/1.40  
% 2.77/1.40  Ordering : KBO
% 2.77/1.40  
% 2.77/1.40  Simplification rules
% 2.77/1.40  ----------------------
% 2.77/1.40  #Subsume      : 17
% 2.77/1.40  #Demod        : 77
% 2.77/1.40  #Tautology    : 75
% 2.77/1.40  #SimpNegUnit  : 3
% 2.77/1.40  #BackRed      : 0
% 2.77/1.40  
% 2.77/1.40  #Partial instantiations: 0
% 2.77/1.40  #Strategies tried      : 1
% 2.77/1.40  
% 2.77/1.40  Timing (in seconds)
% 2.77/1.40  ----------------------
% 2.77/1.40  Preprocessing        : 0.29
% 2.77/1.40  Parsing              : 0.16
% 2.77/1.40  CNF conversion       : 0.02
% 2.77/1.40  Main loop            : 0.34
% 2.77/1.40  Inferencing          : 0.13
% 2.77/1.40  Reduction            : 0.10
% 2.77/1.40  Demodulation         : 0.08
% 2.77/1.40  BG Simplification    : 0.02
% 2.77/1.40  Subsumption          : 0.06
% 2.77/1.40  Abstraction          : 0.02
% 2.77/1.40  MUC search           : 0.00
% 2.77/1.40  Cooper               : 0.00
% 2.77/1.40  Total                : 0.66
% 2.77/1.40  Index Insertion      : 0.00
% 2.77/1.40  Index Deletion       : 0.00
% 2.77/1.40  Index Matching       : 0.00
% 2.77/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
