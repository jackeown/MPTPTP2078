%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:47 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   52 (  92 expanded)
%              Number of leaves         :   20 (  42 expanded)
%              Depth                    :    7
%              Number of atoms          :   87 ( 261 expanded)
%              Number of equality atoms :   11 (  40 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_wellord1 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( ( v2_wellord1(C)
            & r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C)) )
         => ( r1_tarski(k1_wellord1(C,A),k1_wellord1(C,B))
          <=> ( A = B
              | r2_hidden(A,k1_wellord1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_wellord1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( v2_wellord1(C)
          & r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) )
       => ( r2_hidden(k4_tarski(A,B),C)
        <=> r1_tarski(k1_wellord1(C,A),k1_wellord1(C,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).

tff(c_36,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_51,plain,(
    ! [A_25,B_26] :
      ( ~ r2_hidden('#skF_1'(A_25,B_26),B_26)
      | r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_51])).

tff(c_40,plain,
    ( '#skF_5' != '#skF_4'
    | ~ r1_tarski(k1_wellord1('#skF_6','#skF_4'),k1_wellord1('#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_58,plain,(
    ~ r1_tarski(k1_wellord1('#skF_6','#skF_4'),k1_wellord1('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_48,plain,
    ( r1_tarski(k1_wellord1('#skF_6','#skF_4'),k1_wellord1('#skF_6','#skF_5'))
    | r2_hidden('#skF_4',k1_wellord1('#skF_6','#skF_5'))
    | '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_108,plain,
    ( r2_hidden('#skF_4',k1_wellord1('#skF_6','#skF_5'))
    | '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_48])).

tff(c_109,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_111,plain,(
    ~ r1_tarski(k1_wellord1('#skF_6','#skF_4'),k1_wellord1('#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_58])).

tff(c_115,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_111])).

tff(c_116,plain,(
    r2_hidden('#skF_4',k1_wellord1('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_10,plain,(
    ! [D_17,B_13,A_6] :
      ( r2_hidden(k4_tarski(D_17,B_13),A_6)
      | ~ r2_hidden(D_17,k1_wellord1(A_6,B_13))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    v2_wellord1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,(
    r2_hidden('#skF_4',k3_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    r2_hidden('#skF_5',k3_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_229,plain,(
    ! [C_87,A_88,B_89] :
      ( r1_tarski(k1_wellord1(C_87,A_88),k1_wellord1(C_87,B_89))
      | ~ r2_hidden(k4_tarski(A_88,B_89),C_87)
      | ~ r2_hidden(B_89,k3_relat_1(C_87))
      | ~ r2_hidden(A_88,k3_relat_1(C_87))
      | ~ v2_wellord1(C_87)
      | ~ v1_relat_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_250,plain,
    ( ~ r2_hidden(k4_tarski('#skF_4','#skF_5'),'#skF_6')
    | ~ r2_hidden('#skF_5',k3_relat_1('#skF_6'))
    | ~ r2_hidden('#skF_4',k3_relat_1('#skF_6'))
    | ~ v2_wellord1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_229,c_58])).

tff(c_261,plain,(
    ~ r2_hidden(k4_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_250])).

tff(c_264,plain,
    ( ~ r2_hidden('#skF_4',k1_wellord1('#skF_6','#skF_5'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_261])).

tff(c_268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_116,c_264])).

tff(c_269,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_270,plain,(
    r1_tarski(k1_wellord1('#skF_6','#skF_4'),k1_wellord1('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,
    ( ~ r2_hidden('#skF_4',k1_wellord1('#skF_6','#skF_5'))
    | ~ r1_tarski(k1_wellord1('#skF_6','#skF_4'),k1_wellord1('#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_272,plain,(
    ~ r2_hidden('#skF_4',k1_wellord1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_38])).

tff(c_566,plain,(
    ! [A_167,B_168,C_169] :
      ( r2_hidden(k4_tarski(A_167,B_168),C_169)
      | ~ r1_tarski(k1_wellord1(C_169,A_167),k1_wellord1(C_169,B_168))
      | ~ r2_hidden(B_168,k3_relat_1(C_169))
      | ~ r2_hidden(A_167,k3_relat_1(C_169))
      | ~ v2_wellord1(C_169)
      | ~ v1_relat_1(C_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_573,plain,
    ( r2_hidden(k4_tarski('#skF_4','#skF_5'),'#skF_6')
    | ~ r2_hidden('#skF_5',k3_relat_1('#skF_6'))
    | ~ r2_hidden('#skF_4',k3_relat_1('#skF_6'))
    | ~ v2_wellord1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_270,c_566])).

tff(c_583,plain,(
    r2_hidden(k4_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_573])).

tff(c_8,plain,(
    ! [D_17,A_6,B_13] :
      ( r2_hidden(D_17,k1_wellord1(A_6,B_13))
      | ~ r2_hidden(k4_tarski(D_17,B_13),A_6)
      | D_17 = B_13
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_587,plain,
    ( r2_hidden('#skF_4',k1_wellord1('#skF_6','#skF_5'))
    | '#skF_5' = '#skF_4'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_583,c_8])).

tff(c_592,plain,
    ( r2_hidden('#skF_4',k1_wellord1('#skF_6','#skF_5'))
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_587])).

tff(c_594,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_269,c_272,c_592])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n023.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 15:32:51 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.40  
% 2.81/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.40  %$ r2_hidden > r1_tarski > v2_wellord1 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.81/1.40  
% 2.81/1.40  %Foreground sorts:
% 2.81/1.40  
% 2.81/1.40  
% 2.81/1.40  %Background operators:
% 2.81/1.40  
% 2.81/1.40  
% 2.81/1.40  %Foreground operators:
% 2.81/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.81/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.81/1.40  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.81/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.81/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.81/1.40  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 2.81/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.81/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.81/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.81/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.40  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 2.81/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.81/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.81/1.40  
% 2.81/1.41  tff(f_72, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) => (r1_tarski(k1_wellord1(C, A), k1_wellord1(C, B)) <=> ((A = B) | r2_hidden(A, k1_wellord1(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_wellord1)).
% 2.81/1.41  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.81/1.41  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 2.81/1.41  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) => (r2_hidden(k4_tarski(A, B), C) <=> r1_tarski(k1_wellord1(C, A), k1_wellord1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_wellord1)).
% 2.81/1.41  tff(c_36, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.81/1.41  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.41  tff(c_51, plain, (![A_25, B_26]: (~r2_hidden('#skF_1'(A_25, B_26), B_26) | r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.81/1.41  tff(c_56, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_51])).
% 2.81/1.41  tff(c_40, plain, ('#skF_5'!='#skF_4' | ~r1_tarski(k1_wellord1('#skF_6', '#skF_4'), k1_wellord1('#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.81/1.41  tff(c_58, plain, (~r1_tarski(k1_wellord1('#skF_6', '#skF_4'), k1_wellord1('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_40])).
% 2.81/1.41  tff(c_48, plain, (r1_tarski(k1_wellord1('#skF_6', '#skF_4'), k1_wellord1('#skF_6', '#skF_5')) | r2_hidden('#skF_4', k1_wellord1('#skF_6', '#skF_5')) | '#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.81/1.41  tff(c_108, plain, (r2_hidden('#skF_4', k1_wellord1('#skF_6', '#skF_5')) | '#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_58, c_48])).
% 2.81/1.41  tff(c_109, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_108])).
% 2.81/1.41  tff(c_111, plain, (~r1_tarski(k1_wellord1('#skF_6', '#skF_4'), k1_wellord1('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_58])).
% 2.81/1.41  tff(c_115, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_111])).
% 2.81/1.41  tff(c_116, plain, (r2_hidden('#skF_4', k1_wellord1('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_108])).
% 2.81/1.41  tff(c_10, plain, (![D_17, B_13, A_6]: (r2_hidden(k4_tarski(D_17, B_13), A_6) | ~r2_hidden(D_17, k1_wellord1(A_6, B_13)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.81/1.41  tff(c_34, plain, (v2_wellord1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.81/1.41  tff(c_32, plain, (r2_hidden('#skF_4', k3_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.81/1.41  tff(c_30, plain, (r2_hidden('#skF_5', k3_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.81/1.41  tff(c_229, plain, (![C_87, A_88, B_89]: (r1_tarski(k1_wellord1(C_87, A_88), k1_wellord1(C_87, B_89)) | ~r2_hidden(k4_tarski(A_88, B_89), C_87) | ~r2_hidden(B_89, k3_relat_1(C_87)) | ~r2_hidden(A_88, k3_relat_1(C_87)) | ~v2_wellord1(C_87) | ~v1_relat_1(C_87))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.81/1.41  tff(c_250, plain, (~r2_hidden(k4_tarski('#skF_4', '#skF_5'), '#skF_6') | ~r2_hidden('#skF_5', k3_relat_1('#skF_6')) | ~r2_hidden('#skF_4', k3_relat_1('#skF_6')) | ~v2_wellord1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_229, c_58])).
% 2.81/1.41  tff(c_261, plain, (~r2_hidden(k4_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_250])).
% 2.81/1.41  tff(c_264, plain, (~r2_hidden('#skF_4', k1_wellord1('#skF_6', '#skF_5')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_10, c_261])).
% 2.81/1.41  tff(c_268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_116, c_264])).
% 2.81/1.41  tff(c_269, plain, ('#skF_5'!='#skF_4'), inference(splitRight, [status(thm)], [c_40])).
% 2.81/1.41  tff(c_270, plain, (r1_tarski(k1_wellord1('#skF_6', '#skF_4'), k1_wellord1('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_40])).
% 2.81/1.41  tff(c_38, plain, (~r2_hidden('#skF_4', k1_wellord1('#skF_6', '#skF_5')) | ~r1_tarski(k1_wellord1('#skF_6', '#skF_4'), k1_wellord1('#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.81/1.41  tff(c_272, plain, (~r2_hidden('#skF_4', k1_wellord1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_270, c_38])).
% 2.81/1.41  tff(c_566, plain, (![A_167, B_168, C_169]: (r2_hidden(k4_tarski(A_167, B_168), C_169) | ~r1_tarski(k1_wellord1(C_169, A_167), k1_wellord1(C_169, B_168)) | ~r2_hidden(B_168, k3_relat_1(C_169)) | ~r2_hidden(A_167, k3_relat_1(C_169)) | ~v2_wellord1(C_169) | ~v1_relat_1(C_169))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.81/1.41  tff(c_573, plain, (r2_hidden(k4_tarski('#skF_4', '#skF_5'), '#skF_6') | ~r2_hidden('#skF_5', k3_relat_1('#skF_6')) | ~r2_hidden('#skF_4', k3_relat_1('#skF_6')) | ~v2_wellord1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_270, c_566])).
% 2.81/1.41  tff(c_583, plain, (r2_hidden(k4_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_573])).
% 2.81/1.41  tff(c_8, plain, (![D_17, A_6, B_13]: (r2_hidden(D_17, k1_wellord1(A_6, B_13)) | ~r2_hidden(k4_tarski(D_17, B_13), A_6) | D_17=B_13 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.81/1.41  tff(c_587, plain, (r2_hidden('#skF_4', k1_wellord1('#skF_6', '#skF_5')) | '#skF_5'='#skF_4' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_583, c_8])).
% 2.81/1.41  tff(c_592, plain, (r2_hidden('#skF_4', k1_wellord1('#skF_6', '#skF_5')) | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_587])).
% 2.81/1.41  tff(c_594, plain, $false, inference(negUnitSimplification, [status(thm)], [c_269, c_272, c_592])).
% 2.81/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.41  
% 2.81/1.41  Inference rules
% 2.81/1.41  ----------------------
% 2.81/1.41  #Ref     : 0
% 2.81/1.41  #Sup     : 115
% 2.81/1.41  #Fact    : 0
% 2.81/1.41  #Define  : 0
% 2.81/1.41  #Split   : 6
% 2.81/1.41  #Chain   : 0
% 2.81/1.41  #Close   : 0
% 2.81/1.41  
% 2.81/1.41  Ordering : KBO
% 2.81/1.41  
% 2.81/1.41  Simplification rules
% 2.81/1.41  ----------------------
% 2.81/1.41  #Subsume      : 15
% 2.81/1.41  #Demod        : 29
% 2.81/1.41  #Tautology    : 13
% 2.81/1.41  #SimpNegUnit  : 4
% 2.81/1.41  #BackRed      : 3
% 2.81/1.41  
% 2.81/1.41  #Partial instantiations: 0
% 2.81/1.41  #Strategies tried      : 1
% 2.81/1.41  
% 2.81/1.41  Timing (in seconds)
% 2.81/1.41  ----------------------
% 2.81/1.41  Preprocessing        : 0.30
% 2.81/1.41  Parsing              : 0.15
% 2.81/1.41  CNF conversion       : 0.02
% 2.81/1.41  Main loop            : 0.35
% 2.81/1.41  Inferencing          : 0.13
% 2.81/1.41  Reduction            : 0.08
% 2.81/1.41  Demodulation         : 0.06
% 2.81/1.41  BG Simplification    : 0.02
% 2.81/1.41  Subsumption          : 0.09
% 2.81/1.41  Abstraction          : 0.02
% 2.81/1.41  MUC search           : 0.00
% 2.81/1.41  Cooper               : 0.00
% 2.81/1.41  Total                : 0.68
% 2.81/1.41  Index Insertion      : 0.00
% 2.81/1.41  Index Deletion       : 0.00
% 2.81/1.41  Index Matching       : 0.00
% 2.81/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
