%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:49 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :   44 (  61 expanded)
%              Number of leaves         :   17 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 113 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k2_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
            <=> r1_tarski(A,k7_relat_1(B,k1_relat_1(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t219_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_28,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_86,plain,(
    r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_22,plain,
    ( ~ r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1')))
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_176,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_22])).

tff(c_45,plain,(
    ! [B_21,A_22] :
      ( r1_tarski(k7_relat_1(B_21,A_22),B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_49,plain,(
    ! [B_21,A_22] :
      ( k2_xboole_0(k7_relat_1(B_21,A_22),B_21) = B_21
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_45,c_10])).

tff(c_93,plain,(
    k2_xboole_0('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) = k7_relat_1('#skF_2',k1_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_86,c_10])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [A_25,C_26,B_27] :
      ( r1_tarski(A_25,C_26)
      | ~ r1_tarski(k2_xboole_0(A_25,B_27),C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    ! [A_28,B_29] : r1_tarski(A_28,k2_xboole_0(A_28,B_29)) ),
    inference(resolution,[status(thm)],[c_6,c_60])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_82,plain,(
    ! [A_3,B_4,B_29] : r1_tarski(A_3,k2_xboole_0(k2_xboole_0(A_3,B_4),B_29)) ),
    inference(resolution,[status(thm)],[c_69,c_8])).

tff(c_270,plain,(
    ! [B_44] : r1_tarski('#skF_1',k2_xboole_0(k7_relat_1('#skF_2',k1_relat_1('#skF_1')),B_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_82])).

tff(c_283,plain,
    ( r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_270])).

tff(c_292,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_283])).

tff(c_294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_292])).

tff(c_295,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_530,plain,(
    ! [B_59,A_60] :
      ( k7_relat_1(B_59,A_60) = B_59
      | ~ r1_tarski(k1_relat_1(B_59),A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_545,plain,(
    ! [B_59] :
      ( k7_relat_1(B_59,k1_relat_1(B_59)) = B_59
      | ~ v1_relat_1(B_59) ) ),
    inference(resolution,[status(thm)],[c_6,c_530])).

tff(c_814,plain,(
    ! [B_78,A_79,C_80] :
      ( r1_tarski(k7_relat_1(B_78,A_79),k7_relat_1(C_80,A_79))
      | ~ r1_tarski(B_78,C_80)
      | ~ v1_relat_1(C_80)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3104,plain,(
    ! [B_174,C_175] :
      ( r1_tarski(B_174,k7_relat_1(C_175,k1_relat_1(B_174)))
      | ~ r1_tarski(B_174,C_175)
      | ~ v1_relat_1(C_175)
      | ~ v1_relat_1(B_174)
      | ~ v1_relat_1(B_174) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_545,c_814])).

tff(c_296,plain,(
    ~ r1_tarski('#skF_1',k7_relat_1('#skF_2',k1_relat_1('#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_3154,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_3104,c_296])).

tff(c_3193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_295,c_3154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:43:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.72/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.66  
% 3.72/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.72/1.66  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k2_xboole_0 > #nlpp > k1_relat_1 > #skF_2 > #skF_1
% 3.72/1.66  
% 3.72/1.66  %Foreground sorts:
% 3.72/1.66  
% 3.72/1.66  
% 3.72/1.66  %Background operators:
% 3.72/1.66  
% 3.72/1.66  
% 3.72/1.66  %Foreground operators:
% 3.72/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.72/1.66  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.72/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.72/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.72/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.72/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.72/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.72/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.72/1.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.72/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.72/1.66  
% 4.06/1.67  tff(f_68, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) <=> r1_tarski(A, k7_relat_1(B, k1_relat_1(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t219_relat_1)).
% 4.06/1.67  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 4.06/1.67  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.06/1.67  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.06/1.67  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.06/1.67  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 4.06/1.67  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_relat_1)).
% 4.06/1.67  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.06/1.67  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.06/1.67  tff(c_28, plain, (r1_tarski('#skF_1', '#skF_2') | r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.06/1.67  tff(c_86, plain, (r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(splitLeft, [status(thm)], [c_28])).
% 4.06/1.67  tff(c_22, plain, (~r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1'))) | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.06/1.67  tff(c_176, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_22])).
% 4.06/1.67  tff(c_45, plain, (![B_21, A_22]: (r1_tarski(k7_relat_1(B_21, A_22), B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.06/1.67  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.06/1.67  tff(c_49, plain, (![B_21, A_22]: (k2_xboole_0(k7_relat_1(B_21, A_22), B_21)=B_21 | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_45, c_10])).
% 4.06/1.67  tff(c_93, plain, (k2_xboole_0('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))=k7_relat_1('#skF_2', k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_86, c_10])).
% 4.06/1.67  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.06/1.67  tff(c_60, plain, (![A_25, C_26, B_27]: (r1_tarski(A_25, C_26) | ~r1_tarski(k2_xboole_0(A_25, B_27), C_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.06/1.67  tff(c_69, plain, (![A_28, B_29]: (r1_tarski(A_28, k2_xboole_0(A_28, B_29)))), inference(resolution, [status(thm)], [c_6, c_60])).
% 4.06/1.67  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.06/1.67  tff(c_82, plain, (![A_3, B_4, B_29]: (r1_tarski(A_3, k2_xboole_0(k2_xboole_0(A_3, B_4), B_29)))), inference(resolution, [status(thm)], [c_69, c_8])).
% 4.06/1.67  tff(c_270, plain, (![B_44]: (r1_tarski('#skF_1', k2_xboole_0(k7_relat_1('#skF_2', k1_relat_1('#skF_1')), B_44)))), inference(superposition, [status(thm), theory('equality')], [c_93, c_82])).
% 4.06/1.67  tff(c_283, plain, (r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_49, c_270])).
% 4.06/1.67  tff(c_292, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_283])).
% 4.06/1.67  tff(c_294, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_292])).
% 4.06/1.67  tff(c_295, plain, (r1_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_28])).
% 4.06/1.67  tff(c_530, plain, (![B_59, A_60]: (k7_relat_1(B_59, A_60)=B_59 | ~r1_tarski(k1_relat_1(B_59), A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.06/1.67  tff(c_545, plain, (![B_59]: (k7_relat_1(B_59, k1_relat_1(B_59))=B_59 | ~v1_relat_1(B_59))), inference(resolution, [status(thm)], [c_6, c_530])).
% 4.06/1.67  tff(c_814, plain, (![B_78, A_79, C_80]: (r1_tarski(k7_relat_1(B_78, A_79), k7_relat_1(C_80, A_79)) | ~r1_tarski(B_78, C_80) | ~v1_relat_1(C_80) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.06/1.67  tff(c_3104, plain, (![B_174, C_175]: (r1_tarski(B_174, k7_relat_1(C_175, k1_relat_1(B_174))) | ~r1_tarski(B_174, C_175) | ~v1_relat_1(C_175) | ~v1_relat_1(B_174) | ~v1_relat_1(B_174))), inference(superposition, [status(thm), theory('equality')], [c_545, c_814])).
% 4.06/1.67  tff(c_296, plain, (~r1_tarski('#skF_1', k7_relat_1('#skF_2', k1_relat_1('#skF_1')))), inference(splitRight, [status(thm)], [c_28])).
% 4.06/1.67  tff(c_3154, plain, (~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_3104, c_296])).
% 4.06/1.67  tff(c_3193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_295, c_3154])).
% 4.06/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.06/1.67  
% 4.06/1.67  Inference rules
% 4.06/1.67  ----------------------
% 4.06/1.67  #Ref     : 0
% 4.06/1.67  #Sup     : 739
% 4.06/1.67  #Fact    : 0
% 4.06/1.67  #Define  : 0
% 4.06/1.67  #Split   : 2
% 4.06/1.67  #Chain   : 0
% 4.06/1.67  #Close   : 0
% 4.06/1.67  
% 4.06/1.67  Ordering : KBO
% 4.06/1.67  
% 4.06/1.67  Simplification rules
% 4.06/1.67  ----------------------
% 4.06/1.67  #Subsume      : 159
% 4.06/1.67  #Demod        : 415
% 4.06/1.67  #Tautology    : 311
% 4.06/1.67  #SimpNegUnit  : 1
% 4.06/1.67  #BackRed      : 0
% 4.06/1.67  
% 4.06/1.67  #Partial instantiations: 0
% 4.06/1.67  #Strategies tried      : 1
% 4.06/1.67  
% 4.06/1.67  Timing (in seconds)
% 4.06/1.67  ----------------------
% 4.06/1.67  Preprocessing        : 0.26
% 4.06/1.67  Parsing              : 0.15
% 4.06/1.67  CNF conversion       : 0.02
% 4.06/1.67  Main loop            : 0.66
% 4.06/1.67  Inferencing          : 0.23
% 4.06/1.67  Reduction            : 0.23
% 4.06/1.67  Demodulation         : 0.18
% 4.06/1.67  BG Simplification    : 0.02
% 4.06/1.67  Subsumption          : 0.13
% 4.06/1.67  Abstraction          : 0.04
% 4.06/1.67  MUC search           : 0.00
% 4.06/1.67  Cooper               : 0.00
% 4.06/1.67  Total                : 0.95
% 4.06/1.67  Index Insertion      : 0.00
% 4.06/1.67  Index Deletion       : 0.00
% 4.06/1.67  Index Matching       : 0.00
% 4.06/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
