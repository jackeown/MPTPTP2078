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
% DateTime   : Thu Dec  3 10:06:22 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 119 expanded)
%              Number of leaves         :   16 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :   95 ( 265 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > k1_ordinal1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,k1_ordinal1(B))
            <=> r1_ordinal1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_46,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_42,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_55,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_hidden(A,B)
          <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_60,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_18,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_29,plain,(
    ~ r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_26,plain,
    ( r2_hidden('#skF_1',k1_ordinal1('#skF_2'))
    | r1_ordinal1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_30,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_26])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r1_ordinal1(A_1,B_2)
      | ~ v3_ordinal1(B_2)
      | ~ v3_ordinal1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_6] :
      ( v3_ordinal1(k1_ordinal1(A_6))
      | ~ v3_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_37,plain,(
    ! [B_20,A_21] :
      ( r2_hidden(B_20,A_21)
      | r1_ordinal1(A_21,B_20)
      | ~ v3_ordinal1(B_20)
      | ~ v3_ordinal1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_40,plain,
    ( r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_37,c_29])).

tff(c_46,plain,
    ( r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_40])).

tff(c_48,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_51,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_48])).

tff(c_55,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_51])).

tff(c_56,plain,(
    r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_59,plain,(
    ! [A_24,B_25] :
      ( r2_hidden(A_24,B_25)
      | ~ r1_ordinal1(k1_ordinal1(A_24),B_25)
      | ~ v3_ordinal1(B_25)
      | ~ v3_ordinal1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_65,plain,
    ( r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_59])).

tff(c_69,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_65])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( ~ r1_tarski(B_11,A_10)
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_73,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_69,c_14])).

tff(c_76,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_73])).

tff(c_80,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_30,c_76])).

tff(c_81,plain,(
    ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( r2_hidden(B_5,A_3)
      | r1_ordinal1(A_3,B_5)
      | ~ v3_ordinal1(B_5)
      | ~ v3_ordinal1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_117,plain,(
    ! [A_34,B_35] :
      ( r1_ordinal1(k1_ordinal1(A_34),B_35)
      | ~ r2_hidden(A_34,B_35)
      | ~ v3_ordinal1(B_35)
      | ~ v3_ordinal1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_89,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ r1_ordinal1(A_26,B_27)
      | ~ v3_ordinal1(B_27)
      | ~ v3_ordinal1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_83,plain,(
    r2_hidden('#skF_1',k1_ordinal1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_26])).

tff(c_87,plain,(
    ~ r1_tarski(k1_ordinal1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_83,c_14])).

tff(c_92,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_89,c_87])).

tff(c_95,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_1')
    | ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_92])).

tff(c_96,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_99,plain,(
    ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_96])).

tff(c_103,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_99])).

tff(c_104,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_2'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_123,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_117,c_104])).

tff(c_127,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18,c_123])).

tff(c_130,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_127])).

tff(c_133,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_130])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_133])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:49:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.16  
% 1.64/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.16  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > k1_ordinal1 > #skF_2 > #skF_1
% 1.64/1.16  
% 1.64/1.16  %Foreground sorts:
% 1.64/1.16  
% 1.64/1.16  
% 1.64/1.16  %Background operators:
% 1.64/1.16  
% 1.64/1.16  
% 1.64/1.16  %Foreground operators:
% 1.64/1.16  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.64/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.16  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 1.64/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.16  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.64/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.16  
% 1.64/1.17  tff(f_70, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, k1_ordinal1(B)) <=> r1_ordinal1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_ordinal1)).
% 1.64/1.17  tff(f_33, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 1.64/1.17  tff(f_46, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 1.64/1.17  tff(f_42, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 1.64/1.17  tff(f_55, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 1.64/1.17  tff(f_60, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 1.64/1.17  tff(c_18, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.64/1.17  tff(c_16, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.64/1.17  tff(c_20, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.64/1.17  tff(c_29, plain, (~r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_20])).
% 1.64/1.17  tff(c_26, plain, (r2_hidden('#skF_1', k1_ordinal1('#skF_2')) | r1_ordinal1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.64/1.17  tff(c_30, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_29, c_26])).
% 1.64/1.17  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r1_ordinal1(A_1, B_2) | ~v3_ordinal1(B_2) | ~v3_ordinal1(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.64/1.17  tff(c_8, plain, (![A_6]: (v3_ordinal1(k1_ordinal1(A_6)) | ~v3_ordinal1(A_6))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.64/1.17  tff(c_37, plain, (![B_20, A_21]: (r2_hidden(B_20, A_21) | r1_ordinal1(A_21, B_20) | ~v3_ordinal1(B_20) | ~v3_ordinal1(A_21))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.64/1.17  tff(c_40, plain, (r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_37, c_29])).
% 1.64/1.17  tff(c_46, plain, (r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_40])).
% 1.64/1.17  tff(c_48, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_46])).
% 1.64/1.17  tff(c_51, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_48])).
% 1.64/1.17  tff(c_55, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_51])).
% 1.64/1.17  tff(c_56, plain, (r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_46])).
% 1.64/1.17  tff(c_59, plain, (![A_24, B_25]: (r2_hidden(A_24, B_25) | ~r1_ordinal1(k1_ordinal1(A_24), B_25) | ~v3_ordinal1(B_25) | ~v3_ordinal1(A_24))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.64/1.17  tff(c_65, plain, (r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_56, c_59])).
% 1.64/1.17  tff(c_69, plain, (r2_hidden('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_65])).
% 1.64/1.17  tff(c_14, plain, (![B_11, A_10]: (~r1_tarski(B_11, A_10) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.64/1.17  tff(c_73, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_69, c_14])).
% 1.64/1.17  tff(c_76, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_4, c_73])).
% 1.64/1.17  tff(c_80, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_30, c_76])).
% 1.64/1.17  tff(c_81, plain, (~r1_ordinal1('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_20])).
% 1.64/1.17  tff(c_6, plain, (![B_5, A_3]: (r2_hidden(B_5, A_3) | r1_ordinal1(A_3, B_5) | ~v3_ordinal1(B_5) | ~v3_ordinal1(A_3))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.64/1.17  tff(c_117, plain, (![A_34, B_35]: (r1_ordinal1(k1_ordinal1(A_34), B_35) | ~r2_hidden(A_34, B_35) | ~v3_ordinal1(B_35) | ~v3_ordinal1(A_34))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.64/1.17  tff(c_89, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~r1_ordinal1(A_26, B_27) | ~v3_ordinal1(B_27) | ~v3_ordinal1(A_26))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.64/1.17  tff(c_83, plain, (r2_hidden('#skF_1', k1_ordinal1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_81, c_26])).
% 1.64/1.17  tff(c_87, plain, (~r1_tarski(k1_ordinal1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_83, c_14])).
% 1.64/1.17  tff(c_92, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(resolution, [status(thm)], [c_89, c_87])).
% 1.64/1.17  tff(c_95, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_1') | ~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_92])).
% 1.64/1.17  tff(c_96, plain, (~v3_ordinal1(k1_ordinal1('#skF_2'))), inference(splitLeft, [status(thm)], [c_95])).
% 1.64/1.17  tff(c_99, plain, (~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_96])).
% 1.64/1.17  tff(c_103, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_99])).
% 1.64/1.17  tff(c_104, plain, (~r1_ordinal1(k1_ordinal1('#skF_2'), '#skF_1')), inference(splitRight, [status(thm)], [c_95])).
% 1.64/1.17  tff(c_123, plain, (~r2_hidden('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_117, c_104])).
% 1.64/1.17  tff(c_127, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18, c_123])).
% 1.64/1.17  tff(c_130, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_127])).
% 1.64/1.17  tff(c_133, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_130])).
% 1.64/1.17  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_133])).
% 1.64/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.17  
% 1.64/1.17  Inference rules
% 1.64/1.17  ----------------------
% 1.64/1.17  #Ref     : 0
% 1.64/1.17  #Sup     : 16
% 1.64/1.17  #Fact    : 0
% 1.64/1.17  #Define  : 0
% 1.64/1.17  #Split   : 3
% 1.64/1.17  #Chain   : 0
% 1.64/1.17  #Close   : 0
% 1.64/1.17  
% 1.64/1.17  Ordering : KBO
% 1.64/1.17  
% 1.64/1.17  Simplification rules
% 1.64/1.17  ----------------------
% 1.64/1.17  #Subsume      : 2
% 1.64/1.17  #Demod        : 14
% 1.64/1.17  #Tautology    : 7
% 1.64/1.17  #SimpNegUnit  : 3
% 1.64/1.17  #BackRed      : 0
% 1.64/1.17  
% 1.64/1.17  #Partial instantiations: 0
% 1.64/1.17  #Strategies tried      : 1
% 1.64/1.17  
% 1.64/1.17  Timing (in seconds)
% 1.64/1.17  ----------------------
% 1.64/1.18  Preprocessing        : 0.27
% 1.64/1.18  Parsing              : 0.15
% 1.64/1.18  CNF conversion       : 0.02
% 1.64/1.18  Main loop            : 0.15
% 1.64/1.18  Inferencing          : 0.06
% 1.64/1.18  Reduction            : 0.04
% 1.64/1.18  Demodulation         : 0.02
% 1.64/1.18  BG Simplification    : 0.01
% 1.64/1.18  Subsumption          : 0.02
% 1.64/1.18  Abstraction          : 0.01
% 1.64/1.18  MUC search           : 0.00
% 1.64/1.18  Cooper               : 0.00
% 1.64/1.18  Total                : 0.45
% 1.64/1.18  Index Insertion      : 0.00
% 1.64/1.18  Index Deletion       : 0.00
% 1.64/1.18  Index Matching       : 0.00
% 1.64/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
