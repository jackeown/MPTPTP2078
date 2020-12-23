%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:21 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   48 (  61 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   57 (  89 expanded)
%              Number of equality atoms :   11 (  21 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> r2_hidden(B,k11_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(c_4,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_35,plain,(
    ! [A_30,B_31] :
      ( ~ r2_hidden(A_30,B_31)
      | ~ r1_xboole_0(k1_tarski(A_30),B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_40,plain,(
    ! [A_30] : ~ r2_hidden(A_30,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_35])).

tff(c_26,plain,
    ( k11_relat_1('#skF_7','#skF_6') = k1_xboole_0
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_48,plain,(
    ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_32,plain,
    ( r2_hidden('#skF_6',k1_relat_1('#skF_7'))
    | k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_49,plain,(
    k11_relat_1('#skF_7','#skF_6') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_32])).

tff(c_24,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_51,plain,(
    ! [A_36,B_37,C_38] :
      ( r2_hidden(k4_tarski(A_36,B_37),C_38)
      | ~ r2_hidden(B_37,k11_relat_1(C_38,A_36))
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [C_21,A_6,D_24] :
      ( r2_hidden(C_21,k1_relat_1(A_6))
      | ~ r2_hidden(k4_tarski(C_21,D_24),A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_62,plain,(
    ! [A_39,C_40,B_41] :
      ( r2_hidden(A_39,k1_relat_1(C_40))
      | ~ r2_hidden(B_41,k11_relat_1(C_40,A_39))
      | ~ v1_relat_1(C_40) ) ),
    inference(resolution,[status(thm)],[c_51,c_10])).

tff(c_71,plain,(
    ! [A_42,C_43] :
      ( r2_hidden(A_42,k1_relat_1(C_43))
      | ~ v1_relat_1(C_43)
      | k11_relat_1(C_43,A_42) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_62])).

tff(c_78,plain,
    ( ~ v1_relat_1('#skF_7')
    | k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_71,c_48])).

tff(c_82,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_78])).

tff(c_84,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_82])).

tff(c_86,plain,(
    r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_85,plain,(
    k11_relat_1('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_134,plain,(
    ! [C_58,A_59] :
      ( r2_hidden(k4_tarski(C_58,'#skF_5'(A_59,k1_relat_1(A_59),C_58)),A_59)
      | ~ r2_hidden(C_58,k1_relat_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [B_26,C_27,A_25] :
      ( r2_hidden(B_26,k11_relat_1(C_27,A_25))
      | ~ r2_hidden(k4_tarski(A_25,B_26),C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_723,plain,(
    ! [A_95,C_96] :
      ( r2_hidden('#skF_5'(A_95,k1_relat_1(A_95),C_96),k11_relat_1(A_95,C_96))
      | ~ v1_relat_1(A_95)
      | ~ r2_hidden(C_96,k1_relat_1(A_95)) ) ),
    inference(resolution,[status(thm)],[c_134,c_22])).

tff(c_743,plain,
    ( r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0)
    | ~ v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_6',k1_relat_1('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_723])).

tff(c_748,plain,(
    r2_hidden('#skF_5'('#skF_7',k1_relat_1('#skF_7'),'#skF_6'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_24,c_743])).

tff(c_750,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_748])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.40  
% 2.67/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.40  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_4
% 2.67/1.40  
% 2.67/1.40  %Foreground sorts:
% 2.67/1.40  
% 2.67/1.40  
% 2.67/1.40  %Background operators:
% 2.67/1.40  
% 2.67/1.40  
% 2.67/1.40  %Foreground operators:
% 2.67/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.67/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.67/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.67/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.67/1.40  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.67/1.40  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 2.67/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.67/1.40  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.67/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.67/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.67/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.67/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.67/1.40  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.67/1.40  
% 2.67/1.41  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.67/1.41  tff(f_40, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.67/1.41  tff(f_62, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t205_relat_1)).
% 2.67/1.41  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.67/1.41  tff(f_54, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) <=> r2_hidden(B, k11_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t204_relat_1)).
% 2.67/1.41  tff(f_48, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 2.67/1.41  tff(c_4, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.67/1.41  tff(c_35, plain, (![A_30, B_31]: (~r2_hidden(A_30, B_31) | ~r1_xboole_0(k1_tarski(A_30), B_31))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.67/1.41  tff(c_40, plain, (![A_30]: (~r2_hidden(A_30, k1_xboole_0))), inference(resolution, [status(thm)], [c_4, c_35])).
% 2.67/1.41  tff(c_26, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0 | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.67/1.41  tff(c_48, plain, (~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_26])).
% 2.67/1.41  tff(c_32, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7')) | k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.67/1.41  tff(c_49, plain, (k11_relat_1('#skF_7', '#skF_6')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_48, c_32])).
% 2.67/1.41  tff(c_24, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.67/1.41  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.67/1.41  tff(c_51, plain, (![A_36, B_37, C_38]: (r2_hidden(k4_tarski(A_36, B_37), C_38) | ~r2_hidden(B_37, k11_relat_1(C_38, A_36)) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.67/1.41  tff(c_10, plain, (![C_21, A_6, D_24]: (r2_hidden(C_21, k1_relat_1(A_6)) | ~r2_hidden(k4_tarski(C_21, D_24), A_6))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.67/1.41  tff(c_62, plain, (![A_39, C_40, B_41]: (r2_hidden(A_39, k1_relat_1(C_40)) | ~r2_hidden(B_41, k11_relat_1(C_40, A_39)) | ~v1_relat_1(C_40))), inference(resolution, [status(thm)], [c_51, c_10])).
% 2.67/1.41  tff(c_71, plain, (![A_42, C_43]: (r2_hidden(A_42, k1_relat_1(C_43)) | ~v1_relat_1(C_43) | k11_relat_1(C_43, A_42)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_62])).
% 2.67/1.41  tff(c_78, plain, (~v1_relat_1('#skF_7') | k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_71, c_48])).
% 2.67/1.41  tff(c_82, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_78])).
% 2.67/1.41  tff(c_84, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_82])).
% 2.67/1.41  tff(c_86, plain, (r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_26])).
% 2.67/1.41  tff(c_85, plain, (k11_relat_1('#skF_7', '#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_26])).
% 2.67/1.41  tff(c_134, plain, (![C_58, A_59]: (r2_hidden(k4_tarski(C_58, '#skF_5'(A_59, k1_relat_1(A_59), C_58)), A_59) | ~r2_hidden(C_58, k1_relat_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.67/1.41  tff(c_22, plain, (![B_26, C_27, A_25]: (r2_hidden(B_26, k11_relat_1(C_27, A_25)) | ~r2_hidden(k4_tarski(A_25, B_26), C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.67/1.41  tff(c_723, plain, (![A_95, C_96]: (r2_hidden('#skF_5'(A_95, k1_relat_1(A_95), C_96), k11_relat_1(A_95, C_96)) | ~v1_relat_1(A_95) | ~r2_hidden(C_96, k1_relat_1(A_95)))), inference(resolution, [status(thm)], [c_134, c_22])).
% 2.67/1.41  tff(c_743, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0) | ~v1_relat_1('#skF_7') | ~r2_hidden('#skF_6', k1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_85, c_723])).
% 2.67/1.41  tff(c_748, plain, (r2_hidden('#skF_5'('#skF_7', k1_relat_1('#skF_7'), '#skF_6'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_24, c_743])).
% 2.67/1.41  tff(c_750, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_748])).
% 2.67/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.41  
% 2.67/1.41  Inference rules
% 2.67/1.41  ----------------------
% 2.67/1.41  #Ref     : 0
% 2.67/1.41  #Sup     : 153
% 2.67/1.41  #Fact    : 0
% 2.67/1.41  #Define  : 0
% 2.67/1.41  #Split   : 3
% 2.67/1.41  #Chain   : 0
% 2.67/1.41  #Close   : 0
% 2.67/1.41  
% 2.67/1.41  Ordering : KBO
% 2.67/1.41  
% 2.67/1.41  Simplification rules
% 2.67/1.41  ----------------------
% 2.67/1.41  #Subsume      : 35
% 2.67/1.41  #Demod        : 66
% 2.67/1.41  #Tautology    : 29
% 2.67/1.41  #SimpNegUnit  : 30
% 2.67/1.41  #BackRed      : 1
% 2.67/1.41  
% 2.67/1.41  #Partial instantiations: 0
% 2.67/1.41  #Strategies tried      : 1
% 2.67/1.41  
% 2.67/1.41  Timing (in seconds)
% 2.67/1.41  ----------------------
% 2.67/1.41  Preprocessing        : 0.26
% 2.67/1.41  Parsing              : 0.14
% 2.67/1.41  CNF conversion       : 0.02
% 2.67/1.41  Main loop            : 0.35
% 2.67/1.41  Inferencing          : 0.14
% 2.67/1.41  Reduction            : 0.09
% 2.67/1.41  Demodulation         : 0.05
% 2.67/1.41  BG Simplification    : 0.02
% 2.67/1.41  Subsumption          : 0.09
% 2.67/1.41  Abstraction          : 0.02
% 2.67/1.41  MUC search           : 0.00
% 2.67/1.41  Cooper               : 0.00
% 2.67/1.41  Total                : 0.64
% 2.67/1.41  Index Insertion      : 0.00
% 2.67/1.41  Index Deletion       : 0.00
% 2.67/1.41  Index Matching       : 0.00
% 2.67/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
