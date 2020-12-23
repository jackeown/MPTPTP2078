%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:47 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 185 expanded)
%              Number of leaves         :   19 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  129 ( 642 expanded)
%              Number of equality atoms :   11 (  52 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_wellord1 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( ( v2_wellord1(C)
            & r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C))
            & ! [D] :
                ( r2_hidden(D,k1_wellord1(C,A))
               => ( r2_hidden(k4_tarski(D,B),C)
                  & D != B ) ) )
         => r2_hidden(k4_tarski(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_wellord1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( v2_wellord1(C)
          & r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) )
       => ( r2_hidden(k4_tarski(A,B),C)
        <=> r1_tarski(k1_wellord1(C,A),k1_wellord1(C,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( v2_wellord1(C)
          & r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) )
       => ( r1_tarski(k1_wellord1(C,A),k1_wellord1(C,B))
        <=> ( A = B
            | r2_hidden(A,k1_wellord1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_wellord1)).

tff(c_22,plain,(
    ~ r2_hidden(k4_tarski('#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_30,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_28,plain,(
    v2_wellord1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_26,plain,(
    r2_hidden('#skF_2',k3_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_24,plain,(
    r2_hidden('#skF_3',k3_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_36,plain,(
    ! [A_19,B_20] :
      ( ~ r2_hidden('#skF_1'(A_19,B_20),B_20)
      | r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_41,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_36])).

tff(c_34,plain,(
    ! [D_16] :
      ( r2_hidden(k4_tarski(D_16,'#skF_3'),'#skF_4')
      | ~ r2_hidden(D_16,k1_wellord1('#skF_4','#skF_2')) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_48,plain,(
    ! [C_23,B_24,A_25] :
      ( r2_hidden(C_23,B_24)
      | ~ r2_hidden(C_23,A_25)
      | ~ r1_tarski(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_109,plain,(
    ! [D_38,B_39] :
      ( r2_hidden(k4_tarski(D_38,'#skF_3'),B_39)
      | ~ r1_tarski('#skF_4',B_39)
      | ~ r2_hidden(D_38,k1_wellord1('#skF_4','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_34,c_48])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( r2_hidden(A_6,k3_relat_1(C_8))
      | ~ r2_hidden(k4_tarski(A_6,B_7),C_8)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_132,plain,(
    ! [D_40,B_41] :
      ( r2_hidden(D_40,k3_relat_1(B_41))
      | ~ v1_relat_1(B_41)
      | ~ r1_tarski('#skF_4',B_41)
      | ~ r2_hidden(D_40,k1_wellord1('#skF_4','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_109,c_10])).

tff(c_144,plain,(
    ! [B_2,B_41] :
      ( r2_hidden('#skF_1'(k1_wellord1('#skF_4','#skF_2'),B_2),k3_relat_1(B_41))
      | ~ v1_relat_1(B_41)
      | ~ r1_tarski('#skF_4',B_41)
      | r1_tarski(k1_wellord1('#skF_4','#skF_2'),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_132])).

tff(c_58,plain,(
    ! [A_1,B_2,B_24] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_24)
      | ~ r1_tarski(A_1,B_24)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_48])).

tff(c_14,plain,(
    ! [C_11,A_9,B_10] :
      ( r1_tarski(k1_wellord1(C_11,A_9),k1_wellord1(C_11,B_10))
      | ~ r2_hidden(k4_tarski(A_9,B_10),C_11)
      | ~ r2_hidden(B_10,k3_relat_1(C_11))
      | ~ r2_hidden(A_9,k3_relat_1(C_11))
      | ~ v2_wellord1(C_11)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_583,plain,(
    ! [A_114,C_115,B_116] :
      ( r2_hidden(A_114,k1_wellord1(C_115,B_116))
      | B_116 = A_114
      | ~ r1_tarski(k1_wellord1(C_115,A_114),k1_wellord1(C_115,B_116))
      | ~ r2_hidden(B_116,k3_relat_1(C_115))
      | ~ r2_hidden(A_114,k3_relat_1(C_115))
      | ~ v2_wellord1(C_115)
      | ~ v1_relat_1(C_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_709,plain,(
    ! [A_137,C_138,B_139] :
      ( r2_hidden(A_137,k1_wellord1(C_138,B_139))
      | B_139 = A_137
      | ~ r2_hidden(k4_tarski(A_137,B_139),C_138)
      | ~ r2_hidden(B_139,k3_relat_1(C_138))
      | ~ r2_hidden(A_137,k3_relat_1(C_138))
      | ~ v2_wellord1(C_138)
      | ~ v1_relat_1(C_138) ) ),
    inference(resolution,[status(thm)],[c_14,c_583])).

tff(c_721,plain,(
    ! [D_16] :
      ( r2_hidden(D_16,k1_wellord1('#skF_4','#skF_3'))
      | D_16 = '#skF_3'
      | ~ r2_hidden('#skF_3',k3_relat_1('#skF_4'))
      | ~ r2_hidden(D_16,k3_relat_1('#skF_4'))
      | ~ v2_wellord1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ r2_hidden(D_16,k1_wellord1('#skF_4','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_34,c_709])).

tff(c_729,plain,(
    ! [D_140] :
      ( r2_hidden(D_140,k1_wellord1('#skF_4','#skF_3'))
      | D_140 = '#skF_3'
      | ~ r2_hidden(D_140,k3_relat_1('#skF_4'))
      | ~ r2_hidden(D_140,k1_wellord1('#skF_4','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_24,c_721])).

tff(c_843,plain,(
    ! [A_151,B_152] :
      ( r2_hidden('#skF_1'(A_151,B_152),k1_wellord1('#skF_4','#skF_3'))
      | '#skF_1'(A_151,B_152) = '#skF_3'
      | ~ r2_hidden('#skF_1'(A_151,B_152),k3_relat_1('#skF_4'))
      | ~ r1_tarski(A_151,k1_wellord1('#skF_4','#skF_2'))
      | r1_tarski(A_151,B_152) ) ),
    inference(resolution,[status(thm)],[c_58,c_729])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_852,plain,(
    ! [A_153] :
      ( '#skF_1'(A_153,k1_wellord1('#skF_4','#skF_3')) = '#skF_3'
      | ~ r2_hidden('#skF_1'(A_153,k1_wellord1('#skF_4','#skF_3')),k3_relat_1('#skF_4'))
      | ~ r1_tarski(A_153,k1_wellord1('#skF_4','#skF_2'))
      | r1_tarski(A_153,k1_wellord1('#skF_4','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_843,c_4])).

tff(c_868,plain,
    ( '#skF_1'(k1_wellord1('#skF_4','#skF_2'),k1_wellord1('#skF_4','#skF_3')) = '#skF_3'
    | ~ r1_tarski(k1_wellord1('#skF_4','#skF_2'),k1_wellord1('#skF_4','#skF_2'))
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_4','#skF_4')
    | r1_tarski(k1_wellord1('#skF_4','#skF_2'),k1_wellord1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_144,c_852])).

tff(c_900,plain,
    ( '#skF_1'(k1_wellord1('#skF_4','#skF_2'),k1_wellord1('#skF_4','#skF_3')) = '#skF_3'
    | r1_tarski(k1_wellord1('#skF_4','#skF_2'),k1_wellord1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_30,c_41,c_868])).

tff(c_913,plain,(
    r1_tarski(k1_wellord1('#skF_4','#skF_2'),k1_wellord1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_900])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] :
      ( r2_hidden(k4_tarski(A_9,B_10),C_11)
      | ~ r1_tarski(k1_wellord1(C_11,A_9),k1_wellord1(C_11,B_10))
      | ~ r2_hidden(B_10,k3_relat_1(C_11))
      | ~ r2_hidden(A_9,k3_relat_1(C_11))
      | ~ v2_wellord1(C_11)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_929,plain,
    ( r2_hidden(k4_tarski('#skF_2','#skF_3'),'#skF_4')
    | ~ r2_hidden('#skF_3',k3_relat_1('#skF_4'))
    | ~ r2_hidden('#skF_2',k3_relat_1('#skF_4'))
    | ~ v2_wellord1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_913,c_12])).

tff(c_951,plain,(
    r2_hidden(k4_tarski('#skF_2','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_28,c_26,c_24,c_929])).

tff(c_953,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_951])).

tff(c_955,plain,(
    ~ r1_tarski(k1_wellord1('#skF_4','#skF_2'),k1_wellord1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_900])).

tff(c_32,plain,(
    ~ r2_hidden('#skF_3',k1_wellord1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_954,plain,(
    '#skF_1'(k1_wellord1('#skF_4','#skF_2'),k1_wellord1('#skF_4','#skF_3')) = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_900])).

tff(c_1011,plain,
    ( r2_hidden('#skF_3',k1_wellord1('#skF_4','#skF_2'))
    | r1_tarski(k1_wellord1('#skF_4','#skF_2'),k1_wellord1('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_954,c_6])).

tff(c_1042,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_955,c_32,c_1011])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:50:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.53  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.53  
% 3.32/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.53  %$ r2_hidden > r1_tarski > v2_wellord1 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.32/1.53  
% 3.32/1.53  %Foreground sorts:
% 3.32/1.53  
% 3.32/1.53  
% 3.32/1.53  %Background operators:
% 3.32/1.53  
% 3.32/1.53  
% 3.32/1.53  %Foreground operators:
% 3.32/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.32/1.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.32/1.53  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.32/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.32/1.53  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 3.32/1.53  tff('#skF_2', type, '#skF_2': $i).
% 3.32/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.53  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.32/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.32/1.53  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 3.32/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.32/1.53  
% 3.46/1.55  tff(f_85, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => ((((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) & (![D]: (r2_hidden(D, k1_wellord1(C, A)) => (r2_hidden(k4_tarski(D, B), C) & ~(D = B))))) => r2_hidden(k4_tarski(A, B), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_wellord1)).
% 3.46/1.55  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.46/1.55  tff(f_40, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 3.46/1.55  tff(f_52, axiom, (![A, B, C]: (v1_relat_1(C) => (((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) => (r2_hidden(k4_tarski(A, B), C) <=> r1_tarski(k1_wellord1(C, A), k1_wellord1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_wellord1)).
% 3.46/1.55  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) => (r1_tarski(k1_wellord1(C, A), k1_wellord1(C, B)) <=> ((A = B) | r2_hidden(A, k1_wellord1(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_wellord1)).
% 3.46/1.55  tff(c_22, plain, (~r2_hidden(k4_tarski('#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.46/1.55  tff(c_30, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.46/1.55  tff(c_28, plain, (v2_wellord1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.46/1.55  tff(c_26, plain, (r2_hidden('#skF_2', k3_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.46/1.55  tff(c_24, plain, (r2_hidden('#skF_3', k3_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.46/1.55  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.46/1.55  tff(c_36, plain, (![A_19, B_20]: (~r2_hidden('#skF_1'(A_19, B_20), B_20) | r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.46/1.55  tff(c_41, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_36])).
% 3.46/1.55  tff(c_34, plain, (![D_16]: (r2_hidden(k4_tarski(D_16, '#skF_3'), '#skF_4') | ~r2_hidden(D_16, k1_wellord1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.46/1.55  tff(c_48, plain, (![C_23, B_24, A_25]: (r2_hidden(C_23, B_24) | ~r2_hidden(C_23, A_25) | ~r1_tarski(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.46/1.55  tff(c_109, plain, (![D_38, B_39]: (r2_hidden(k4_tarski(D_38, '#skF_3'), B_39) | ~r1_tarski('#skF_4', B_39) | ~r2_hidden(D_38, k1_wellord1('#skF_4', '#skF_2')))), inference(resolution, [status(thm)], [c_34, c_48])).
% 3.46/1.55  tff(c_10, plain, (![A_6, C_8, B_7]: (r2_hidden(A_6, k3_relat_1(C_8)) | ~r2_hidden(k4_tarski(A_6, B_7), C_8) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.46/1.55  tff(c_132, plain, (![D_40, B_41]: (r2_hidden(D_40, k3_relat_1(B_41)) | ~v1_relat_1(B_41) | ~r1_tarski('#skF_4', B_41) | ~r2_hidden(D_40, k1_wellord1('#skF_4', '#skF_2')))), inference(resolution, [status(thm)], [c_109, c_10])).
% 3.46/1.55  tff(c_144, plain, (![B_2, B_41]: (r2_hidden('#skF_1'(k1_wellord1('#skF_4', '#skF_2'), B_2), k3_relat_1(B_41)) | ~v1_relat_1(B_41) | ~r1_tarski('#skF_4', B_41) | r1_tarski(k1_wellord1('#skF_4', '#skF_2'), B_2))), inference(resolution, [status(thm)], [c_6, c_132])).
% 3.46/1.55  tff(c_58, plain, (![A_1, B_2, B_24]: (r2_hidden('#skF_1'(A_1, B_2), B_24) | ~r1_tarski(A_1, B_24) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_48])).
% 3.46/1.55  tff(c_14, plain, (![C_11, A_9, B_10]: (r1_tarski(k1_wellord1(C_11, A_9), k1_wellord1(C_11, B_10)) | ~r2_hidden(k4_tarski(A_9, B_10), C_11) | ~r2_hidden(B_10, k3_relat_1(C_11)) | ~r2_hidden(A_9, k3_relat_1(C_11)) | ~v2_wellord1(C_11) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.46/1.55  tff(c_583, plain, (![A_114, C_115, B_116]: (r2_hidden(A_114, k1_wellord1(C_115, B_116)) | B_116=A_114 | ~r1_tarski(k1_wellord1(C_115, A_114), k1_wellord1(C_115, B_116)) | ~r2_hidden(B_116, k3_relat_1(C_115)) | ~r2_hidden(A_114, k3_relat_1(C_115)) | ~v2_wellord1(C_115) | ~v1_relat_1(C_115))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.46/1.55  tff(c_709, plain, (![A_137, C_138, B_139]: (r2_hidden(A_137, k1_wellord1(C_138, B_139)) | B_139=A_137 | ~r2_hidden(k4_tarski(A_137, B_139), C_138) | ~r2_hidden(B_139, k3_relat_1(C_138)) | ~r2_hidden(A_137, k3_relat_1(C_138)) | ~v2_wellord1(C_138) | ~v1_relat_1(C_138))), inference(resolution, [status(thm)], [c_14, c_583])).
% 3.46/1.55  tff(c_721, plain, (![D_16]: (r2_hidden(D_16, k1_wellord1('#skF_4', '#skF_3')) | D_16='#skF_3' | ~r2_hidden('#skF_3', k3_relat_1('#skF_4')) | ~r2_hidden(D_16, k3_relat_1('#skF_4')) | ~v2_wellord1('#skF_4') | ~v1_relat_1('#skF_4') | ~r2_hidden(D_16, k1_wellord1('#skF_4', '#skF_2')))), inference(resolution, [status(thm)], [c_34, c_709])).
% 3.46/1.55  tff(c_729, plain, (![D_140]: (r2_hidden(D_140, k1_wellord1('#skF_4', '#skF_3')) | D_140='#skF_3' | ~r2_hidden(D_140, k3_relat_1('#skF_4')) | ~r2_hidden(D_140, k1_wellord1('#skF_4', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_24, c_721])).
% 3.46/1.55  tff(c_843, plain, (![A_151, B_152]: (r2_hidden('#skF_1'(A_151, B_152), k1_wellord1('#skF_4', '#skF_3')) | '#skF_1'(A_151, B_152)='#skF_3' | ~r2_hidden('#skF_1'(A_151, B_152), k3_relat_1('#skF_4')) | ~r1_tarski(A_151, k1_wellord1('#skF_4', '#skF_2')) | r1_tarski(A_151, B_152))), inference(resolution, [status(thm)], [c_58, c_729])).
% 3.46/1.55  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.46/1.55  tff(c_852, plain, (![A_153]: ('#skF_1'(A_153, k1_wellord1('#skF_4', '#skF_3'))='#skF_3' | ~r2_hidden('#skF_1'(A_153, k1_wellord1('#skF_4', '#skF_3')), k3_relat_1('#skF_4')) | ~r1_tarski(A_153, k1_wellord1('#skF_4', '#skF_2')) | r1_tarski(A_153, k1_wellord1('#skF_4', '#skF_3')))), inference(resolution, [status(thm)], [c_843, c_4])).
% 3.46/1.55  tff(c_868, plain, ('#skF_1'(k1_wellord1('#skF_4', '#skF_2'), k1_wellord1('#skF_4', '#skF_3'))='#skF_3' | ~r1_tarski(k1_wellord1('#skF_4', '#skF_2'), k1_wellord1('#skF_4', '#skF_2')) | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_4', '#skF_4') | r1_tarski(k1_wellord1('#skF_4', '#skF_2'), k1_wellord1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_144, c_852])).
% 3.46/1.55  tff(c_900, plain, ('#skF_1'(k1_wellord1('#skF_4', '#skF_2'), k1_wellord1('#skF_4', '#skF_3'))='#skF_3' | r1_tarski(k1_wellord1('#skF_4', '#skF_2'), k1_wellord1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_41, c_30, c_41, c_868])).
% 3.46/1.55  tff(c_913, plain, (r1_tarski(k1_wellord1('#skF_4', '#skF_2'), k1_wellord1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_900])).
% 3.46/1.55  tff(c_12, plain, (![A_9, B_10, C_11]: (r2_hidden(k4_tarski(A_9, B_10), C_11) | ~r1_tarski(k1_wellord1(C_11, A_9), k1_wellord1(C_11, B_10)) | ~r2_hidden(B_10, k3_relat_1(C_11)) | ~r2_hidden(A_9, k3_relat_1(C_11)) | ~v2_wellord1(C_11) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.46/1.55  tff(c_929, plain, (r2_hidden(k4_tarski('#skF_2', '#skF_3'), '#skF_4') | ~r2_hidden('#skF_3', k3_relat_1('#skF_4')) | ~r2_hidden('#skF_2', k3_relat_1('#skF_4')) | ~v2_wellord1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_913, c_12])).
% 3.46/1.55  tff(c_951, plain, (r2_hidden(k4_tarski('#skF_2', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_28, c_26, c_24, c_929])).
% 3.46/1.55  tff(c_953, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_951])).
% 3.46/1.55  tff(c_955, plain, (~r1_tarski(k1_wellord1('#skF_4', '#skF_2'), k1_wellord1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_900])).
% 3.46/1.55  tff(c_32, plain, (~r2_hidden('#skF_3', k1_wellord1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.46/1.55  tff(c_954, plain, ('#skF_1'(k1_wellord1('#skF_4', '#skF_2'), k1_wellord1('#skF_4', '#skF_3'))='#skF_3'), inference(splitRight, [status(thm)], [c_900])).
% 3.46/1.55  tff(c_1011, plain, (r2_hidden('#skF_3', k1_wellord1('#skF_4', '#skF_2')) | r1_tarski(k1_wellord1('#skF_4', '#skF_2'), k1_wellord1('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_954, c_6])).
% 3.46/1.55  tff(c_1042, plain, $false, inference(negUnitSimplification, [status(thm)], [c_955, c_32, c_1011])).
% 3.46/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.55  
% 3.46/1.55  Inference rules
% 3.46/1.55  ----------------------
% 3.46/1.55  #Ref     : 0
% 3.46/1.55  #Sup     : 221
% 3.46/1.55  #Fact    : 0
% 3.46/1.55  #Define  : 0
% 3.46/1.55  #Split   : 5
% 3.46/1.55  #Chain   : 0
% 3.46/1.55  #Close   : 0
% 3.46/1.55  
% 3.46/1.55  Ordering : KBO
% 3.46/1.55  
% 3.46/1.55  Simplification rules
% 3.46/1.55  ----------------------
% 3.46/1.55  #Subsume      : 85
% 3.46/1.55  #Demod        : 110
% 3.46/1.55  #Tautology    : 33
% 3.46/1.55  #SimpNegUnit  : 15
% 3.46/1.55  #BackRed      : 0
% 3.46/1.55  
% 3.46/1.55  #Partial instantiations: 0
% 3.46/1.55  #Strategies tried      : 1
% 3.46/1.55  
% 3.46/1.55  Timing (in seconds)
% 3.46/1.55  ----------------------
% 3.46/1.55  Preprocessing        : 0.26
% 3.46/1.55  Parsing              : 0.14
% 3.46/1.55  CNF conversion       : 0.02
% 3.46/1.55  Main loop            : 0.49
% 3.46/1.55  Inferencing          : 0.17
% 3.46/1.55  Reduction            : 0.13
% 3.46/1.55  Demodulation         : 0.09
% 3.46/1.55  BG Simplification    : 0.02
% 3.46/1.55  Subsumption          : 0.14
% 3.46/1.55  Abstraction          : 0.02
% 3.46/1.55  MUC search           : 0.00
% 3.46/1.55  Cooper               : 0.00
% 3.46/1.55  Total                : 0.78
% 3.46/1.55  Index Insertion      : 0.00
% 3.46/1.55  Index Deletion       : 0.00
% 3.46/1.55  Index Matching       : 0.00
% 3.46/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
