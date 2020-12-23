%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:10 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   41 (  73 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 180 expanded)
%              Number of equality atoms :    8 (  28 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( v1_relat_1(C)
         => ( C = k7_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(D,B)
                  & r2_hidden(k4_tarski(D,E),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_40,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( v1_funct_1(k7_relat_1(A_23,B_24))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [A_23,B_24] :
      ( v1_relat_1(k7_relat_1(A_23,B_24))
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_36,plain,(
    k1_funct_1(k7_relat_1('#skF_7','#skF_6'),'#skF_5') != k1_funct_1('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_38,plain,(
    r2_hidden('#skF_5',k1_relat_1(k7_relat_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_30,plain,(
    ! [A_25,C_27] :
      ( r2_hidden(k4_tarski(A_25,k1_funct_1(C_27,A_25)),C_27)
      | ~ r2_hidden(A_25,k1_relat_1(C_27))
      | ~ v1_funct_1(C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_106,plain,(
    ! [D_53,E_54,A_55,B_56] :
      ( r2_hidden(k4_tarski(D_53,E_54),A_55)
      | ~ r2_hidden(k4_tarski(D_53,E_54),k7_relat_1(A_55,B_56))
      | ~ v1_relat_1(k7_relat_1(A_55,B_56))
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_207,plain,(
    ! [A_75,A_76,B_77] :
      ( r2_hidden(k4_tarski(A_75,k1_funct_1(k7_relat_1(A_76,B_77),A_75)),A_76)
      | ~ v1_relat_1(A_76)
      | ~ r2_hidden(A_75,k1_relat_1(k7_relat_1(A_76,B_77)))
      | ~ v1_funct_1(k7_relat_1(A_76,B_77))
      | ~ v1_relat_1(k7_relat_1(A_76,B_77)) ) ),
    inference(resolution,[status(thm)],[c_30,c_106])).

tff(c_32,plain,(
    ! [C_27,A_25,B_26] :
      ( k1_funct_1(C_27,A_25) = B_26
      | ~ r2_hidden(k4_tarski(A_25,B_26),C_27)
      | ~ v1_funct_1(C_27)
      | ~ v1_relat_1(C_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_268,plain,(
    ! [A_81,B_82,A_83] :
      ( k1_funct_1(k7_relat_1(A_81,B_82),A_83) = k1_funct_1(A_81,A_83)
      | ~ v1_funct_1(A_81)
      | ~ v1_relat_1(A_81)
      | ~ r2_hidden(A_83,k1_relat_1(k7_relat_1(A_81,B_82)))
      | ~ v1_funct_1(k7_relat_1(A_81,B_82))
      | ~ v1_relat_1(k7_relat_1(A_81,B_82)) ) ),
    inference(resolution,[status(thm)],[c_207,c_32])).

tff(c_298,plain,
    ( k1_funct_1(k7_relat_1('#skF_7','#skF_6'),'#skF_5') = k1_funct_1('#skF_7','#skF_5')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_funct_1(k7_relat_1('#skF_7','#skF_6'))
    | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_38,c_268])).

tff(c_308,plain,
    ( k1_funct_1(k7_relat_1('#skF_7','#skF_6'),'#skF_5') = k1_funct_1('#skF_7','#skF_5')
    | ~ v1_funct_1(k7_relat_1('#skF_7','#skF_6'))
    | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_298])).

tff(c_309,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_7','#skF_6'))
    | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_308])).

tff(c_310,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_309])).

tff(c_392,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_310])).

tff(c_396,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_392])).

tff(c_397,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_309])).

tff(c_401,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_26,c_397])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_401])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.56/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.39  
% 2.56/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.39  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.56/1.39  
% 2.56/1.39  %Foreground sorts:
% 2.56/1.39  
% 2.56/1.39  
% 2.56/1.39  %Background operators:
% 2.56/1.39  
% 2.56/1.39  
% 2.56/1.39  %Foreground operators:
% 2.56/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.56/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.56/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.56/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.56/1.39  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.56/1.39  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.56/1.39  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.56/1.39  tff('#skF_7', type, '#skF_7': $i).
% 2.56/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.56/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.56/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.56/1.39  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.56/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.56/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.56/1.39  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.56/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.56/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.56/1.39  
% 2.85/1.40  tff(f_74, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_funct_1)).
% 2.85/1.40  tff(f_55, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 2.85/1.40  tff(f_65, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.85/1.40  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_relat_1)).
% 2.85/1.40  tff(c_42, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.85/1.40  tff(c_40, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.85/1.40  tff(c_26, plain, (![A_23, B_24]: (v1_funct_1(k7_relat_1(A_23, B_24)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.85/1.40  tff(c_28, plain, (![A_23, B_24]: (v1_relat_1(k7_relat_1(A_23, B_24)) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.85/1.40  tff(c_36, plain, (k1_funct_1(k7_relat_1('#skF_7', '#skF_6'), '#skF_5')!=k1_funct_1('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.85/1.40  tff(c_38, plain, (r2_hidden('#skF_5', k1_relat_1(k7_relat_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.85/1.40  tff(c_30, plain, (![A_25, C_27]: (r2_hidden(k4_tarski(A_25, k1_funct_1(C_27, A_25)), C_27) | ~r2_hidden(A_25, k1_relat_1(C_27)) | ~v1_funct_1(C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.85/1.40  tff(c_106, plain, (![D_53, E_54, A_55, B_56]: (r2_hidden(k4_tarski(D_53, E_54), A_55) | ~r2_hidden(k4_tarski(D_53, E_54), k7_relat_1(A_55, B_56)) | ~v1_relat_1(k7_relat_1(A_55, B_56)) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.85/1.40  tff(c_207, plain, (![A_75, A_76, B_77]: (r2_hidden(k4_tarski(A_75, k1_funct_1(k7_relat_1(A_76, B_77), A_75)), A_76) | ~v1_relat_1(A_76) | ~r2_hidden(A_75, k1_relat_1(k7_relat_1(A_76, B_77))) | ~v1_funct_1(k7_relat_1(A_76, B_77)) | ~v1_relat_1(k7_relat_1(A_76, B_77)))), inference(resolution, [status(thm)], [c_30, c_106])).
% 2.85/1.40  tff(c_32, plain, (![C_27, A_25, B_26]: (k1_funct_1(C_27, A_25)=B_26 | ~r2_hidden(k4_tarski(A_25, B_26), C_27) | ~v1_funct_1(C_27) | ~v1_relat_1(C_27))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.85/1.40  tff(c_268, plain, (![A_81, B_82, A_83]: (k1_funct_1(k7_relat_1(A_81, B_82), A_83)=k1_funct_1(A_81, A_83) | ~v1_funct_1(A_81) | ~v1_relat_1(A_81) | ~r2_hidden(A_83, k1_relat_1(k7_relat_1(A_81, B_82))) | ~v1_funct_1(k7_relat_1(A_81, B_82)) | ~v1_relat_1(k7_relat_1(A_81, B_82)))), inference(resolution, [status(thm)], [c_207, c_32])).
% 2.85/1.40  tff(c_298, plain, (k1_funct_1(k7_relat_1('#skF_7', '#skF_6'), '#skF_5')=k1_funct_1('#skF_7', '#skF_5') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_funct_1(k7_relat_1('#skF_7', '#skF_6')) | ~v1_relat_1(k7_relat_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_38, c_268])).
% 2.85/1.40  tff(c_308, plain, (k1_funct_1(k7_relat_1('#skF_7', '#skF_6'), '#skF_5')=k1_funct_1('#skF_7', '#skF_5') | ~v1_funct_1(k7_relat_1('#skF_7', '#skF_6')) | ~v1_relat_1(k7_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_298])).
% 2.85/1.40  tff(c_309, plain, (~v1_funct_1(k7_relat_1('#skF_7', '#skF_6')) | ~v1_relat_1(k7_relat_1('#skF_7', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_36, c_308])).
% 2.85/1.40  tff(c_310, plain, (~v1_relat_1(k7_relat_1('#skF_7', '#skF_6'))), inference(splitLeft, [status(thm)], [c_309])).
% 2.85/1.40  tff(c_392, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_28, c_310])).
% 2.85/1.40  tff(c_396, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_392])).
% 2.85/1.40  tff(c_397, plain, (~v1_funct_1(k7_relat_1('#skF_7', '#skF_6'))), inference(splitRight, [status(thm)], [c_309])).
% 2.85/1.40  tff(c_401, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_26, c_397])).
% 2.85/1.40  tff(c_405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_401])).
% 2.85/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.40  
% 2.85/1.41  Inference rules
% 2.85/1.41  ----------------------
% 2.85/1.41  #Ref     : 0
% 2.85/1.41  #Sup     : 76
% 2.85/1.41  #Fact    : 0
% 2.85/1.41  #Define  : 0
% 2.85/1.41  #Split   : 1
% 2.85/1.41  #Chain   : 0
% 2.85/1.41  #Close   : 0
% 2.85/1.41  
% 2.85/1.41  Ordering : KBO
% 2.85/1.41  
% 2.85/1.41  Simplification rules
% 2.85/1.41  ----------------------
% 2.85/1.41  #Subsume      : 4
% 2.85/1.41  #Demod        : 8
% 2.85/1.41  #Tautology    : 8
% 2.85/1.41  #SimpNegUnit  : 1
% 2.85/1.41  #BackRed      : 0
% 2.85/1.41  
% 2.85/1.41  #Partial instantiations: 0
% 2.85/1.41  #Strategies tried      : 1
% 2.85/1.41  
% 2.85/1.41  Timing (in seconds)
% 2.85/1.41  ----------------------
% 2.85/1.41  Preprocessing        : 0.31
% 2.85/1.41  Parsing              : 0.16
% 2.85/1.41  CNF conversion       : 0.03
% 2.85/1.41  Main loop            : 0.34
% 2.85/1.41  Inferencing          : 0.12
% 2.85/1.41  Reduction            : 0.08
% 2.85/1.41  Demodulation         : 0.06
% 2.85/1.41  BG Simplification    : 0.03
% 2.85/1.41  Subsumption          : 0.08
% 2.85/1.41  Abstraction          : 0.02
% 2.85/1.41  MUC search           : 0.00
% 2.85/1.41  Cooper               : 0.00
% 2.85/1.41  Total                : 0.68
% 2.85/1.41  Index Insertion      : 0.00
% 2.85/1.41  Index Deletion       : 0.00
% 2.85/1.41  Index Matching       : 0.00
% 2.85/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
