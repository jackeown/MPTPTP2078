%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:10 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 100 expanded)
%              Number of leaves         :   22 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :   87 ( 269 expanded)
%              Number of equality atoms :    8 (  31 expanded)
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

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(c_32,plain,(
    k1_funct_1(k7_relat_1('#skF_7','#skF_6'),'#skF_5') != k1_funct_1('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(k7_relat_1(A_20,B_21))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    r2_hidden('#skF_5',k1_relat_1(k7_relat_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    ! [A_24,C_26] :
      ( r2_hidden(k4_tarski(A_24,k1_funct_1(C_26,A_24)),C_26)
      | ~ r2_hidden(A_24,k1_relat_1(C_26))
      | ~ v1_funct_1(C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_53,plain,(
    ! [D_39,B_40,E_41,A_42] :
      ( r2_hidden(D_39,B_40)
      | ~ r2_hidden(k4_tarski(D_39,E_41),k7_relat_1(A_42,B_40))
      | ~ v1_relat_1(k7_relat_1(A_42,B_40))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_65,plain,(
    ! [A_47,B_48,A_49] :
      ( r2_hidden(A_47,B_48)
      | ~ v1_relat_1(A_49)
      | ~ r2_hidden(A_47,k1_relat_1(k7_relat_1(A_49,B_48)))
      | ~ v1_funct_1(k7_relat_1(A_49,B_48))
      | ~ v1_relat_1(k7_relat_1(A_49,B_48)) ) ),
    inference(resolution,[status(thm)],[c_26,c_53])).

tff(c_72,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_funct_1(k7_relat_1('#skF_7','#skF_6'))
    | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_65])).

tff(c_76,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ v1_funct_1(k7_relat_1('#skF_7','#skF_6'))
    | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_72])).

tff(c_77,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_80,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_20,c_77])).

tff(c_84,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_80])).

tff(c_86,plain,(
    v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_36,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    ! [A_22,B_23] :
      ( v1_funct_1(k7_relat_1(A_22,B_23))
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_85,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_7','#skF_6'))
    | r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_104,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_107,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_22,c_104])).

tff(c_111,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_107])).

tff(c_113,plain,(
    v1_funct_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_59,plain,(
    ! [D_43,E_44,A_45,B_46] :
      ( r2_hidden(k4_tarski(D_43,E_44),A_45)
      | ~ r2_hidden(k4_tarski(D_43,E_44),k7_relat_1(A_45,B_46))
      | ~ v1_relat_1(k7_relat_1(A_45,B_46))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_169,plain,(
    ! [A_68,A_69,B_70] :
      ( r2_hidden(k4_tarski(A_68,k1_funct_1(k7_relat_1(A_69,B_70),A_68)),A_69)
      | ~ v1_relat_1(A_69)
      | ~ r2_hidden(A_68,k1_relat_1(k7_relat_1(A_69,B_70)))
      | ~ v1_funct_1(k7_relat_1(A_69,B_70))
      | ~ v1_relat_1(k7_relat_1(A_69,B_70)) ) ),
    inference(resolution,[status(thm)],[c_26,c_59])).

tff(c_28,plain,(
    ! [C_26,A_24,B_25] :
      ( k1_funct_1(C_26,A_24) = B_25
      | ~ r2_hidden(k4_tarski(A_24,B_25),C_26)
      | ~ v1_funct_1(C_26)
      | ~ v1_relat_1(C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_484,plain,(
    ! [A_100,B_101,A_102] :
      ( k1_funct_1(k7_relat_1(A_100,B_101),A_102) = k1_funct_1(A_100,A_102)
      | ~ v1_funct_1(A_100)
      | ~ v1_relat_1(A_100)
      | ~ r2_hidden(A_102,k1_relat_1(k7_relat_1(A_100,B_101)))
      | ~ v1_funct_1(k7_relat_1(A_100,B_101))
      | ~ v1_relat_1(k7_relat_1(A_100,B_101)) ) ),
    inference(resolution,[status(thm)],[c_169,c_28])).

tff(c_538,plain,
    ( k1_funct_1(k7_relat_1('#skF_7','#skF_6'),'#skF_5') = k1_funct_1('#skF_7','#skF_5')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_funct_1(k7_relat_1('#skF_7','#skF_6'))
    | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_34,c_484])).

tff(c_554,plain,(
    k1_funct_1(k7_relat_1('#skF_7','#skF_6'),'#skF_5') = k1_funct_1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_113,c_38,c_36,c_538])).

tff(c_556,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_554])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:58:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.48  
% 2.96/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.48  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.96/1.48  
% 2.96/1.48  %Foreground sorts:
% 2.96/1.48  
% 2.96/1.48  
% 2.96/1.48  %Background operators:
% 2.96/1.48  
% 2.96/1.48  
% 2.96/1.48  %Foreground operators:
% 2.96/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.96/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.96/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.96/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.96/1.48  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.96/1.48  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.96/1.48  tff('#skF_7', type, '#skF_7': $i).
% 2.96/1.48  tff('#skF_5', type, '#skF_5': $i).
% 2.96/1.48  tff('#skF_6', type, '#skF_6': $i).
% 2.96/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.96/1.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.96/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.96/1.48  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.96/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.96/1.48  
% 2.96/1.49  tff(f_70, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_funct_1)).
% 2.96/1.49  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.96/1.49  tff(f_61, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 2.96/1.49  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_relat_1)).
% 2.96/1.49  tff(f_51, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 2.96/1.49  tff(c_32, plain, (k1_funct_1(k7_relat_1('#skF_7', '#skF_6'), '#skF_5')!=k1_funct_1('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.96/1.49  tff(c_38, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.96/1.49  tff(c_20, plain, (![A_20, B_21]: (v1_relat_1(k7_relat_1(A_20, B_21)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.96/1.49  tff(c_34, plain, (r2_hidden('#skF_5', k1_relat_1(k7_relat_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.96/1.49  tff(c_26, plain, (![A_24, C_26]: (r2_hidden(k4_tarski(A_24, k1_funct_1(C_26, A_24)), C_26) | ~r2_hidden(A_24, k1_relat_1(C_26)) | ~v1_funct_1(C_26) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.96/1.49  tff(c_53, plain, (![D_39, B_40, E_41, A_42]: (r2_hidden(D_39, B_40) | ~r2_hidden(k4_tarski(D_39, E_41), k7_relat_1(A_42, B_40)) | ~v1_relat_1(k7_relat_1(A_42, B_40)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.96/1.49  tff(c_65, plain, (![A_47, B_48, A_49]: (r2_hidden(A_47, B_48) | ~v1_relat_1(A_49) | ~r2_hidden(A_47, k1_relat_1(k7_relat_1(A_49, B_48))) | ~v1_funct_1(k7_relat_1(A_49, B_48)) | ~v1_relat_1(k7_relat_1(A_49, B_48)))), inference(resolution, [status(thm)], [c_26, c_53])).
% 2.96/1.49  tff(c_72, plain, (r2_hidden('#skF_5', '#skF_6') | ~v1_relat_1('#skF_7') | ~v1_funct_1(k7_relat_1('#skF_7', '#skF_6')) | ~v1_relat_1(k7_relat_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_65])).
% 2.96/1.49  tff(c_76, plain, (r2_hidden('#skF_5', '#skF_6') | ~v1_funct_1(k7_relat_1('#skF_7', '#skF_6')) | ~v1_relat_1(k7_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_72])).
% 2.96/1.49  tff(c_77, plain, (~v1_relat_1(k7_relat_1('#skF_7', '#skF_6'))), inference(splitLeft, [status(thm)], [c_76])).
% 2.96/1.49  tff(c_80, plain, (~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_20, c_77])).
% 2.96/1.49  tff(c_84, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_80])).
% 2.96/1.49  tff(c_86, plain, (v1_relat_1(k7_relat_1('#skF_7', '#skF_6'))), inference(splitRight, [status(thm)], [c_76])).
% 2.96/1.49  tff(c_36, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.96/1.49  tff(c_22, plain, (![A_22, B_23]: (v1_funct_1(k7_relat_1(A_22, B_23)) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.96/1.49  tff(c_85, plain, (~v1_funct_1(k7_relat_1('#skF_7', '#skF_6')) | r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_76])).
% 2.96/1.49  tff(c_104, plain, (~v1_funct_1(k7_relat_1('#skF_7', '#skF_6'))), inference(splitLeft, [status(thm)], [c_85])).
% 2.96/1.49  tff(c_107, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_22, c_104])).
% 2.96/1.49  tff(c_111, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_107])).
% 2.96/1.49  tff(c_113, plain, (v1_funct_1(k7_relat_1('#skF_7', '#skF_6'))), inference(splitRight, [status(thm)], [c_85])).
% 2.96/1.49  tff(c_59, plain, (![D_43, E_44, A_45, B_46]: (r2_hidden(k4_tarski(D_43, E_44), A_45) | ~r2_hidden(k4_tarski(D_43, E_44), k7_relat_1(A_45, B_46)) | ~v1_relat_1(k7_relat_1(A_45, B_46)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.96/1.49  tff(c_169, plain, (![A_68, A_69, B_70]: (r2_hidden(k4_tarski(A_68, k1_funct_1(k7_relat_1(A_69, B_70), A_68)), A_69) | ~v1_relat_1(A_69) | ~r2_hidden(A_68, k1_relat_1(k7_relat_1(A_69, B_70))) | ~v1_funct_1(k7_relat_1(A_69, B_70)) | ~v1_relat_1(k7_relat_1(A_69, B_70)))), inference(resolution, [status(thm)], [c_26, c_59])).
% 2.96/1.49  tff(c_28, plain, (![C_26, A_24, B_25]: (k1_funct_1(C_26, A_24)=B_25 | ~r2_hidden(k4_tarski(A_24, B_25), C_26) | ~v1_funct_1(C_26) | ~v1_relat_1(C_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.96/1.49  tff(c_484, plain, (![A_100, B_101, A_102]: (k1_funct_1(k7_relat_1(A_100, B_101), A_102)=k1_funct_1(A_100, A_102) | ~v1_funct_1(A_100) | ~v1_relat_1(A_100) | ~r2_hidden(A_102, k1_relat_1(k7_relat_1(A_100, B_101))) | ~v1_funct_1(k7_relat_1(A_100, B_101)) | ~v1_relat_1(k7_relat_1(A_100, B_101)))), inference(resolution, [status(thm)], [c_169, c_28])).
% 2.96/1.49  tff(c_538, plain, (k1_funct_1(k7_relat_1('#skF_7', '#skF_6'), '#skF_5')=k1_funct_1('#skF_7', '#skF_5') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_funct_1(k7_relat_1('#skF_7', '#skF_6')) | ~v1_relat_1(k7_relat_1('#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_34, c_484])).
% 2.96/1.49  tff(c_554, plain, (k1_funct_1(k7_relat_1('#skF_7', '#skF_6'), '#skF_5')=k1_funct_1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_113, c_38, c_36, c_538])).
% 2.96/1.49  tff(c_556, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_554])).
% 2.96/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.49  
% 2.96/1.49  Inference rules
% 2.96/1.49  ----------------------
% 2.96/1.49  #Ref     : 0
% 2.96/1.49  #Sup     : 107
% 2.96/1.49  #Fact    : 0
% 2.96/1.49  #Define  : 0
% 2.96/1.49  #Split   : 2
% 2.96/1.49  #Chain   : 0
% 2.96/1.49  #Close   : 0
% 2.96/1.49  
% 2.96/1.49  Ordering : KBO
% 2.96/1.49  
% 2.96/1.49  Simplification rules
% 2.96/1.49  ----------------------
% 2.96/1.49  #Subsume      : 4
% 2.96/1.49  #Demod        : 12
% 2.96/1.49  #Tautology    : 12
% 2.96/1.49  #SimpNegUnit  : 1
% 2.96/1.49  #BackRed      : 0
% 2.96/1.49  
% 2.96/1.49  #Partial instantiations: 0
% 2.96/1.49  #Strategies tried      : 1
% 2.96/1.49  
% 2.96/1.49  Timing (in seconds)
% 2.96/1.49  ----------------------
% 2.96/1.49  Preprocessing        : 0.29
% 2.96/1.49  Parsing              : 0.16
% 2.96/1.49  CNF conversion       : 0.02
% 2.96/1.49  Main loop            : 0.36
% 2.96/1.49  Inferencing          : 0.14
% 2.96/1.50  Reduction            : 0.08
% 2.96/1.50  Demodulation         : 0.06
% 2.96/1.50  BG Simplification    : 0.02
% 2.96/1.50  Subsumption          : 0.09
% 2.96/1.50  Abstraction          : 0.02
% 2.96/1.50  MUC search           : 0.00
% 2.96/1.50  Cooper               : 0.00
% 2.96/1.50  Total                : 0.68
% 2.96/1.50  Index Insertion      : 0.00
% 2.96/1.50  Index Deletion       : 0.00
% 2.96/1.50  Index Matching       : 0.00
% 2.96/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
