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
% DateTime   : Thu Dec  3 10:04:19 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 120 expanded)
%              Number of leaves         :   22 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :   89 ( 353 expanded)
%              Number of equality atoms :    8 (  39 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k8_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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
       => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
         => k1_funct_1(k8_relat_1(B,C),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( C = k8_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(E,A)
                  & r2_hidden(k4_tarski(D,E),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v1_relat_1(k8_relat_1(A,B))
        & v1_funct_1(k8_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_funct_1)).

tff(c_32,plain,(
    k1_funct_1(k8_relat_1('#skF_6','#skF_7'),'#skF_5') != k1_funct_1('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    ! [A_19,B_20] :
      ( v1_relat_1(k8_relat_1(A_19,B_20))
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_36,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_34,plain,(
    r2_hidden('#skF_5',k1_relat_1(k8_relat_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    ! [A_23,C_25] :
      ( r2_hidden(k4_tarski(A_23,k1_funct_1(C_25,A_23)),C_25)
      | ~ r2_hidden(A_23,k1_relat_1(C_25))
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_59,plain,(
    ! [D_42,E_43,B_44,A_45] :
      ( r2_hidden(k4_tarski(D_42,E_43),B_44)
      | ~ r2_hidden(k4_tarski(D_42,E_43),k8_relat_1(A_45,B_44))
      | ~ v1_relat_1(k8_relat_1(A_45,B_44))
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_123,plain,(
    ! [A_67,A_68,B_69] :
      ( r2_hidden(k4_tarski(A_67,k1_funct_1(k8_relat_1(A_68,B_69),A_67)),B_69)
      | ~ v1_relat_1(B_69)
      | ~ r2_hidden(A_67,k1_relat_1(k8_relat_1(A_68,B_69)))
      | ~ v1_funct_1(k8_relat_1(A_68,B_69))
      | ~ v1_relat_1(k8_relat_1(A_68,B_69)) ) ),
    inference(resolution,[status(thm)],[c_26,c_59])).

tff(c_30,plain,(
    ! [A_23,C_25,B_24] :
      ( r2_hidden(A_23,k1_relat_1(C_25))
      | ~ r2_hidden(k4_tarski(A_23,B_24),C_25)
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_148,plain,(
    ! [A_70,B_71,A_72] :
      ( r2_hidden(A_70,k1_relat_1(B_71))
      | ~ v1_funct_1(B_71)
      | ~ v1_relat_1(B_71)
      | ~ r2_hidden(A_70,k1_relat_1(k8_relat_1(A_72,B_71)))
      | ~ v1_funct_1(k8_relat_1(A_72,B_71))
      | ~ v1_relat_1(k8_relat_1(A_72,B_71)) ) ),
    inference(resolution,[status(thm)],[c_123,c_30])).

tff(c_175,plain,
    ( r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_funct_1(k8_relat_1('#skF_6','#skF_7'))
    | ~ v1_relat_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_34,c_148])).

tff(c_184,plain,
    ( r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ v1_funct_1(k8_relat_1('#skF_6','#skF_7'))
    | ~ v1_relat_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_175])).

tff(c_185,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_188,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_20,c_185])).

tff(c_192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_188])).

tff(c_194,plain,(
    v1_relat_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_22,plain,(
    ! [A_21,B_22] :
      ( v1_funct_1(k8_relat_1(A_21,B_22))
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_193,plain,
    ( ~ v1_funct_1(k8_relat_1('#skF_6','#skF_7'))
    | r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_195,plain,(
    ~ v1_funct_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_193])).

tff(c_198,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_22,c_195])).

tff(c_202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_198])).

tff(c_204,plain,(
    v1_funct_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_193])).

tff(c_28,plain,(
    ! [C_25,A_23,B_24] :
      ( k1_funct_1(C_25,A_23) = B_24
      | ~ r2_hidden(k4_tarski(A_23,B_24),C_25)
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_236,plain,(
    ! [A_79,B_80,A_81] :
      ( k1_funct_1(k8_relat_1(A_79,B_80),A_81) = k1_funct_1(B_80,A_81)
      | ~ v1_funct_1(B_80)
      | ~ v1_relat_1(B_80)
      | ~ r2_hidden(A_81,k1_relat_1(k8_relat_1(A_79,B_80)))
      | ~ v1_funct_1(k8_relat_1(A_79,B_80))
      | ~ v1_relat_1(k8_relat_1(A_79,B_80)) ) ),
    inference(resolution,[status(thm)],[c_123,c_28])).

tff(c_267,plain,
    ( k1_funct_1(k8_relat_1('#skF_6','#skF_7'),'#skF_5') = k1_funct_1('#skF_7','#skF_5')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_funct_1(k8_relat_1('#skF_6','#skF_7'))
    | ~ v1_relat_1(k8_relat_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_34,c_236])).

tff(c_277,plain,(
    k1_funct_1(k8_relat_1('#skF_6','#skF_7'),'#skF_5') = k1_funct_1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_204,c_38,c_36,c_267])).

tff(c_279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_277])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.37  
% 2.18/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.37  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k8_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.18/1.37  
% 2.18/1.37  %Foreground sorts:
% 2.18/1.37  
% 2.18/1.37  
% 2.18/1.37  %Background operators:
% 2.18/1.37  
% 2.18/1.37  
% 2.18/1.37  %Foreground operators:
% 2.18/1.37  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.18/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.18/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.18/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.18/1.37  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.18/1.37  tff('#skF_7', type, '#skF_7': $i).
% 2.18/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.18/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.18/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.18/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.18/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.18/1.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.18/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.18/1.37  
% 2.48/1.38  tff(f_70, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) => (k1_funct_1(k8_relat_1(B, C), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_funct_1)).
% 2.48/1.38  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => v1_relat_1(k8_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relat_1)).
% 2.48/1.38  tff(f_61, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 2.48/1.38  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k8_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(E, A) & r2_hidden(k4_tarski(D, E), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_relat_1)).
% 2.48/1.38  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v1_relat_1(k8_relat_1(A, B)) & v1_funct_1(k8_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_funct_1)).
% 2.48/1.38  tff(c_32, plain, (k1_funct_1(k8_relat_1('#skF_6', '#skF_7'), '#skF_5')!=k1_funct_1('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.48/1.38  tff(c_38, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.48/1.38  tff(c_20, plain, (![A_19, B_20]: (v1_relat_1(k8_relat_1(A_19, B_20)) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.48/1.38  tff(c_36, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.48/1.38  tff(c_34, plain, (r2_hidden('#skF_5', k1_relat_1(k8_relat_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.48/1.38  tff(c_26, plain, (![A_23, C_25]: (r2_hidden(k4_tarski(A_23, k1_funct_1(C_25, A_23)), C_25) | ~r2_hidden(A_23, k1_relat_1(C_25)) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.48/1.38  tff(c_59, plain, (![D_42, E_43, B_44, A_45]: (r2_hidden(k4_tarski(D_42, E_43), B_44) | ~r2_hidden(k4_tarski(D_42, E_43), k8_relat_1(A_45, B_44)) | ~v1_relat_1(k8_relat_1(A_45, B_44)) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.48/1.38  tff(c_123, plain, (![A_67, A_68, B_69]: (r2_hidden(k4_tarski(A_67, k1_funct_1(k8_relat_1(A_68, B_69), A_67)), B_69) | ~v1_relat_1(B_69) | ~r2_hidden(A_67, k1_relat_1(k8_relat_1(A_68, B_69))) | ~v1_funct_1(k8_relat_1(A_68, B_69)) | ~v1_relat_1(k8_relat_1(A_68, B_69)))), inference(resolution, [status(thm)], [c_26, c_59])).
% 2.48/1.38  tff(c_30, plain, (![A_23, C_25, B_24]: (r2_hidden(A_23, k1_relat_1(C_25)) | ~r2_hidden(k4_tarski(A_23, B_24), C_25) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.48/1.38  tff(c_148, plain, (![A_70, B_71, A_72]: (r2_hidden(A_70, k1_relat_1(B_71)) | ~v1_funct_1(B_71) | ~v1_relat_1(B_71) | ~r2_hidden(A_70, k1_relat_1(k8_relat_1(A_72, B_71))) | ~v1_funct_1(k8_relat_1(A_72, B_71)) | ~v1_relat_1(k8_relat_1(A_72, B_71)))), inference(resolution, [status(thm)], [c_123, c_30])).
% 2.48/1.38  tff(c_175, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_funct_1(k8_relat_1('#skF_6', '#skF_7')) | ~v1_relat_1(k8_relat_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_34, c_148])).
% 2.48/1.38  tff(c_184, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~v1_funct_1(k8_relat_1('#skF_6', '#skF_7')) | ~v1_relat_1(k8_relat_1('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_175])).
% 2.48/1.38  tff(c_185, plain, (~v1_relat_1(k8_relat_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_184])).
% 2.48/1.38  tff(c_188, plain, (~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_20, c_185])).
% 2.48/1.38  tff(c_192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_188])).
% 2.48/1.38  tff(c_194, plain, (v1_relat_1(k8_relat_1('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_184])).
% 2.48/1.38  tff(c_22, plain, (![A_21, B_22]: (v1_funct_1(k8_relat_1(A_21, B_22)) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.48/1.38  tff(c_193, plain, (~v1_funct_1(k8_relat_1('#skF_6', '#skF_7')) | r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_184])).
% 2.48/1.38  tff(c_195, plain, (~v1_funct_1(k8_relat_1('#skF_6', '#skF_7'))), inference(splitLeft, [status(thm)], [c_193])).
% 2.48/1.38  tff(c_198, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_22, c_195])).
% 2.48/1.38  tff(c_202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_198])).
% 2.48/1.38  tff(c_204, plain, (v1_funct_1(k8_relat_1('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_193])).
% 2.48/1.38  tff(c_28, plain, (![C_25, A_23, B_24]: (k1_funct_1(C_25, A_23)=B_24 | ~r2_hidden(k4_tarski(A_23, B_24), C_25) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.48/1.38  tff(c_236, plain, (![A_79, B_80, A_81]: (k1_funct_1(k8_relat_1(A_79, B_80), A_81)=k1_funct_1(B_80, A_81) | ~v1_funct_1(B_80) | ~v1_relat_1(B_80) | ~r2_hidden(A_81, k1_relat_1(k8_relat_1(A_79, B_80))) | ~v1_funct_1(k8_relat_1(A_79, B_80)) | ~v1_relat_1(k8_relat_1(A_79, B_80)))), inference(resolution, [status(thm)], [c_123, c_28])).
% 2.48/1.38  tff(c_267, plain, (k1_funct_1(k8_relat_1('#skF_6', '#skF_7'), '#skF_5')=k1_funct_1('#skF_7', '#skF_5') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_funct_1(k8_relat_1('#skF_6', '#skF_7')) | ~v1_relat_1(k8_relat_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_34, c_236])).
% 2.48/1.38  tff(c_277, plain, (k1_funct_1(k8_relat_1('#skF_6', '#skF_7'), '#skF_5')=k1_funct_1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_194, c_204, c_38, c_36, c_267])).
% 2.48/1.38  tff(c_279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_277])).
% 2.48/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.38  
% 2.48/1.38  Inference rules
% 2.48/1.38  ----------------------
% 2.48/1.38  #Ref     : 0
% 2.48/1.38  #Sup     : 48
% 2.48/1.38  #Fact    : 0
% 2.48/1.38  #Define  : 0
% 2.48/1.38  #Split   : 2
% 2.48/1.38  #Chain   : 0
% 2.48/1.38  #Close   : 0
% 2.48/1.38  
% 2.48/1.38  Ordering : KBO
% 2.48/1.38  
% 2.48/1.38  Simplification rules
% 2.48/1.38  ----------------------
% 2.48/1.38  #Subsume      : 2
% 2.48/1.38  #Demod        : 9
% 2.48/1.38  #Tautology    : 6
% 2.48/1.38  #SimpNegUnit  : 1
% 2.48/1.38  #BackRed      : 0
% 2.48/1.38  
% 2.48/1.38  #Partial instantiations: 0
% 2.48/1.38  #Strategies tried      : 1
% 2.48/1.38  
% 2.48/1.38  Timing (in seconds)
% 2.48/1.38  ----------------------
% 2.48/1.39  Preprocessing        : 0.29
% 2.48/1.39  Parsing              : 0.16
% 2.48/1.39  CNF conversion       : 0.02
% 2.48/1.39  Main loop            : 0.25
% 2.48/1.39  Inferencing          : 0.10
% 2.48/1.39  Reduction            : 0.06
% 2.48/1.39  Demodulation         : 0.04
% 2.48/1.39  BG Simplification    : 0.02
% 2.48/1.39  Subsumption          : 0.06
% 2.48/1.39  Abstraction          : 0.01
% 2.48/1.39  MUC search           : 0.00
% 2.48/1.39  Cooper               : 0.00
% 2.48/1.39  Total                : 0.58
% 2.48/1.39  Index Insertion      : 0.00
% 2.48/1.39  Index Deletion       : 0.00
% 2.48/1.39  Index Matching       : 0.00
% 2.48/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
