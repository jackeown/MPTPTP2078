%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:18 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.27s
% Verified   : 
% Statistics : Number of formulae       :   45 (  66 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   89 ( 174 expanded)
%              Number of equality atoms :    5 (  17 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ( k1_relat_1(k5_relat_1(B,A)) = k1_relat_1(B)
             => r1_tarski(k2_relat_1(B),k1_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(k5_relat_1(C,B)))
          <=> ( r2_hidden(A,k1_relat_1(C))
              & r2_hidden(k1_funct_1(C,A),k1_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_1)).

tff(c_32,plain,(
    ~ r1_tarski(k2_relat_1('#skF_7'),k1_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_48,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_1'(A_53,B_54),A_53)
      | r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_53,plain,(
    ! [A_53] : r1_tarski(A_53,A_53) ),
    inference(resolution,[status(thm)],[c_48,c_4])).

tff(c_76,plain,(
    ! [A_68,C_69] :
      ( r2_hidden('#skF_5'(A_68,k2_relat_1(A_68),C_69),k1_relat_1(A_68))
      | ~ r2_hidden(C_69,k2_relat_1(A_68))
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_82,plain,(
    ! [A_68,C_69,B_2] :
      ( r2_hidden('#skF_5'(A_68,k2_relat_1(A_68),C_69),B_2)
      | ~ r1_tarski(k1_relat_1(A_68),B_2)
      | ~ r2_hidden(C_69,k2_relat_1(A_68))
      | ~ v1_funct_1(A_68)
      | ~ v1_relat_1(A_68) ) ),
    inference(resolution,[status(thm)],[c_76,c_2])).

tff(c_42,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34,plain,(
    k1_relat_1(k5_relat_1('#skF_7','#skF_6')) = k1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_10,plain,(
    ! [A_6,C_42] :
      ( k1_funct_1(A_6,'#skF_5'(A_6,k2_relat_1(A_6),C_42)) = C_42
      | ~ r2_hidden(C_42,k2_relat_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_182,plain,(
    ! [C_87,A_88,B_89] :
      ( r2_hidden(k1_funct_1(C_87,A_88),k1_relat_1(B_89))
      | ~ r2_hidden(A_88,k1_relat_1(k5_relat_1(C_87,B_89)))
      | ~ v1_funct_1(C_87)
      | ~ v1_relat_1(C_87)
      | ~ v1_funct_1(B_89)
      | ~ v1_relat_1(B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_604,plain,(
    ! [C_178,B_179,A_180] :
      ( r2_hidden(C_178,k1_relat_1(B_179))
      | ~ r2_hidden('#skF_5'(A_180,k2_relat_1(A_180),C_178),k1_relat_1(k5_relat_1(A_180,B_179)))
      | ~ v1_funct_1(A_180)
      | ~ v1_relat_1(A_180)
      | ~ v1_funct_1(B_179)
      | ~ v1_relat_1(B_179)
      | ~ r2_hidden(C_178,k2_relat_1(A_180))
      | ~ v1_funct_1(A_180)
      | ~ v1_relat_1(A_180) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_182])).

tff(c_615,plain,(
    ! [C_178] :
      ( r2_hidden(C_178,k1_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_5'('#skF_7',k2_relat_1('#skF_7'),C_178),k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6')
      | ~ r2_hidden(C_178,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_604])).

tff(c_620,plain,(
    ! [C_181] :
      ( r2_hidden(C_181,k1_relat_1('#skF_6'))
      | ~ r2_hidden('#skF_5'('#skF_7',k2_relat_1('#skF_7'),C_181),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_181,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_42,c_40,c_38,c_36,c_615])).

tff(c_624,plain,(
    ! [C_69] :
      ( r2_hidden(C_69,k1_relat_1('#skF_6'))
      | ~ r1_tarski(k1_relat_1('#skF_7'),k1_relat_1('#skF_7'))
      | ~ r2_hidden(C_69,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_82,c_620])).

tff(c_635,plain,(
    ! [C_182] :
      ( r2_hidden(C_182,k1_relat_1('#skF_6'))
      | ~ r2_hidden(C_182,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_53,c_624])).

tff(c_745,plain,(
    ! [B_183] :
      ( r2_hidden('#skF_1'(k2_relat_1('#skF_7'),B_183),k1_relat_1('#skF_6'))
      | r1_tarski(k2_relat_1('#skF_7'),B_183) ) ),
    inference(resolution,[status(thm)],[c_6,c_635])).

tff(c_751,plain,(
    r1_tarski(k2_relat_1('#skF_7'),k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_745,c_4])).

tff(c_756,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_751])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:20:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.54  
% 3.27/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.55  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k5_relat_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 3.27/1.55  
% 3.27/1.55  %Foreground sorts:
% 3.27/1.55  
% 3.27/1.55  
% 3.27/1.55  %Background operators:
% 3.27/1.55  
% 3.27/1.55  
% 3.27/1.55  %Foreground operators:
% 3.27/1.55  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.27/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.27/1.55  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.27/1.55  tff('#skF_7', type, '#skF_7': $i).
% 3.27/1.55  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.27/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.27/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.27/1.55  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.27/1.55  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.27/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.27/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.27/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.27/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.27/1.55  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.27/1.55  
% 3.27/1.56  tff(f_76, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(k5_relat_1(B, A)) = k1_relat_1(B)) => r1_tarski(k2_relat_1(B), k1_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_funct_1)).
% 3.27/1.56  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.27/1.56  tff(f_47, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 3.27/1.56  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k5_relat_1(C, B))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), k1_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_1)).
% 3.27/1.56  tff(c_32, plain, (~r1_tarski(k2_relat_1('#skF_7'), k1_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.27/1.56  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.27/1.56  tff(c_38, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.27/1.56  tff(c_36, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.27/1.56  tff(c_48, plain, (![A_53, B_54]: (r2_hidden('#skF_1'(A_53, B_54), A_53) | r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.27/1.56  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.27/1.56  tff(c_53, plain, (![A_53]: (r1_tarski(A_53, A_53))), inference(resolution, [status(thm)], [c_48, c_4])).
% 3.27/1.56  tff(c_76, plain, (![A_68, C_69]: (r2_hidden('#skF_5'(A_68, k2_relat_1(A_68), C_69), k1_relat_1(A_68)) | ~r2_hidden(C_69, k2_relat_1(A_68)) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.27/1.56  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.27/1.56  tff(c_82, plain, (![A_68, C_69, B_2]: (r2_hidden('#skF_5'(A_68, k2_relat_1(A_68), C_69), B_2) | ~r1_tarski(k1_relat_1(A_68), B_2) | ~r2_hidden(C_69, k2_relat_1(A_68)) | ~v1_funct_1(A_68) | ~v1_relat_1(A_68))), inference(resolution, [status(thm)], [c_76, c_2])).
% 3.27/1.56  tff(c_42, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.27/1.56  tff(c_40, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.27/1.56  tff(c_34, plain, (k1_relat_1(k5_relat_1('#skF_7', '#skF_6'))=k1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.27/1.56  tff(c_10, plain, (![A_6, C_42]: (k1_funct_1(A_6, '#skF_5'(A_6, k2_relat_1(A_6), C_42))=C_42 | ~r2_hidden(C_42, k2_relat_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.27/1.56  tff(c_182, plain, (![C_87, A_88, B_89]: (r2_hidden(k1_funct_1(C_87, A_88), k1_relat_1(B_89)) | ~r2_hidden(A_88, k1_relat_1(k5_relat_1(C_87, B_89))) | ~v1_funct_1(C_87) | ~v1_relat_1(C_87) | ~v1_funct_1(B_89) | ~v1_relat_1(B_89))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.27/1.56  tff(c_604, plain, (![C_178, B_179, A_180]: (r2_hidden(C_178, k1_relat_1(B_179)) | ~r2_hidden('#skF_5'(A_180, k2_relat_1(A_180), C_178), k1_relat_1(k5_relat_1(A_180, B_179))) | ~v1_funct_1(A_180) | ~v1_relat_1(A_180) | ~v1_funct_1(B_179) | ~v1_relat_1(B_179) | ~r2_hidden(C_178, k2_relat_1(A_180)) | ~v1_funct_1(A_180) | ~v1_relat_1(A_180))), inference(superposition, [status(thm), theory('equality')], [c_10, c_182])).
% 3.27/1.56  tff(c_615, plain, (![C_178]: (r2_hidden(C_178, k1_relat_1('#skF_6')) | ~r2_hidden('#skF_5'('#skF_7', k2_relat_1('#skF_7'), C_178), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~r2_hidden(C_178, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_604])).
% 3.27/1.56  tff(c_620, plain, (![C_181]: (r2_hidden(C_181, k1_relat_1('#skF_6')) | ~r2_hidden('#skF_5'('#skF_7', k2_relat_1('#skF_7'), C_181), k1_relat_1('#skF_7')) | ~r2_hidden(C_181, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_42, c_40, c_38, c_36, c_615])).
% 3.27/1.56  tff(c_624, plain, (![C_69]: (r2_hidden(C_69, k1_relat_1('#skF_6')) | ~r1_tarski(k1_relat_1('#skF_7'), k1_relat_1('#skF_7')) | ~r2_hidden(C_69, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_82, c_620])).
% 3.27/1.56  tff(c_635, plain, (![C_182]: (r2_hidden(C_182, k1_relat_1('#skF_6')) | ~r2_hidden(C_182, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_53, c_624])).
% 3.27/1.56  tff(c_745, plain, (![B_183]: (r2_hidden('#skF_1'(k2_relat_1('#skF_7'), B_183), k1_relat_1('#skF_6')) | r1_tarski(k2_relat_1('#skF_7'), B_183))), inference(resolution, [status(thm)], [c_6, c_635])).
% 3.27/1.56  tff(c_751, plain, (r1_tarski(k2_relat_1('#skF_7'), k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_745, c_4])).
% 3.27/1.56  tff(c_756, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_751])).
% 3.27/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.56  
% 3.27/1.56  Inference rules
% 3.27/1.56  ----------------------
% 3.27/1.56  #Ref     : 0
% 3.27/1.56  #Sup     : 165
% 3.27/1.56  #Fact    : 0
% 3.27/1.56  #Define  : 0
% 3.27/1.56  #Split   : 1
% 3.27/1.56  #Chain   : 0
% 3.27/1.56  #Close   : 0
% 3.27/1.56  
% 3.27/1.56  Ordering : KBO
% 3.27/1.56  
% 3.27/1.56  Simplification rules
% 3.27/1.56  ----------------------
% 3.27/1.56  #Subsume      : 31
% 3.27/1.56  #Demod        : 41
% 3.27/1.56  #Tautology    : 20
% 3.27/1.56  #SimpNegUnit  : 1
% 3.27/1.56  #BackRed      : 0
% 3.27/1.56  
% 3.27/1.56  #Partial instantiations: 0
% 3.27/1.56  #Strategies tried      : 1
% 3.27/1.56  
% 3.27/1.56  Timing (in seconds)
% 3.27/1.56  ----------------------
% 3.27/1.56  Preprocessing        : 0.32
% 3.27/1.56  Parsing              : 0.17
% 3.27/1.56  CNF conversion       : 0.03
% 3.27/1.56  Main loop            : 0.44
% 3.27/1.56  Inferencing          : 0.17
% 3.27/1.56  Reduction            : 0.10
% 3.27/1.56  Demodulation         : 0.07
% 3.27/1.56  BG Simplification    : 0.03
% 3.27/1.56  Subsumption          : 0.12
% 3.27/1.56  Abstraction          : 0.02
% 3.27/1.56  MUC search           : 0.00
% 3.27/1.56  Cooper               : 0.00
% 3.27/1.56  Total                : 0.79
% 3.27/1.56  Index Insertion      : 0.00
% 3.27/1.56  Index Deletion       : 0.00
% 3.27/1.56  Index Matching       : 0.00
% 3.27/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
