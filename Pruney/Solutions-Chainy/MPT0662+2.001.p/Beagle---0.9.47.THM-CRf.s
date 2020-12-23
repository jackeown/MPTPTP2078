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
% DateTime   : Thu Dec  3 10:04:10 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   51 (  63 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   91 ( 119 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

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

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_funct_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k6_relat_1(A)
      <=> ! [C,D] :
            ( r2_hidden(k4_tarski(C,D),B)
          <=> ( r2_hidden(C,A)
              & C = D ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_funct_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_46,plain,(
    r2_hidden('#skF_5',k1_relat_1(k7_relat_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_98,plain,(
    ! [A_37,B_38,C_39] :
      ( r2_hidden(A_37,B_38)
      | ~ r2_hidden(A_37,k1_relat_1(k7_relat_1(C_39,B_38)))
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_101,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_46,c_98])).

tff(c_104,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_101])).

tff(c_48,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_32,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34,plain,(
    ! [A_15] : v1_funct_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_14,plain,(
    ! [D_8,A_1] :
      ( r2_hidden(k4_tarski(D_8,D_8),k6_relat_1(A_1))
      | ~ r2_hidden(D_8,A_1)
      | ~ v1_relat_1(k6_relat_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_56,plain,(
    ! [D_8,A_1] :
      ( r2_hidden(k4_tarski(D_8,D_8),k6_relat_1(A_1))
      | ~ r2_hidden(D_8,A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_14])).

tff(c_119,plain,(
    ! [C_46,A_47,B_48] :
      ( k1_funct_1(C_46,A_47) = B_48
      | ~ r2_hidden(k4_tarski(A_47,B_48),C_46)
      | ~ v1_funct_1(C_46)
      | ~ v1_relat_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_122,plain,(
    ! [A_1,D_8] :
      ( k1_funct_1(k6_relat_1(A_1),D_8) = D_8
      | ~ v1_funct_1(k6_relat_1(A_1))
      | ~ v1_relat_1(k6_relat_1(A_1))
      | ~ r2_hidden(D_8,A_1) ) ),
    inference(resolution,[status(thm)],[c_56,c_119])).

tff(c_125,plain,(
    ! [A_1,D_8] :
      ( k1_funct_1(k6_relat_1(A_1),D_8) = D_8
      | ~ r2_hidden(D_8,A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_122])).

tff(c_30,plain,(
    ! [A_13,B_14] :
      ( k5_relat_1(k6_relat_1(A_13),B_14) = k7_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20,plain,(
    ! [A_9] : k1_relat_1(k6_relat_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_540,plain,(
    ! [B_82,C_83,A_84] :
      ( k1_funct_1(k5_relat_1(B_82,C_83),A_84) = k1_funct_1(C_83,k1_funct_1(B_82,A_84))
      | ~ r2_hidden(A_84,k1_relat_1(B_82))
      | ~ v1_funct_1(C_83)
      | ~ v1_relat_1(C_83)
      | ~ v1_funct_1(B_82)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_582,plain,(
    ! [A_9,C_83,A_84] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_9),C_83),A_84) = k1_funct_1(C_83,k1_funct_1(k6_relat_1(A_9),A_84))
      | ~ r2_hidden(A_84,A_9)
      | ~ v1_funct_1(C_83)
      | ~ v1_relat_1(C_83)
      | ~ v1_funct_1(k6_relat_1(A_9))
      | ~ v1_relat_1(k6_relat_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_540])).

tff(c_656,plain,(
    ! [A_88,C_89,A_90] :
      ( k1_funct_1(k5_relat_1(k6_relat_1(A_88),C_89),A_90) = k1_funct_1(C_89,k1_funct_1(k6_relat_1(A_88),A_90))
      | ~ r2_hidden(A_90,A_88)
      | ~ v1_funct_1(C_89)
      | ~ v1_relat_1(C_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_582])).

tff(c_687,plain,(
    ! [B_91,A_92,A_93] :
      ( k1_funct_1(B_91,k1_funct_1(k6_relat_1(A_92),A_93)) = k1_funct_1(k7_relat_1(B_91,A_92),A_93)
      | ~ r2_hidden(A_93,A_92)
      | ~ v1_funct_1(B_91)
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(B_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_656])).

tff(c_810,plain,(
    ! [B_100,A_101,D_102] :
      ( k1_funct_1(k7_relat_1(B_100,A_101),D_102) = k1_funct_1(B_100,D_102)
      | ~ r2_hidden(D_102,A_101)
      | ~ v1_funct_1(B_100)
      | ~ v1_relat_1(B_100)
      | ~ v1_relat_1(B_100)
      | ~ r2_hidden(D_102,A_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_687])).

tff(c_44,plain,(
    k1_funct_1(k7_relat_1('#skF_7','#skF_6'),'#skF_5') != k1_funct_1('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_835,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_810,c_44])).

tff(c_860,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_50,c_48,c_835])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:29:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.46  
% 3.02/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.46  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k5_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1 > #skF_4
% 3.02/1.46  
% 3.02/1.46  %Foreground sorts:
% 3.02/1.46  
% 3.02/1.46  
% 3.02/1.46  %Background operators:
% 3.02/1.46  
% 3.02/1.46  
% 3.02/1.46  %Foreground operators:
% 3.02/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.02/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.02/1.46  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.02/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.02/1.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.02/1.46  tff('#skF_7', type, '#skF_7': $i).
% 3.02/1.46  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.02/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.02/1.46  tff('#skF_5', type, '#skF_5': $i).
% 3.02/1.46  tff('#skF_6', type, '#skF_6': $i).
% 3.02/1.46  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.02/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.02/1.46  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.02/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.46  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.02/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.02/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.02/1.46  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.02/1.46  
% 3.17/1.47  tff(f_88, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_funct_1)).
% 3.17/1.47  tff(f_48, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 3.17/1.47  tff(f_56, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.17/1.47  tff(f_36, axiom, (![A, B]: (v1_relat_1(B) => ((B = k6_relat_1(A)) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), B) <=> (r2_hidden(C, A) & (C = D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_relat_1)).
% 3.17/1.47  tff(f_79, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 3.17/1.47  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.17/1.47  tff(f_40, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.17/1.47  tff(f_69, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_funct_1)).
% 3.17/1.47  tff(c_50, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.17/1.47  tff(c_46, plain, (r2_hidden('#skF_5', k1_relat_1(k7_relat_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.17/1.47  tff(c_98, plain, (![A_37, B_38, C_39]: (r2_hidden(A_37, B_38) | ~r2_hidden(A_37, k1_relat_1(k7_relat_1(C_39, B_38))) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.17/1.47  tff(c_101, plain, (r2_hidden('#skF_5', '#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_46, c_98])).
% 3.17/1.47  tff(c_104, plain, (r2_hidden('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_101])).
% 3.17/1.47  tff(c_48, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.17/1.47  tff(c_32, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.17/1.47  tff(c_34, plain, (![A_15]: (v1_funct_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.17/1.47  tff(c_14, plain, (![D_8, A_1]: (r2_hidden(k4_tarski(D_8, D_8), k6_relat_1(A_1)) | ~r2_hidden(D_8, A_1) | ~v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.17/1.47  tff(c_56, plain, (![D_8, A_1]: (r2_hidden(k4_tarski(D_8, D_8), k6_relat_1(A_1)) | ~r2_hidden(D_8, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_14])).
% 3.17/1.47  tff(c_119, plain, (![C_46, A_47, B_48]: (k1_funct_1(C_46, A_47)=B_48 | ~r2_hidden(k4_tarski(A_47, B_48), C_46) | ~v1_funct_1(C_46) | ~v1_relat_1(C_46))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.17/1.47  tff(c_122, plain, (![A_1, D_8]: (k1_funct_1(k6_relat_1(A_1), D_8)=D_8 | ~v1_funct_1(k6_relat_1(A_1)) | ~v1_relat_1(k6_relat_1(A_1)) | ~r2_hidden(D_8, A_1))), inference(resolution, [status(thm)], [c_56, c_119])).
% 3.17/1.47  tff(c_125, plain, (![A_1, D_8]: (k1_funct_1(k6_relat_1(A_1), D_8)=D_8 | ~r2_hidden(D_8, A_1))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_122])).
% 3.17/1.47  tff(c_30, plain, (![A_13, B_14]: (k5_relat_1(k6_relat_1(A_13), B_14)=k7_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.17/1.47  tff(c_20, plain, (![A_9]: (k1_relat_1(k6_relat_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.17/1.47  tff(c_540, plain, (![B_82, C_83, A_84]: (k1_funct_1(k5_relat_1(B_82, C_83), A_84)=k1_funct_1(C_83, k1_funct_1(B_82, A_84)) | ~r2_hidden(A_84, k1_relat_1(B_82)) | ~v1_funct_1(C_83) | ~v1_relat_1(C_83) | ~v1_funct_1(B_82) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.17/1.47  tff(c_582, plain, (![A_9, C_83, A_84]: (k1_funct_1(k5_relat_1(k6_relat_1(A_9), C_83), A_84)=k1_funct_1(C_83, k1_funct_1(k6_relat_1(A_9), A_84)) | ~r2_hidden(A_84, A_9) | ~v1_funct_1(C_83) | ~v1_relat_1(C_83) | ~v1_funct_1(k6_relat_1(A_9)) | ~v1_relat_1(k6_relat_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_540])).
% 3.17/1.47  tff(c_656, plain, (![A_88, C_89, A_90]: (k1_funct_1(k5_relat_1(k6_relat_1(A_88), C_89), A_90)=k1_funct_1(C_89, k1_funct_1(k6_relat_1(A_88), A_90)) | ~r2_hidden(A_90, A_88) | ~v1_funct_1(C_89) | ~v1_relat_1(C_89))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_582])).
% 3.17/1.47  tff(c_687, plain, (![B_91, A_92, A_93]: (k1_funct_1(B_91, k1_funct_1(k6_relat_1(A_92), A_93))=k1_funct_1(k7_relat_1(B_91, A_92), A_93) | ~r2_hidden(A_93, A_92) | ~v1_funct_1(B_91) | ~v1_relat_1(B_91) | ~v1_relat_1(B_91))), inference(superposition, [status(thm), theory('equality')], [c_30, c_656])).
% 3.17/1.47  tff(c_810, plain, (![B_100, A_101, D_102]: (k1_funct_1(k7_relat_1(B_100, A_101), D_102)=k1_funct_1(B_100, D_102) | ~r2_hidden(D_102, A_101) | ~v1_funct_1(B_100) | ~v1_relat_1(B_100) | ~v1_relat_1(B_100) | ~r2_hidden(D_102, A_101))), inference(superposition, [status(thm), theory('equality')], [c_125, c_687])).
% 3.17/1.47  tff(c_44, plain, (k1_funct_1(k7_relat_1('#skF_7', '#skF_6'), '#skF_5')!=k1_funct_1('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.17/1.47  tff(c_835, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_810, c_44])).
% 3.17/1.47  tff(c_860, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_50, c_48, c_835])).
% 3.17/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.47  
% 3.17/1.47  Inference rules
% 3.17/1.47  ----------------------
% 3.17/1.47  #Ref     : 0
% 3.17/1.47  #Sup     : 164
% 3.17/1.47  #Fact    : 0
% 3.17/1.47  #Define  : 0
% 3.17/1.47  #Split   : 1
% 3.17/1.47  #Chain   : 0
% 3.17/1.47  #Close   : 0
% 3.17/1.47  
% 3.17/1.47  Ordering : KBO
% 3.17/1.47  
% 3.17/1.47  Simplification rules
% 3.17/1.47  ----------------------
% 3.17/1.47  #Subsume      : 12
% 3.17/1.47  #Demod        : 89
% 3.17/1.47  #Tautology    : 37
% 3.17/1.47  #SimpNegUnit  : 0
% 3.17/1.47  #BackRed      : 0
% 3.17/1.47  
% 3.17/1.47  #Partial instantiations: 0
% 3.17/1.47  #Strategies tried      : 1
% 3.17/1.47  
% 3.17/1.47  Timing (in seconds)
% 3.17/1.47  ----------------------
% 3.17/1.48  Preprocessing        : 0.31
% 3.17/1.48  Parsing              : 0.16
% 3.17/1.48  CNF conversion       : 0.02
% 3.17/1.48  Main loop            : 0.40
% 3.17/1.48  Inferencing          : 0.15
% 3.17/1.48  Reduction            : 0.11
% 3.17/1.48  Demodulation         : 0.08
% 3.17/1.48  BG Simplification    : 0.03
% 3.17/1.48  Subsumption          : 0.08
% 3.17/1.48  Abstraction          : 0.03
% 3.17/1.48  MUC search           : 0.00
% 3.17/1.48  Cooper               : 0.00
% 3.17/1.48  Total                : 0.74
% 3.17/1.48  Index Insertion      : 0.00
% 3.17/1.48  Index Deletion       : 0.00
% 3.17/1.48  Index Matching       : 0.00
% 3.17/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
