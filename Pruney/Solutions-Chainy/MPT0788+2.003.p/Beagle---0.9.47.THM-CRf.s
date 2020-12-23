%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:47 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 117 expanded)
%              Number of leaves         :   26 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :  114 ( 347 expanded)
%              Number of equality atoms :   11 (  47 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(v1_relat_2,type,(
    v1_relat_2: $i > $o )).

tff(v8_relat_2,type,(
    v8_relat_2: $i > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(v6_relat_2,type,(
    v6_relat_2: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v4_relat_2,type,(
    v4_relat_2: $i > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_wellord1,type,(
    v1_wellord1: $i > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( ( v2_wellord1(C)
            & r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C)) )
         => ( r1_tarski(k1_wellord1(C,A),k1_wellord1(C,B))
          <=> ( A = B
              | r2_hidden(A,k1_wellord1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_wellord1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v1_relat_2(A)
      <=> ! [B] :
            ( r2_hidden(B,k3_relat_1(A))
           => r2_hidden(k4_tarski(B,B),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_wellord1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( v2_wellord1(C)
          & r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) )
       => ( r2_hidden(k4_tarski(A,B),C)
        <=> r1_tarski(k1_wellord1(C,A),k1_wellord1(C,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

tff(c_48,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_46,plain,(
    v2_wellord1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_72,plain,(
    ! [A_25] :
      ( v1_relat_2(A_25)
      | ~ v2_wellord1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_75,plain,
    ( v1_relat_2('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_72])).

tff(c_78,plain,(
    v1_relat_2('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_75])).

tff(c_44,plain,(
    r2_hidden('#skF_4',k3_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_32,plain,(
    ! [B_17,A_14] :
      ( r2_hidden(k4_tarski(B_17,B_17),A_14)
      | ~ r2_hidden(B_17,k3_relat_1(A_14))
      | ~ v1_relat_2(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_163,plain,(
    ! [C_56,A_57,B_58] :
      ( r1_tarski(k1_wellord1(C_56,A_57),k1_wellord1(C_56,B_58))
      | ~ r2_hidden(k4_tarski(A_57,B_58),C_56)
      | ~ r2_hidden(B_58,k3_relat_1(C_56))
      | ~ r2_hidden(A_57,k3_relat_1(C_56))
      | ~ v2_wellord1(C_56)
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_52,plain,
    ( '#skF_5' != '#skF_4'
    | ~ r1_tarski(k1_wellord1('#skF_6','#skF_4'),k1_wellord1('#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_71,plain,(
    ~ r1_tarski(k1_wellord1('#skF_6','#skF_4'),k1_wellord1('#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_60,plain,
    ( r1_tarski(k1_wellord1('#skF_6','#skF_4'),k1_wellord1('#skF_6','#skF_5'))
    | r2_hidden('#skF_4',k1_wellord1('#skF_6','#skF_5'))
    | '#skF_5' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_104,plain,
    ( r2_hidden('#skF_4',k1_wellord1('#skF_6','#skF_5'))
    | '#skF_5' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_60])).

tff(c_105,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_106,plain,(
    ~ r1_tarski(k1_wellord1('#skF_6','#skF_4'),k1_wellord1('#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_71])).

tff(c_166,plain,
    ( ~ r2_hidden(k4_tarski('#skF_4','#skF_4'),'#skF_6')
    | ~ r2_hidden('#skF_4',k3_relat_1('#skF_6'))
    | ~ v2_wellord1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_163,c_106])).

tff(c_169,plain,(
    ~ r2_hidden(k4_tarski('#skF_4','#skF_4'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_166])).

tff(c_172,plain,
    ( ~ r2_hidden('#skF_4',k3_relat_1('#skF_6'))
    | ~ v1_relat_2('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_32,c_169])).

tff(c_179,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_78,c_44,c_172])).

tff(c_180,plain,(
    r2_hidden('#skF_4',k1_wellord1('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_4,plain,(
    ! [D_12,B_8,A_1] :
      ( r2_hidden(k4_tarski(D_12,B_8),A_1)
      | ~ r2_hidden(D_12,k1_wellord1(A_1,B_8))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_42,plain,(
    r2_hidden('#skF_5',k3_relat_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_226,plain,(
    ! [C_77,A_78,B_79] :
      ( r1_tarski(k1_wellord1(C_77,A_78),k1_wellord1(C_77,B_79))
      | ~ r2_hidden(k4_tarski(A_78,B_79),C_77)
      | ~ r2_hidden(B_79,k3_relat_1(C_77))
      | ~ r2_hidden(A_78,k3_relat_1(C_77))
      | ~ v2_wellord1(C_77)
      | ~ v1_relat_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_229,plain,
    ( ~ r2_hidden(k4_tarski('#skF_4','#skF_5'),'#skF_6')
    | ~ r2_hidden('#skF_5',k3_relat_1('#skF_6'))
    | ~ r2_hidden('#skF_4',k3_relat_1('#skF_6'))
    | ~ v2_wellord1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_226,c_71])).

tff(c_232,plain,(
    ~ r2_hidden(k4_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_229])).

tff(c_235,plain,
    ( ~ r2_hidden('#skF_4',k1_wellord1('#skF_6','#skF_5'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_232])).

tff(c_239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_180,c_235])).

tff(c_240,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_241,plain,(
    r1_tarski(k1_wellord1('#skF_6','#skF_4'),k1_wellord1('#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_50,plain,
    ( ~ r2_hidden('#skF_4',k1_wellord1('#skF_6','#skF_5'))
    | ~ r1_tarski(k1_wellord1('#skF_6','#skF_4'),k1_wellord1('#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_252,plain,(
    ~ r2_hidden('#skF_4',k1_wellord1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_50])).

tff(c_322,plain,(
    ! [A_108,B_109,C_110] :
      ( r2_hidden(k4_tarski(A_108,B_109),C_110)
      | ~ r1_tarski(k1_wellord1(C_110,A_108),k1_wellord1(C_110,B_109))
      | ~ r2_hidden(B_109,k3_relat_1(C_110))
      | ~ r2_hidden(A_108,k3_relat_1(C_110))
      | ~ v2_wellord1(C_110)
      | ~ v1_relat_1(C_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_325,plain,
    ( r2_hidden(k4_tarski('#skF_4','#skF_5'),'#skF_6')
    | ~ r2_hidden('#skF_5',k3_relat_1('#skF_6'))
    | ~ r2_hidden('#skF_4',k3_relat_1('#skF_6'))
    | ~ v2_wellord1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_241,c_322])).

tff(c_328,plain,(
    r2_hidden(k4_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_325])).

tff(c_2,plain,(
    ! [D_12,A_1,B_8] :
      ( r2_hidden(D_12,k1_wellord1(A_1,B_8))
      | ~ r2_hidden(k4_tarski(D_12,B_8),A_1)
      | D_12 = B_8
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_331,plain,
    ( r2_hidden('#skF_4',k1_wellord1('#skF_6','#skF_5'))
    | '#skF_5' = '#skF_4'
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_328,c_2])).

tff(c_334,plain,
    ( r2_hidden('#skF_4',k1_wellord1('#skF_6','#skF_5'))
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_331])).

tff(c_336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_240,c_252,c_334])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.35  
% 2.44/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.35  %$ r2_hidden > r1_tarski > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.44/1.35  
% 2.44/1.35  %Foreground sorts:
% 2.44/1.35  
% 2.44/1.35  
% 2.44/1.35  %Background operators:
% 2.44/1.35  
% 2.44/1.35  
% 2.44/1.35  %Foreground operators:
% 2.44/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.44/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.44/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.44/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.44/1.35  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 2.44/1.35  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 2.44/1.35  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.44/1.35  tff(v6_relat_2, type, v6_relat_2: $i > $o).
% 2.44/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.44/1.35  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 2.44/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.44/1.35  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 2.44/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.44/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.44/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.44/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.44/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.44/1.35  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.44/1.35  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 2.44/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.44/1.35  tff(v1_wellord1, type, v1_wellord1: $i > $o).
% 2.44/1.35  
% 2.44/1.37  tff(f_88, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) => (r1_tarski(k1_wellord1(C, A), k1_wellord1(C, B)) <=> ((A = B) | r2_hidden(A, k1_wellord1(C, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_wellord1)).
% 2.44/1.37  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) <=> ((((v1_relat_2(A) & v8_relat_2(A)) & v4_relat_2(A)) & v6_relat_2(A)) & v1_wellord1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_wellord1)).
% 2.44/1.37  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (v1_relat_2(A) <=> (![B]: (r2_hidden(B, k3_relat_1(A)) => r2_hidden(k4_tarski(B, B), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_wellord1)).
% 2.44/1.37  tff(f_73, axiom, (![A, B, C]: (v1_relat_1(C) => (((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) => (r2_hidden(k4_tarski(A, B), C) <=> r1_tarski(k1_wellord1(C, A), k1_wellord1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_wellord1)).
% 2.44/1.37  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 2.44/1.37  tff(c_48, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.44/1.37  tff(c_46, plain, (v2_wellord1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.44/1.37  tff(c_72, plain, (![A_25]: (v1_relat_2(A_25) | ~v2_wellord1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.44/1.37  tff(c_75, plain, (v1_relat_2('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_46, c_72])).
% 2.44/1.37  tff(c_78, plain, (v1_relat_2('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_75])).
% 2.44/1.37  tff(c_44, plain, (r2_hidden('#skF_4', k3_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.44/1.37  tff(c_32, plain, (![B_17, A_14]: (r2_hidden(k4_tarski(B_17, B_17), A_14) | ~r2_hidden(B_17, k3_relat_1(A_14)) | ~v1_relat_2(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.44/1.37  tff(c_163, plain, (![C_56, A_57, B_58]: (r1_tarski(k1_wellord1(C_56, A_57), k1_wellord1(C_56, B_58)) | ~r2_hidden(k4_tarski(A_57, B_58), C_56) | ~r2_hidden(B_58, k3_relat_1(C_56)) | ~r2_hidden(A_57, k3_relat_1(C_56)) | ~v2_wellord1(C_56) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.44/1.37  tff(c_52, plain, ('#skF_5'!='#skF_4' | ~r1_tarski(k1_wellord1('#skF_6', '#skF_4'), k1_wellord1('#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.44/1.37  tff(c_71, plain, (~r1_tarski(k1_wellord1('#skF_6', '#skF_4'), k1_wellord1('#skF_6', '#skF_5'))), inference(splitLeft, [status(thm)], [c_52])).
% 2.44/1.37  tff(c_60, plain, (r1_tarski(k1_wellord1('#skF_6', '#skF_4'), k1_wellord1('#skF_6', '#skF_5')) | r2_hidden('#skF_4', k1_wellord1('#skF_6', '#skF_5')) | '#skF_5'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.44/1.37  tff(c_104, plain, (r2_hidden('#skF_4', k1_wellord1('#skF_6', '#skF_5')) | '#skF_5'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_71, c_60])).
% 2.44/1.37  tff(c_105, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_104])).
% 2.44/1.37  tff(c_106, plain, (~r1_tarski(k1_wellord1('#skF_6', '#skF_4'), k1_wellord1('#skF_6', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_105, c_71])).
% 2.44/1.37  tff(c_166, plain, (~r2_hidden(k4_tarski('#skF_4', '#skF_4'), '#skF_6') | ~r2_hidden('#skF_4', k3_relat_1('#skF_6')) | ~v2_wellord1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_163, c_106])).
% 2.44/1.37  tff(c_169, plain, (~r2_hidden(k4_tarski('#skF_4', '#skF_4'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_166])).
% 2.44/1.37  tff(c_172, plain, (~r2_hidden('#skF_4', k3_relat_1('#skF_6')) | ~v1_relat_2('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_32, c_169])).
% 2.44/1.37  tff(c_179, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_78, c_44, c_172])).
% 2.44/1.37  tff(c_180, plain, (r2_hidden('#skF_4', k1_wellord1('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_104])).
% 2.44/1.37  tff(c_4, plain, (![D_12, B_8, A_1]: (r2_hidden(k4_tarski(D_12, B_8), A_1) | ~r2_hidden(D_12, k1_wellord1(A_1, B_8)) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.44/1.37  tff(c_42, plain, (r2_hidden('#skF_5', k3_relat_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.44/1.37  tff(c_226, plain, (![C_77, A_78, B_79]: (r1_tarski(k1_wellord1(C_77, A_78), k1_wellord1(C_77, B_79)) | ~r2_hidden(k4_tarski(A_78, B_79), C_77) | ~r2_hidden(B_79, k3_relat_1(C_77)) | ~r2_hidden(A_78, k3_relat_1(C_77)) | ~v2_wellord1(C_77) | ~v1_relat_1(C_77))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.44/1.37  tff(c_229, plain, (~r2_hidden(k4_tarski('#skF_4', '#skF_5'), '#skF_6') | ~r2_hidden('#skF_5', k3_relat_1('#skF_6')) | ~r2_hidden('#skF_4', k3_relat_1('#skF_6')) | ~v2_wellord1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_226, c_71])).
% 2.44/1.37  tff(c_232, plain, (~r2_hidden(k4_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_229])).
% 2.44/1.37  tff(c_235, plain, (~r2_hidden('#skF_4', k1_wellord1('#skF_6', '#skF_5')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_4, c_232])).
% 2.44/1.37  tff(c_239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_180, c_235])).
% 2.44/1.37  tff(c_240, plain, ('#skF_5'!='#skF_4'), inference(splitRight, [status(thm)], [c_52])).
% 2.44/1.37  tff(c_241, plain, (r1_tarski(k1_wellord1('#skF_6', '#skF_4'), k1_wellord1('#skF_6', '#skF_5'))), inference(splitRight, [status(thm)], [c_52])).
% 2.44/1.37  tff(c_50, plain, (~r2_hidden('#skF_4', k1_wellord1('#skF_6', '#skF_5')) | ~r1_tarski(k1_wellord1('#skF_6', '#skF_4'), k1_wellord1('#skF_6', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.44/1.37  tff(c_252, plain, (~r2_hidden('#skF_4', k1_wellord1('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_241, c_50])).
% 2.44/1.37  tff(c_322, plain, (![A_108, B_109, C_110]: (r2_hidden(k4_tarski(A_108, B_109), C_110) | ~r1_tarski(k1_wellord1(C_110, A_108), k1_wellord1(C_110, B_109)) | ~r2_hidden(B_109, k3_relat_1(C_110)) | ~r2_hidden(A_108, k3_relat_1(C_110)) | ~v2_wellord1(C_110) | ~v1_relat_1(C_110))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.44/1.37  tff(c_325, plain, (r2_hidden(k4_tarski('#skF_4', '#skF_5'), '#skF_6') | ~r2_hidden('#skF_5', k3_relat_1('#skF_6')) | ~r2_hidden('#skF_4', k3_relat_1('#skF_6')) | ~v2_wellord1('#skF_6') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_241, c_322])).
% 2.44/1.37  tff(c_328, plain, (r2_hidden(k4_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_325])).
% 2.44/1.37  tff(c_2, plain, (![D_12, A_1, B_8]: (r2_hidden(D_12, k1_wellord1(A_1, B_8)) | ~r2_hidden(k4_tarski(D_12, B_8), A_1) | D_12=B_8 | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.44/1.37  tff(c_331, plain, (r2_hidden('#skF_4', k1_wellord1('#skF_6', '#skF_5')) | '#skF_5'='#skF_4' | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_328, c_2])).
% 2.44/1.37  tff(c_334, plain, (r2_hidden('#skF_4', k1_wellord1('#skF_6', '#skF_5')) | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_331])).
% 2.44/1.37  tff(c_336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_240, c_252, c_334])).
% 2.44/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.44/1.37  
% 2.44/1.37  Inference rules
% 2.44/1.37  ----------------------
% 2.44/1.37  #Ref     : 0
% 2.44/1.37  #Sup     : 45
% 2.44/1.37  #Fact    : 0
% 2.44/1.37  #Define  : 0
% 2.44/1.37  #Split   : 2
% 2.44/1.37  #Chain   : 0
% 2.44/1.37  #Close   : 0
% 2.44/1.37  
% 2.44/1.37  Ordering : KBO
% 2.44/1.37  
% 2.44/1.37  Simplification rules
% 2.44/1.37  ----------------------
% 2.44/1.37  #Subsume      : 3
% 2.44/1.37  #Demod        : 25
% 2.44/1.37  #Tautology    : 18
% 2.44/1.37  #SimpNegUnit  : 3
% 2.44/1.37  #BackRed      : 2
% 2.44/1.37  
% 2.44/1.37  #Partial instantiations: 0
% 2.44/1.37  #Strategies tried      : 1
% 2.44/1.37  
% 2.44/1.37  Timing (in seconds)
% 2.44/1.37  ----------------------
% 2.44/1.37  Preprocessing        : 0.32
% 2.44/1.37  Parsing              : 0.16
% 2.44/1.37  CNF conversion       : 0.03
% 2.44/1.37  Main loop            : 0.28
% 2.44/1.37  Inferencing          : 0.11
% 2.44/1.37  Reduction            : 0.07
% 2.44/1.37  Demodulation         : 0.05
% 2.44/1.37  BG Simplification    : 0.02
% 2.44/1.37  Subsumption          : 0.06
% 2.44/1.37  Abstraction          : 0.01
% 2.44/1.37  MUC search           : 0.00
% 2.44/1.37  Cooper               : 0.00
% 2.44/1.37  Total                : 0.63
% 2.44/1.37  Index Insertion      : 0.00
% 2.44/1.37  Index Deletion       : 0.00
% 2.44/1.37  Index Matching       : 0.00
% 2.44/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
