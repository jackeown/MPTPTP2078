%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:10 EST 2020

% Result     : Theorem 4.32s
% Output     : CNFRefutation 4.32s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 113 expanded)
%              Number of leaves         :   24 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 307 expanded)
%              Number of equality atoms :   14 (  53 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
         => k1_funct_1(k7_relat_1(C,B),A) = k1_funct_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_funct_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( ( r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> r2_hidden(k4_tarski(B,C),A) ) )
          & ( ~ r2_hidden(B,k1_relat_1(A))
           => ( C = k1_funct_1(A,B)
            <=> C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

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

tff(c_40,plain,(
    k1_funct_1(k7_relat_1('#skF_7','#skF_6'),'#skF_5') != k1_funct_1('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_46,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_44,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_42,plain,(
    r2_hidden('#skF_5',k1_relat_1(k7_relat_1('#skF_7','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_62,plain,(
    ! [A_41,C_42,B_43] :
      ( r2_hidden(A_41,k1_relat_1(C_42))
      | ~ r2_hidden(A_41,k1_relat_1(k7_relat_1(C_42,B_43)))
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_69,plain,
    ( r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_62])).

tff(c_73,plain,(
    r2_hidden('#skF_5',k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_69])).

tff(c_30,plain,(
    ! [B_28,A_25] :
      ( r2_hidden(k4_tarski(B_28,k1_funct_1(A_25,B_28)),A_25)
      | ~ r2_hidden(B_28,k1_relat_1(A_25))
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_36,plain,(
    ! [A_30,B_31] :
      ( v1_funct_1(k7_relat_1(A_30,B_31))
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(k7_relat_1(A_20,B_21))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_49,plain,(
    ! [A_36,B_37,C_38] :
      ( r2_hidden(A_36,B_37)
      | ~ r2_hidden(A_36,k1_relat_1(k7_relat_1(C_38,B_37)))
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_52,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_49])).

tff(c_55,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_52])).

tff(c_147,plain,(
    ! [D_69,E_70,A_71,B_72] :
      ( r2_hidden(k4_tarski(D_69,E_70),k7_relat_1(A_71,B_72))
      | ~ r2_hidden(k4_tarski(D_69,E_70),A_71)
      | ~ r2_hidden(D_69,B_72)
      | ~ v1_relat_1(k7_relat_1(A_71,B_72))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [A_25,B_28,C_29] :
      ( k1_funct_1(A_25,B_28) = C_29
      | ~ r2_hidden(k4_tarski(B_28,C_29),A_25)
      | ~ r2_hidden(B_28,k1_relat_1(A_25))
      | ~ v1_funct_1(A_25)
      | ~ v1_relat_1(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1820,plain,(
    ! [A_1063,B_1064,D_1065,E_1066] :
      ( k1_funct_1(k7_relat_1(A_1063,B_1064),D_1065) = E_1066
      | ~ r2_hidden(D_1065,k1_relat_1(k7_relat_1(A_1063,B_1064)))
      | ~ v1_funct_1(k7_relat_1(A_1063,B_1064))
      | ~ r2_hidden(k4_tarski(D_1065,E_1066),A_1063)
      | ~ r2_hidden(D_1065,B_1064)
      | ~ v1_relat_1(k7_relat_1(A_1063,B_1064))
      | ~ v1_relat_1(A_1063) ) ),
    inference(resolution,[status(thm)],[c_147,c_28])).

tff(c_1874,plain,(
    ! [E_1066] :
      ( k1_funct_1(k7_relat_1('#skF_7','#skF_6'),'#skF_5') = E_1066
      | ~ v1_funct_1(k7_relat_1('#skF_7','#skF_6'))
      | ~ r2_hidden(k4_tarski('#skF_5',E_1066),'#skF_7')
      | ~ r2_hidden('#skF_5','#skF_6')
      | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6'))
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_42,c_1820])).

tff(c_1890,plain,(
    ! [E_1066] :
      ( k1_funct_1(k7_relat_1('#skF_7','#skF_6'),'#skF_5') = E_1066
      | ~ v1_funct_1(k7_relat_1('#skF_7','#skF_6'))
      | ~ r2_hidden(k4_tarski('#skF_5',E_1066),'#skF_7')
      | ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_55,c_1874])).

tff(c_1891,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1890])).

tff(c_1894,plain,(
    ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_20,c_1891])).

tff(c_1898,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1894])).

tff(c_1899,plain,(
    ! [E_1066] :
      ( ~ v1_funct_1(k7_relat_1('#skF_7','#skF_6'))
      | k1_funct_1(k7_relat_1('#skF_7','#skF_6'),'#skF_5') = E_1066
      | ~ r2_hidden(k4_tarski('#skF_5',E_1066),'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_1890])).

tff(c_1901,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_7','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_1899])).

tff(c_1904,plain,
    ( ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_1901])).

tff(c_1908,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_1904])).

tff(c_2108,plain,(
    ! [E_1224] :
      ( k1_funct_1(k7_relat_1('#skF_7','#skF_6'),'#skF_5') = E_1224
      | ~ r2_hidden(k4_tarski('#skF_5',E_1224),'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_1899])).

tff(c_2133,plain,
    ( k1_funct_1(k7_relat_1('#skF_7','#skF_6'),'#skF_5') = k1_funct_1('#skF_7','#skF_5')
    | ~ r2_hidden('#skF_5',k1_relat_1('#skF_7'))
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_2108])).

tff(c_2140,plain,(
    k1_funct_1(k7_relat_1('#skF_7','#skF_6'),'#skF_5') = k1_funct_1('#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_73,c_2133])).

tff(c_2142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_2140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:28:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.32/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.32/1.77  
% 4.32/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.32/1.78  %$ r2_hidden > v1_relat_1 > v1_funct_1 > k7_relat_1 > k4_tarski > k1_funct_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 4.32/1.78  
% 4.32/1.78  %Foreground sorts:
% 4.32/1.78  
% 4.32/1.78  
% 4.32/1.78  %Background operators:
% 4.32/1.78  
% 4.32/1.78  
% 4.32/1.78  %Foreground operators:
% 4.32/1.78  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.32/1.78  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.32/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.32/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.32/1.78  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.32/1.78  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.32/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.32/1.78  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.32/1.78  tff('#skF_7', type, '#skF_7': $i).
% 4.32/1.78  tff('#skF_5', type, '#skF_5': $i).
% 4.32/1.78  tff('#skF_6', type, '#skF_6': $i).
% 4.32/1.78  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.32/1.78  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.32/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.32/1.78  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.32/1.78  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.32/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.32/1.78  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.32/1.78  
% 4.32/1.79  tff(f_86, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) => (k1_funct_1(k7_relat_1(C, B), A) = k1_funct_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_funct_1)).
% 4.32/1.79  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 4.32/1.79  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> r2_hidden(k4_tarski(B, C), A))) & (~r2_hidden(B, k1_relat_1(A)) => ((C = k1_funct_1(A, B)) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 4.32/1.79  tff(f_77, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_funct_1)).
% 4.32/1.79  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.32/1.79  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (v1_relat_1(C) => ((C = k7_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (r2_hidden(D, B) & r2_hidden(k4_tarski(D, E), A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_relat_1)).
% 4.32/1.79  tff(c_40, plain, (k1_funct_1(k7_relat_1('#skF_7', '#skF_6'), '#skF_5')!=k1_funct_1('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.32/1.79  tff(c_46, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.32/1.79  tff(c_44, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.32/1.79  tff(c_42, plain, (r2_hidden('#skF_5', k1_relat_1(k7_relat_1('#skF_7', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.32/1.79  tff(c_62, plain, (![A_41, C_42, B_43]: (r2_hidden(A_41, k1_relat_1(C_42)) | ~r2_hidden(A_41, k1_relat_1(k7_relat_1(C_42, B_43))) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.32/1.79  tff(c_69, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_42, c_62])).
% 4.32/1.79  tff(c_73, plain, (r2_hidden('#skF_5', k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_69])).
% 4.32/1.79  tff(c_30, plain, (![B_28, A_25]: (r2_hidden(k4_tarski(B_28, k1_funct_1(A_25, B_28)), A_25) | ~r2_hidden(B_28, k1_relat_1(A_25)) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.32/1.79  tff(c_36, plain, (![A_30, B_31]: (v1_funct_1(k7_relat_1(A_30, B_31)) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.32/1.79  tff(c_20, plain, (![A_20, B_21]: (v1_relat_1(k7_relat_1(A_20, B_21)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.32/1.79  tff(c_49, plain, (![A_36, B_37, C_38]: (r2_hidden(A_36, B_37) | ~r2_hidden(A_36, k1_relat_1(k7_relat_1(C_38, B_37))) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.32/1.79  tff(c_52, plain, (r2_hidden('#skF_5', '#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_42, c_49])).
% 4.32/1.79  tff(c_55, plain, (r2_hidden('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_52])).
% 4.32/1.79  tff(c_147, plain, (![D_69, E_70, A_71, B_72]: (r2_hidden(k4_tarski(D_69, E_70), k7_relat_1(A_71, B_72)) | ~r2_hidden(k4_tarski(D_69, E_70), A_71) | ~r2_hidden(D_69, B_72) | ~v1_relat_1(k7_relat_1(A_71, B_72)) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.32/1.79  tff(c_28, plain, (![A_25, B_28, C_29]: (k1_funct_1(A_25, B_28)=C_29 | ~r2_hidden(k4_tarski(B_28, C_29), A_25) | ~r2_hidden(B_28, k1_relat_1(A_25)) | ~v1_funct_1(A_25) | ~v1_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.32/1.79  tff(c_1820, plain, (![A_1063, B_1064, D_1065, E_1066]: (k1_funct_1(k7_relat_1(A_1063, B_1064), D_1065)=E_1066 | ~r2_hidden(D_1065, k1_relat_1(k7_relat_1(A_1063, B_1064))) | ~v1_funct_1(k7_relat_1(A_1063, B_1064)) | ~r2_hidden(k4_tarski(D_1065, E_1066), A_1063) | ~r2_hidden(D_1065, B_1064) | ~v1_relat_1(k7_relat_1(A_1063, B_1064)) | ~v1_relat_1(A_1063))), inference(resolution, [status(thm)], [c_147, c_28])).
% 4.32/1.79  tff(c_1874, plain, (![E_1066]: (k1_funct_1(k7_relat_1('#skF_7', '#skF_6'), '#skF_5')=E_1066 | ~v1_funct_1(k7_relat_1('#skF_7', '#skF_6')) | ~r2_hidden(k4_tarski('#skF_5', E_1066), '#skF_7') | ~r2_hidden('#skF_5', '#skF_6') | ~v1_relat_1(k7_relat_1('#skF_7', '#skF_6')) | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_42, c_1820])).
% 4.32/1.79  tff(c_1890, plain, (![E_1066]: (k1_funct_1(k7_relat_1('#skF_7', '#skF_6'), '#skF_5')=E_1066 | ~v1_funct_1(k7_relat_1('#skF_7', '#skF_6')) | ~r2_hidden(k4_tarski('#skF_5', E_1066), '#skF_7') | ~v1_relat_1(k7_relat_1('#skF_7', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_55, c_1874])).
% 4.32/1.79  tff(c_1891, plain, (~v1_relat_1(k7_relat_1('#skF_7', '#skF_6'))), inference(splitLeft, [status(thm)], [c_1890])).
% 4.32/1.79  tff(c_1894, plain, (~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_20, c_1891])).
% 4.32/1.79  tff(c_1898, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_1894])).
% 4.32/1.79  tff(c_1899, plain, (![E_1066]: (~v1_funct_1(k7_relat_1('#skF_7', '#skF_6')) | k1_funct_1(k7_relat_1('#skF_7', '#skF_6'), '#skF_5')=E_1066 | ~r2_hidden(k4_tarski('#skF_5', E_1066), '#skF_7'))), inference(splitRight, [status(thm)], [c_1890])).
% 4.32/1.79  tff(c_1901, plain, (~v1_funct_1(k7_relat_1('#skF_7', '#skF_6'))), inference(splitLeft, [status(thm)], [c_1899])).
% 4.32/1.79  tff(c_1904, plain, (~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_36, c_1901])).
% 4.32/1.79  tff(c_1908, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_1904])).
% 4.32/1.79  tff(c_2108, plain, (![E_1224]: (k1_funct_1(k7_relat_1('#skF_7', '#skF_6'), '#skF_5')=E_1224 | ~r2_hidden(k4_tarski('#skF_5', E_1224), '#skF_7'))), inference(splitRight, [status(thm)], [c_1899])).
% 4.32/1.79  tff(c_2133, plain, (k1_funct_1(k7_relat_1('#skF_7', '#skF_6'), '#skF_5')=k1_funct_1('#skF_7', '#skF_5') | ~r2_hidden('#skF_5', k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_30, c_2108])).
% 4.32/1.79  tff(c_2140, plain, (k1_funct_1(k7_relat_1('#skF_7', '#skF_6'), '#skF_5')=k1_funct_1('#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_73, c_2133])).
% 4.32/1.79  tff(c_2142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_2140])).
% 4.32/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.32/1.79  
% 4.32/1.79  Inference rules
% 4.32/1.79  ----------------------
% 4.32/1.79  #Ref     : 0
% 4.32/1.79  #Sup     : 285
% 4.32/1.79  #Fact    : 1
% 4.32/1.79  #Define  : 0
% 4.32/1.79  #Split   : 2
% 4.32/1.79  #Chain   : 0
% 4.32/1.79  #Close   : 0
% 4.32/1.79  
% 4.32/1.79  Ordering : KBO
% 4.32/1.79  
% 4.32/1.79  Simplification rules
% 4.32/1.79  ----------------------
% 4.32/1.79  #Subsume      : 34
% 4.32/1.79  #Demod        : 48
% 4.32/1.79  #Tautology    : 95
% 4.32/1.79  #SimpNegUnit  : 1
% 4.32/1.79  #BackRed      : 0
% 4.32/1.79  
% 4.32/1.79  #Partial instantiations: 660
% 4.32/1.79  #Strategies tried      : 1
% 4.32/1.79  
% 4.32/1.79  Timing (in seconds)
% 4.32/1.79  ----------------------
% 4.32/1.79  Preprocessing        : 0.31
% 4.32/1.79  Parsing              : 0.16
% 4.32/1.79  CNF conversion       : 0.03
% 4.32/1.79  Main loop            : 0.72
% 4.32/1.79  Inferencing          : 0.30
% 4.32/1.79  Reduction            : 0.15
% 4.32/1.79  Demodulation         : 0.11
% 4.32/1.79  BG Simplification    : 0.04
% 4.32/1.79  Subsumption          : 0.20
% 4.32/1.79  Abstraction          : 0.04
% 4.32/1.79  MUC search           : 0.00
% 4.32/1.79  Cooper               : 0.00
% 4.32/1.79  Total                : 1.06
% 4.32/1.79  Index Insertion      : 0.00
% 4.32/1.79  Index Deletion       : 0.00
% 4.32/1.79  Index Matching       : 0.00
% 4.32/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
