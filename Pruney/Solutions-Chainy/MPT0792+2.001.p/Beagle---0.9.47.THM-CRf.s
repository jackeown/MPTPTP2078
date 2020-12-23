%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:47 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 124 expanded)
%              Number of leaves         :   28 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  101 ( 423 expanded)
%              Number of equality atoms :   14 (  55 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_wellord1,type,(
    v1_wellord1: $i > $o )).

tff(f_108,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_wellord1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( v2_wellord1(C)
          & r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) )
       => ( r2_hidden(k4_tarski(A,B),C)
        <=> r1_tarski(k1_wellord1(C,A),k1_wellord1(C,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v6_relat_2(A)
      <=> ! [B,C] :
            ~ ( r2_hidden(B,k3_relat_1(A))
              & r2_hidden(C,k3_relat_1(A))
              & B != C
              & ~ r2_hidden(k4_tarski(B,C),A)
              & ~ r2_hidden(k4_tarski(C,B),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l4_wellord1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

tff(c_62,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_60,plain,(
    v2_wellord1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_56,plain,(
    r2_hidden('#skF_6',k3_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_176,plain,(
    ! [A_66,B_67,C_68] :
      ( r2_hidden(k4_tarski(A_66,B_67),C_68)
      | ~ r1_tarski(k1_wellord1(C_68,A_66),k1_wellord1(C_68,B_67))
      | ~ r2_hidden(B_67,k3_relat_1(C_68))
      | ~ r2_hidden(A_66,k3_relat_1(C_68))
      | ~ v2_wellord1(C_68)
      | ~ v1_relat_1(C_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_181,plain,(
    ! [A_66,C_68] :
      ( r2_hidden(k4_tarski(A_66,A_66),C_68)
      | ~ r2_hidden(A_66,k3_relat_1(C_68))
      | ~ v2_wellord1(C_68)
      | ~ v1_relat_1(C_68) ) ),
    inference(resolution,[status(thm)],[c_6,c_176])).

tff(c_64,plain,(
    ~ r2_hidden('#skF_6',k1_wellord1('#skF_7','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_30,plain,(
    ! [A_15] :
      ( v6_relat_2(A_15)
      | ~ v2_wellord1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_58,plain,(
    r2_hidden('#skF_5',k3_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_239,plain,(
    ! [C_78,B_79,A_80] :
      ( r2_hidden(k4_tarski(C_78,B_79),A_80)
      | r2_hidden(k4_tarski(B_79,C_78),A_80)
      | C_78 = B_79
      | ~ r2_hidden(C_78,k3_relat_1(A_80))
      | ~ r2_hidden(B_79,k3_relat_1(A_80))
      | ~ v6_relat_2(A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_54,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_267,plain,
    ( r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_7')
    | '#skF_5' = '#skF_6'
    | ~ r2_hidden('#skF_5',k3_relat_1('#skF_7'))
    | ~ r2_hidden('#skF_6',k3_relat_1('#skF_7'))
    | ~ v6_relat_2('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_239,c_54])).

tff(c_304,plain,
    ( r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_7')
    | '#skF_5' = '#skF_6'
    | ~ v6_relat_2('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_58,c_267])).

tff(c_314,plain,(
    ~ v6_relat_2('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_304])).

tff(c_320,plain,
    ( ~ v2_wellord1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_314])).

tff(c_327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_320])).

tff(c_328,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_353,plain,(
    r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_328])).

tff(c_8,plain,(
    ! [D_14,A_3,B_10] :
      ( r2_hidden(D_14,k1_wellord1(A_3,B_10))
      | ~ r2_hidden(k4_tarski(D_14,B_10),A_3)
      | D_14 = B_10
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_356,plain,
    ( r2_hidden('#skF_6',k1_wellord1('#skF_7','#skF_5'))
    | '#skF_5' = '#skF_6'
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_353,c_8])).

tff(c_359,plain,
    ( r2_hidden('#skF_6',k1_wellord1('#skF_7','#skF_5'))
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_356])).

tff(c_360,plain,(
    '#skF_5' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_359])).

tff(c_368,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_54])).

tff(c_380,plain,
    ( ~ r2_hidden('#skF_6',k3_relat_1('#skF_7'))
    | ~ v2_wellord1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_181,c_368])).

tff(c_387,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_380])).

tff(c_388,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_328])).

tff(c_389,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_5'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_328])).

tff(c_404,plain,(
    ~ r2_hidden(k4_tarski('#skF_6','#skF_6'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_389])).

tff(c_409,plain,
    ( ~ r2_hidden('#skF_6',k3_relat_1('#skF_7'))
    | ~ v2_wellord1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_181,c_404])).

tff(c_416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_409])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:13:25 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.39  
% 2.61/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.40  %$ r2_hidden > r1_tarski > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.61/1.40  
% 2.61/1.40  %Foreground sorts:
% 2.61/1.40  
% 2.61/1.40  
% 2.61/1.40  %Background operators:
% 2.61/1.40  
% 2.61/1.40  
% 2.61/1.40  %Foreground operators:
% 2.61/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.61/1.40  tff('#skF_4', type, '#skF_4': $i > $i).
% 2.61/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.40  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.61/1.40  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 2.61/1.40  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 2.61/1.40  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.61/1.40  tff(v6_relat_2, type, v6_relat_2: $i > $o).
% 2.61/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.61/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.40  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 2.61/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.61/1.40  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 2.61/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.61/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.61/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.61/1.40  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.61/1.40  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 2.61/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.40  tff(v1_wellord1, type, v1_wellord1: $i > $o).
% 2.61/1.40  
% 2.61/1.41  tff(f_108, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => ((((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) & (![D]: (r2_hidden(D, k1_wellord1(C, A)) => (r2_hidden(k4_tarski(D, B), C) & ~(D = B))))) => r2_hidden(k4_tarski(A, B), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_wellord1)).
% 2.61/1.41  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.61/1.41  tff(f_89, axiom, (![A, B, C]: (v1_relat_1(C) => (((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) => (r2_hidden(k4_tarski(A, B), C) <=> r1_tarski(k1_wellord1(C, A), k1_wellord1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_wellord1)).
% 2.61/1.41  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) <=> ((((v1_relat_2(A) & v8_relat_2(A)) & v4_relat_2(A)) & v6_relat_2(A)) & v1_wellord1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_wellord1)).
% 2.61/1.41  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (v6_relat_2(A) <=> (![B, C]: ~((((r2_hidden(B, k3_relat_1(A)) & r2_hidden(C, k3_relat_1(A))) & ~(B = C)) & ~r2_hidden(k4_tarski(B, C), A)) & ~r2_hidden(k4_tarski(C, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l4_wellord1)).
% 2.61/1.41  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 2.61/1.41  tff(c_62, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.61/1.41  tff(c_60, plain, (v2_wellord1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.61/1.41  tff(c_56, plain, (r2_hidden('#skF_6', k3_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.61/1.41  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.41  tff(c_176, plain, (![A_66, B_67, C_68]: (r2_hidden(k4_tarski(A_66, B_67), C_68) | ~r1_tarski(k1_wellord1(C_68, A_66), k1_wellord1(C_68, B_67)) | ~r2_hidden(B_67, k3_relat_1(C_68)) | ~r2_hidden(A_66, k3_relat_1(C_68)) | ~v2_wellord1(C_68) | ~v1_relat_1(C_68))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.61/1.41  tff(c_181, plain, (![A_66, C_68]: (r2_hidden(k4_tarski(A_66, A_66), C_68) | ~r2_hidden(A_66, k3_relat_1(C_68)) | ~v2_wellord1(C_68) | ~v1_relat_1(C_68))), inference(resolution, [status(thm)], [c_6, c_176])).
% 2.61/1.41  tff(c_64, plain, (~r2_hidden('#skF_6', k1_wellord1('#skF_7', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.61/1.41  tff(c_30, plain, (![A_15]: (v6_relat_2(A_15) | ~v2_wellord1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.61/1.41  tff(c_58, plain, (r2_hidden('#skF_5', k3_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.61/1.41  tff(c_239, plain, (![C_78, B_79, A_80]: (r2_hidden(k4_tarski(C_78, B_79), A_80) | r2_hidden(k4_tarski(B_79, C_78), A_80) | C_78=B_79 | ~r2_hidden(C_78, k3_relat_1(A_80)) | ~r2_hidden(B_79, k3_relat_1(A_80)) | ~v6_relat_2(A_80) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.61/1.41  tff(c_54, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.61/1.41  tff(c_267, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_7') | '#skF_5'='#skF_6' | ~r2_hidden('#skF_5', k3_relat_1('#skF_7')) | ~r2_hidden('#skF_6', k3_relat_1('#skF_7')) | ~v6_relat_2('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_239, c_54])).
% 2.61/1.41  tff(c_304, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_7') | '#skF_5'='#skF_6' | ~v6_relat_2('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_56, c_58, c_267])).
% 2.61/1.41  tff(c_314, plain, (~v6_relat_2('#skF_7')), inference(splitLeft, [status(thm)], [c_304])).
% 2.61/1.41  tff(c_320, plain, (~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_30, c_314])).
% 2.61/1.41  tff(c_327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_320])).
% 2.61/1.41  tff(c_328, plain, ('#skF_5'='#skF_6' | r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_7')), inference(splitRight, [status(thm)], [c_304])).
% 2.61/1.41  tff(c_353, plain, (r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_7')), inference(splitLeft, [status(thm)], [c_328])).
% 2.61/1.41  tff(c_8, plain, (![D_14, A_3, B_10]: (r2_hidden(D_14, k1_wellord1(A_3, B_10)) | ~r2_hidden(k4_tarski(D_14, B_10), A_3) | D_14=B_10 | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.61/1.41  tff(c_356, plain, (r2_hidden('#skF_6', k1_wellord1('#skF_7', '#skF_5')) | '#skF_5'='#skF_6' | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_353, c_8])).
% 2.61/1.41  tff(c_359, plain, (r2_hidden('#skF_6', k1_wellord1('#skF_7', '#skF_5')) | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_356])).
% 2.61/1.41  tff(c_360, plain, ('#skF_5'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_64, c_359])).
% 2.61/1.41  tff(c_368, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_360, c_54])).
% 2.61/1.41  tff(c_380, plain, (~r2_hidden('#skF_6', k3_relat_1('#skF_7')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_181, c_368])).
% 2.61/1.41  tff(c_387, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_380])).
% 2.61/1.41  tff(c_388, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_328])).
% 2.61/1.41  tff(c_389, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_5'), '#skF_7')), inference(splitRight, [status(thm)], [c_328])).
% 2.61/1.41  tff(c_404, plain, (~r2_hidden(k4_tarski('#skF_6', '#skF_6'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_388, c_389])).
% 2.61/1.41  tff(c_409, plain, (~r2_hidden('#skF_6', k3_relat_1('#skF_7')) | ~v2_wellord1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_181, c_404])).
% 2.61/1.41  tff(c_416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_409])).
% 2.61/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.41  
% 2.61/1.41  Inference rules
% 2.61/1.41  ----------------------
% 2.61/1.41  #Ref     : 0
% 2.61/1.41  #Sup     : 54
% 2.61/1.41  #Fact    : 2
% 2.61/1.41  #Define  : 0
% 2.61/1.41  #Split   : 3
% 2.61/1.41  #Chain   : 0
% 2.61/1.41  #Close   : 0
% 2.61/1.41  
% 2.61/1.41  Ordering : KBO
% 2.61/1.41  
% 2.61/1.41  Simplification rules
% 2.61/1.41  ----------------------
% 2.61/1.41  #Subsume      : 5
% 2.61/1.41  #Demod        : 53
% 2.61/1.41  #Tautology    : 18
% 2.61/1.41  #SimpNegUnit  : 1
% 2.61/1.41  #BackRed      : 17
% 2.61/1.41  
% 2.61/1.41  #Partial instantiations: 0
% 2.61/1.41  #Strategies tried      : 1
% 2.61/1.41  
% 2.61/1.41  Timing (in seconds)
% 2.61/1.41  ----------------------
% 2.61/1.41  Preprocessing        : 0.31
% 2.61/1.41  Parsing              : 0.15
% 2.61/1.41  CNF conversion       : 0.02
% 2.61/1.41  Main loop            : 0.29
% 2.61/1.41  Inferencing          : 0.11
% 2.61/1.41  Reduction            : 0.08
% 2.61/1.41  Demodulation         : 0.06
% 2.61/1.41  BG Simplification    : 0.02
% 2.61/1.41  Subsumption          : 0.06
% 2.61/1.41  Abstraction          : 0.02
% 2.61/1.41  MUC search           : 0.00
% 2.61/1.41  Cooper               : 0.00
% 2.61/1.41  Total                : 0.63
% 2.61/1.41  Index Insertion      : 0.00
% 2.61/1.41  Index Deletion       : 0.00
% 2.61/1.41  Index Matching       : 0.00
% 2.61/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
