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
% DateTime   : Thu Dec  3 10:06:46 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   49 (  88 expanded)
%              Number of leaves         :   19 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   83 ( 254 expanded)
%              Number of equality atoms :   12 (  41 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_wellord1 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( ( v2_wellord1(C)
            & r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C)) )
         => ( r1_tarski(k1_wellord1(C,A),k1_wellord1(C,B))
          <=> ( A = B
              | r2_hidden(A,k1_wellord1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_wellord1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

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

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( v2_wellord1(C)
          & r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) )
       => ( r2_hidden(k4_tarski(A,B),C)
        <=> r1_tarski(k1_wellord1(C,A),k1_wellord1(C,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).

tff(c_36,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_40,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k1_wellord1('#skF_5','#skF_3'),k1_wellord1('#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_59,plain,(
    ~ r1_tarski(k1_wellord1('#skF_5','#skF_3'),k1_wellord1('#skF_5','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_48,plain,
    ( r1_tarski(k1_wellord1('#skF_5','#skF_3'),k1_wellord1('#skF_5','#skF_4'))
    | r2_hidden('#skF_3',k1_wellord1('#skF_5','#skF_4'))
    | '#skF_3' = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_66,plain,
    ( r2_hidden('#skF_3',k1_wellord1('#skF_5','#skF_4'))
    | '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_48])).

tff(c_67,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_68,plain,(
    ~ r1_tarski(k1_wellord1('#skF_5','#skF_4'),k1_wellord1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_59])).

tff(c_72,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_68])).

tff(c_73,plain,(
    r2_hidden('#skF_3',k1_wellord1('#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_10,plain,(
    ! [D_14,B_10,A_3] :
      ( r2_hidden(k4_tarski(D_14,B_10),A_3)
      | ~ r2_hidden(D_14,k1_wellord1(A_3,B_10))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_34,plain,(
    v2_wellord1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_32,plain,(
    r2_hidden('#skF_3',k3_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_30,plain,(
    r2_hidden('#skF_4',k3_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_126,plain,(
    ! [C_48,A_49,B_50] :
      ( r1_tarski(k1_wellord1(C_48,A_49),k1_wellord1(C_48,B_50))
      | ~ r2_hidden(k4_tarski(A_49,B_50),C_48)
      | ~ r2_hidden(B_50,k3_relat_1(C_48))
      | ~ r2_hidden(A_49,k3_relat_1(C_48))
      | ~ v2_wellord1(C_48)
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_132,plain,
    ( ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),'#skF_5')
    | ~ r2_hidden('#skF_4',k3_relat_1('#skF_5'))
    | ~ r2_hidden('#skF_3',k3_relat_1('#skF_5'))
    | ~ v2_wellord1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_126,c_59])).

tff(c_138,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_132])).

tff(c_142,plain,
    ( ~ r2_hidden('#skF_3',k1_wellord1('#skF_5','#skF_4'))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_138])).

tff(c_146,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_73,c_142])).

tff(c_147,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_148,plain,(
    r1_tarski(k1_wellord1('#skF_5','#skF_3'),k1_wellord1('#skF_5','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_38,plain,
    ( ~ r2_hidden('#skF_3',k1_wellord1('#skF_5','#skF_4'))
    | ~ r1_tarski(k1_wellord1('#skF_5','#skF_3'),k1_wellord1('#skF_5','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_159,plain,(
    ~ r2_hidden('#skF_3',k1_wellord1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_38])).

tff(c_197,plain,(
    ! [A_72,B_73,C_74] :
      ( r2_hidden(k4_tarski(A_72,B_73),C_74)
      | ~ r1_tarski(k1_wellord1(C_74,A_72),k1_wellord1(C_74,B_73))
      | ~ r2_hidden(B_73,k3_relat_1(C_74))
      | ~ r2_hidden(A_72,k3_relat_1(C_74))
      | ~ v2_wellord1(C_74)
      | ~ v1_relat_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_203,plain,
    ( r2_hidden(k4_tarski('#skF_3','#skF_4'),'#skF_5')
    | ~ r2_hidden('#skF_4',k3_relat_1('#skF_5'))
    | ~ r2_hidden('#skF_3',k3_relat_1('#skF_5'))
    | ~ v2_wellord1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_148,c_197])).

tff(c_211,plain,(
    r2_hidden(k4_tarski('#skF_3','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_32,c_30,c_203])).

tff(c_8,plain,(
    ! [D_14,A_3,B_10] :
      ( r2_hidden(D_14,k1_wellord1(A_3,B_10))
      | ~ r2_hidden(k4_tarski(D_14,B_10),A_3)
      | D_14 = B_10
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_215,plain,
    ( r2_hidden('#skF_3',k1_wellord1('#skF_5','#skF_4'))
    | '#skF_3' = '#skF_4'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_211,c_8])).

tff(c_218,plain,
    ( r2_hidden('#skF_3',k1_wellord1('#skF_5','#skF_4'))
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_215])).

tff(c_220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_159,c_218])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:44:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.21  
% 2.03/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.21  %$ r2_hidden > r1_tarski > v2_wellord1 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 2.03/1.21  
% 2.03/1.21  %Foreground sorts:
% 2.03/1.21  
% 2.03/1.21  
% 2.03/1.21  %Background operators:
% 2.03/1.21  
% 2.03/1.21  
% 2.03/1.21  %Foreground operators:
% 2.03/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.03/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.03/1.21  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.03/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.03/1.21  tff('#skF_5', type, '#skF_5': $i).
% 2.03/1.21  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 2.03/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.03/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.03/1.21  tff('#skF_4', type, '#skF_4': $i).
% 2.03/1.21  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 2.03/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.21  
% 2.03/1.22  tff(f_71, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) => (r1_tarski(k1_wellord1(C, A), k1_wellord1(C, B)) <=> ((A = B) | r2_hidden(A, k1_wellord1(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_wellord1)).
% 2.03/1.22  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.03/1.22  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_wellord1)).
% 2.03/1.22  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => (((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) => (r2_hidden(k4_tarski(A, B), C) <=> r1_tarski(k1_wellord1(C, A), k1_wellord1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_wellord1)).
% 2.03/1.22  tff(c_36, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.03/1.22  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.22  tff(c_40, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k1_wellord1('#skF_5', '#skF_3'), k1_wellord1('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.03/1.22  tff(c_59, plain, (~r1_tarski(k1_wellord1('#skF_5', '#skF_3'), k1_wellord1('#skF_5', '#skF_4'))), inference(splitLeft, [status(thm)], [c_40])).
% 2.03/1.22  tff(c_48, plain, (r1_tarski(k1_wellord1('#skF_5', '#skF_3'), k1_wellord1('#skF_5', '#skF_4')) | r2_hidden('#skF_3', k1_wellord1('#skF_5', '#skF_4')) | '#skF_3'='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.03/1.22  tff(c_66, plain, (r2_hidden('#skF_3', k1_wellord1('#skF_5', '#skF_4')) | '#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_59, c_48])).
% 2.03/1.22  tff(c_67, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_66])).
% 2.03/1.22  tff(c_68, plain, (~r1_tarski(k1_wellord1('#skF_5', '#skF_4'), k1_wellord1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_59])).
% 2.03/1.22  tff(c_72, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_68])).
% 2.03/1.22  tff(c_73, plain, (r2_hidden('#skF_3', k1_wellord1('#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_66])).
% 2.03/1.22  tff(c_10, plain, (![D_14, B_10, A_3]: (r2_hidden(k4_tarski(D_14, B_10), A_3) | ~r2_hidden(D_14, k1_wellord1(A_3, B_10)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.03/1.22  tff(c_34, plain, (v2_wellord1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.03/1.22  tff(c_32, plain, (r2_hidden('#skF_3', k3_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.03/1.22  tff(c_30, plain, (r2_hidden('#skF_4', k3_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.03/1.22  tff(c_126, plain, (![C_48, A_49, B_50]: (r1_tarski(k1_wellord1(C_48, A_49), k1_wellord1(C_48, B_50)) | ~r2_hidden(k4_tarski(A_49, B_50), C_48) | ~r2_hidden(B_50, k3_relat_1(C_48)) | ~r2_hidden(A_49, k3_relat_1(C_48)) | ~v2_wellord1(C_48) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.03/1.22  tff(c_132, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), '#skF_5') | ~r2_hidden('#skF_4', k3_relat_1('#skF_5')) | ~r2_hidden('#skF_3', k3_relat_1('#skF_5')) | ~v2_wellord1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_126, c_59])).
% 2.03/1.22  tff(c_138, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_132])).
% 2.03/1.22  tff(c_142, plain, (~r2_hidden('#skF_3', k1_wellord1('#skF_5', '#skF_4')) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_10, c_138])).
% 2.03/1.22  tff(c_146, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_73, c_142])).
% 2.03/1.22  tff(c_147, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_40])).
% 2.03/1.22  tff(c_148, plain, (r1_tarski(k1_wellord1('#skF_5', '#skF_3'), k1_wellord1('#skF_5', '#skF_4'))), inference(splitRight, [status(thm)], [c_40])).
% 2.03/1.22  tff(c_38, plain, (~r2_hidden('#skF_3', k1_wellord1('#skF_5', '#skF_4')) | ~r1_tarski(k1_wellord1('#skF_5', '#skF_3'), k1_wellord1('#skF_5', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.03/1.22  tff(c_159, plain, (~r2_hidden('#skF_3', k1_wellord1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_148, c_38])).
% 2.03/1.22  tff(c_197, plain, (![A_72, B_73, C_74]: (r2_hidden(k4_tarski(A_72, B_73), C_74) | ~r1_tarski(k1_wellord1(C_74, A_72), k1_wellord1(C_74, B_73)) | ~r2_hidden(B_73, k3_relat_1(C_74)) | ~r2_hidden(A_72, k3_relat_1(C_74)) | ~v2_wellord1(C_74) | ~v1_relat_1(C_74))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.03/1.22  tff(c_203, plain, (r2_hidden(k4_tarski('#skF_3', '#skF_4'), '#skF_5') | ~r2_hidden('#skF_4', k3_relat_1('#skF_5')) | ~r2_hidden('#skF_3', k3_relat_1('#skF_5')) | ~v2_wellord1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_148, c_197])).
% 2.03/1.22  tff(c_211, plain, (r2_hidden(k4_tarski('#skF_3', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_32, c_30, c_203])).
% 2.03/1.22  tff(c_8, plain, (![D_14, A_3, B_10]: (r2_hidden(D_14, k1_wellord1(A_3, B_10)) | ~r2_hidden(k4_tarski(D_14, B_10), A_3) | D_14=B_10 | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.03/1.22  tff(c_215, plain, (r2_hidden('#skF_3', k1_wellord1('#skF_5', '#skF_4')) | '#skF_3'='#skF_4' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_211, c_8])).
% 2.03/1.22  tff(c_218, plain, (r2_hidden('#skF_3', k1_wellord1('#skF_5', '#skF_4')) | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_215])).
% 2.03/1.22  tff(c_220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_159, c_218])).
% 2.03/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.22  
% 2.03/1.22  Inference rules
% 2.03/1.22  ----------------------
% 2.03/1.22  #Ref     : 0
% 2.03/1.22  #Sup     : 27
% 2.03/1.22  #Fact    : 0
% 2.03/1.22  #Define  : 0
% 2.03/1.22  #Split   : 3
% 2.03/1.22  #Chain   : 0
% 2.03/1.22  #Close   : 0
% 2.03/1.22  
% 2.03/1.22  Ordering : KBO
% 2.03/1.22  
% 2.03/1.22  Simplification rules
% 2.03/1.23  ----------------------
% 2.03/1.23  #Subsume      : 1
% 2.03/1.23  #Demod        : 23
% 2.03/1.23  #Tautology    : 11
% 2.03/1.23  #SimpNegUnit  : 3
% 2.03/1.23  #BackRed      : 2
% 2.03/1.23  
% 2.03/1.23  #Partial instantiations: 0
% 2.03/1.23  #Strategies tried      : 1
% 2.03/1.23  
% 2.03/1.23  Timing (in seconds)
% 2.03/1.23  ----------------------
% 2.03/1.23  Preprocessing        : 0.30
% 2.03/1.23  Parsing              : 0.15
% 2.03/1.23  CNF conversion       : 0.02
% 2.03/1.23  Main loop            : 0.20
% 2.03/1.23  Inferencing          : 0.07
% 2.03/1.23  Reduction            : 0.05
% 2.03/1.23  Demodulation         : 0.04
% 2.03/1.23  BG Simplification    : 0.02
% 2.03/1.23  Subsumption          : 0.04
% 2.03/1.23  Abstraction          : 0.01
% 2.03/1.23  MUC search           : 0.00
% 2.03/1.23  Cooper               : 0.00
% 2.20/1.23  Total                : 0.52
% 2.20/1.23  Index Insertion      : 0.00
% 2.20/1.23  Index Deletion       : 0.00
% 2.20/1.23  Index Matching       : 0.00
% 2.20/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
