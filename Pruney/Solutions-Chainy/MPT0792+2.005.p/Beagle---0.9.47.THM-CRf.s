%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:48 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 170 expanded)
%              Number of leaves         :   25 (  76 expanded)
%              Depth                    :   10
%              Number of atoms          :  129 ( 674 expanded)
%              Number of equality atoms :   16 (  88 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(v1_wellord1,type,(
    v1_wellord1: $i > $o )).

tff(f_103,negated_conjecture,(
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

tff(f_84,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( v2_wellord1(C)
          & r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) )
       => ( r1_tarski(k1_wellord1(C,A),k1_wellord1(C,B))
        <=> ( A = B
            | r2_hidden(A,k1_wellord1(C,B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_wellord1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( v2_wellord1(C)
          & r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) )
       => ( r2_hidden(k4_tarski(A,B),C)
        <=> r1_tarski(k1_wellord1(C,A),k1_wellord1(C,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_wellord1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
      <=> ( v1_relat_2(A)
          & v8_relat_2(A)
          & v4_relat_2(A)
          & v6_relat_2(A)
          & v1_wellord1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_wellord1)).

tff(f_58,axiom,(
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

tff(c_44,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_42,plain,(
    v2_wellord1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_38,plain,(
    r2_hidden('#skF_4',k3_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,(
    ! [C_14,B_13] :
      ( r1_tarski(k1_wellord1(C_14,B_13),k1_wellord1(C_14,B_13))
      | ~ r2_hidden(B_13,k3_relat_1(C_14))
      | ~ v2_wellord1(C_14)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_127,plain,(
    ! [A_40,B_41,C_42] :
      ( r2_hidden(k4_tarski(A_40,B_41),C_42)
      | ~ r1_tarski(k1_wellord1(C_42,A_40),k1_wellord1(C_42,B_41))
      | ~ r2_hidden(B_41,k3_relat_1(C_42))
      | ~ r2_hidden(A_40,k3_relat_1(C_42))
      | ~ v2_wellord1(C_42)
      | ~ v1_relat_1(C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_192,plain,(
    ! [B_47,C_48] :
      ( r2_hidden(k4_tarski(B_47,B_47),C_48)
      | ~ r2_hidden(B_47,k3_relat_1(C_48))
      | ~ v2_wellord1(C_48)
      | ~ v1_relat_1(C_48) ) ),
    inference(resolution,[status(thm)],[c_34,c_127])).

tff(c_6,plain,(
    ! [A_1] :
      ( v6_relat_2(A_1)
      | ~ v2_wellord1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_40,plain,(
    r2_hidden('#skF_3',k3_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_100,plain,(
    ! [C_37,B_38,A_39] :
      ( r2_hidden(k4_tarski(C_37,B_38),A_39)
      | r2_hidden(k4_tarski(B_38,C_37),A_39)
      | C_37 = B_38
      | ~ r2_hidden(C_37,k3_relat_1(A_39))
      | ~ r2_hidden(B_38,k3_relat_1(A_39))
      | ~ v6_relat_2(A_39)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    ~ r2_hidden(k4_tarski('#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_109,plain,
    ( r2_hidden(k4_tarski('#skF_4','#skF_3'),'#skF_5')
    | '#skF_3' = '#skF_4'
    | ~ r2_hidden('#skF_3',k3_relat_1('#skF_5'))
    | ~ r2_hidden('#skF_4',k3_relat_1('#skF_5'))
    | ~ v6_relat_2('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_100,c_36])).

tff(c_122,plain,
    ( r2_hidden(k4_tarski('#skF_4','#skF_3'),'#skF_5')
    | '#skF_3' = '#skF_4'
    | ~ v6_relat_2('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_38,c_40,c_109])).

tff(c_140,plain,(
    ~ v6_relat_2('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_146,plain,
    ( ~ v2_wellord1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_140])).

tff(c_153,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_146])).

tff(c_155,plain,(
    v6_relat_2('#skF_5') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_118,plain,
    ( r2_hidden(k4_tarski('#skF_4','#skF_3'),'#skF_5')
    | '#skF_3' = '#skF_4'
    | ~ r2_hidden('#skF_4',k3_relat_1('#skF_5'))
    | ~ r2_hidden('#skF_3',k3_relat_1('#skF_5'))
    | ~ v6_relat_2('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_100,c_36])).

tff(c_126,plain,
    ( r2_hidden(k4_tarski('#skF_4','#skF_3'),'#skF_5')
    | '#skF_3' = '#skF_4'
    | ~ v6_relat_2('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_38,c_118])).

tff(c_157,plain,
    ( r2_hidden(k4_tarski('#skF_4','#skF_3'),'#skF_5')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_126])).

tff(c_158,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_161,plain,(
    ~ r2_hidden(k4_tarski('#skF_4','#skF_4'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_36])).

tff(c_195,plain,
    ( ~ r2_hidden('#skF_4',k3_relat_1('#skF_5'))
    | ~ v2_wellord1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_192,c_161])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_195])).

tff(c_201,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_46,plain,(
    ~ r2_hidden('#skF_4',k1_wellord1('#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_154,plain,
    ( '#skF_3' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_4','#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_202,plain,(
    r2_hidden(k4_tarski('#skF_4','#skF_3'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_154])).

tff(c_28,plain,(
    ! [C_11,A_9,B_10] :
      ( r1_tarski(k1_wellord1(C_11,A_9),k1_wellord1(C_11,B_10))
      | ~ r2_hidden(k4_tarski(A_9,B_10),C_11)
      | ~ r2_hidden(B_10,k3_relat_1(C_11))
      | ~ r2_hidden(A_9,k3_relat_1(C_11))
      | ~ v2_wellord1(C_11)
      | ~ v1_relat_1(C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_222,plain,(
    ! [A_54,C_55,B_56] :
      ( r2_hidden(A_54,k1_wellord1(C_55,B_56))
      | B_56 = A_54
      | ~ r1_tarski(k1_wellord1(C_55,A_54),k1_wellord1(C_55,B_56))
      | ~ r2_hidden(B_56,k3_relat_1(C_55))
      | ~ r2_hidden(A_54,k3_relat_1(C_55))
      | ~ v2_wellord1(C_55)
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_236,plain,(
    ! [A_57,C_58,B_59] :
      ( r2_hidden(A_57,k1_wellord1(C_58,B_59))
      | B_59 = A_57
      | ~ r2_hidden(k4_tarski(A_57,B_59),C_58)
      | ~ r2_hidden(B_59,k3_relat_1(C_58))
      | ~ r2_hidden(A_57,k3_relat_1(C_58))
      | ~ v2_wellord1(C_58)
      | ~ v1_relat_1(C_58) ) ),
    inference(resolution,[status(thm)],[c_28,c_222])).

tff(c_245,plain,
    ( r2_hidden('#skF_4',k1_wellord1('#skF_5','#skF_3'))
    | '#skF_3' = '#skF_4'
    | ~ r2_hidden('#skF_3',k3_relat_1('#skF_5'))
    | ~ r2_hidden('#skF_4',k3_relat_1('#skF_5'))
    | ~ v2_wellord1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_202,c_236])).

tff(c_260,plain,
    ( r2_hidden('#skF_4',k1_wellord1('#skF_5','#skF_3'))
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_38,c_40,c_245])).

tff(c_262,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_46,c_260])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:25:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.32  
% 2.38/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.32  %$ r2_hidden > r1_tarski > v8_relat_2 > v6_relat_2 > v4_relat_2 > v2_wellord1 > v1_wellord1 > v1_relat_2 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.38/1.32  
% 2.38/1.32  %Foreground sorts:
% 2.38/1.32  
% 2.38/1.32  
% 2.38/1.32  %Background operators:
% 2.38/1.32  
% 2.38/1.32  
% 2.38/1.32  %Foreground operators:
% 2.38/1.32  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.38/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.38/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.38/1.32  tff(v1_relat_2, type, v1_relat_2: $i > $o).
% 2.38/1.32  tff(v8_relat_2, type, v8_relat_2: $i > $o).
% 2.38/1.32  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.38/1.32  tff(v6_relat_2, type, v6_relat_2: $i > $o).
% 2.38/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.32  tff(v4_relat_2, type, v4_relat_2: $i > $o).
% 2.38/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.38/1.32  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 2.38/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.38/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.38/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.38/1.32  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 2.38/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.32  tff(v1_wellord1, type, v1_wellord1: $i > $o).
% 2.38/1.32  
% 2.38/1.34  tff(f_103, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => ((((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) & (![D]: (r2_hidden(D, k1_wellord1(C, A)) => (r2_hidden(k4_tarski(D, B), C) & ~(D = B))))) => r2_hidden(k4_tarski(A, B), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_wellord1)).
% 2.38/1.34  tff(f_84, axiom, (![A, B, C]: (v1_relat_1(C) => (((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) => (r1_tarski(k1_wellord1(C, A), k1_wellord1(C, B)) <=> ((A = B) | r2_hidden(A, k1_wellord1(C, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_wellord1)).
% 2.38/1.34  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (((v2_wellord1(C) & r2_hidden(A, k3_relat_1(C))) & r2_hidden(B, k3_relat_1(C))) => (r2_hidden(k4_tarski(A, B), C) <=> r1_tarski(k1_wellord1(C, A), k1_wellord1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_wellord1)).
% 2.38/1.34  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) <=> ((((v1_relat_2(A) & v8_relat_2(A)) & v4_relat_2(A)) & v6_relat_2(A)) & v1_wellord1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_wellord1)).
% 2.38/1.34  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (v6_relat_2(A) <=> (![B, C]: ~((((r2_hidden(B, k3_relat_1(A)) & r2_hidden(C, k3_relat_1(A))) & ~(B = C)) & ~r2_hidden(k4_tarski(B, C), A)) & ~r2_hidden(k4_tarski(C, B), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l4_wellord1)).
% 2.38/1.34  tff(c_44, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.38/1.34  tff(c_42, plain, (v2_wellord1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.38/1.34  tff(c_38, plain, (r2_hidden('#skF_4', k3_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.38/1.34  tff(c_34, plain, (![C_14, B_13]: (r1_tarski(k1_wellord1(C_14, B_13), k1_wellord1(C_14, B_13)) | ~r2_hidden(B_13, k3_relat_1(C_14)) | ~v2_wellord1(C_14) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.38/1.34  tff(c_127, plain, (![A_40, B_41, C_42]: (r2_hidden(k4_tarski(A_40, B_41), C_42) | ~r1_tarski(k1_wellord1(C_42, A_40), k1_wellord1(C_42, B_41)) | ~r2_hidden(B_41, k3_relat_1(C_42)) | ~r2_hidden(A_40, k3_relat_1(C_42)) | ~v2_wellord1(C_42) | ~v1_relat_1(C_42))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.38/1.34  tff(c_192, plain, (![B_47, C_48]: (r2_hidden(k4_tarski(B_47, B_47), C_48) | ~r2_hidden(B_47, k3_relat_1(C_48)) | ~v2_wellord1(C_48) | ~v1_relat_1(C_48))), inference(resolution, [status(thm)], [c_34, c_127])).
% 2.38/1.34  tff(c_6, plain, (![A_1]: (v6_relat_2(A_1) | ~v2_wellord1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.38/1.34  tff(c_40, plain, (r2_hidden('#skF_3', k3_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.38/1.34  tff(c_100, plain, (![C_37, B_38, A_39]: (r2_hidden(k4_tarski(C_37, B_38), A_39) | r2_hidden(k4_tarski(B_38, C_37), A_39) | C_37=B_38 | ~r2_hidden(C_37, k3_relat_1(A_39)) | ~r2_hidden(B_38, k3_relat_1(A_39)) | ~v6_relat_2(A_39) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.38/1.34  tff(c_36, plain, (~r2_hidden(k4_tarski('#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.38/1.34  tff(c_109, plain, (r2_hidden(k4_tarski('#skF_4', '#skF_3'), '#skF_5') | '#skF_3'='#skF_4' | ~r2_hidden('#skF_3', k3_relat_1('#skF_5')) | ~r2_hidden('#skF_4', k3_relat_1('#skF_5')) | ~v6_relat_2('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_100, c_36])).
% 2.38/1.34  tff(c_122, plain, (r2_hidden(k4_tarski('#skF_4', '#skF_3'), '#skF_5') | '#skF_3'='#skF_4' | ~v6_relat_2('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_38, c_40, c_109])).
% 2.38/1.34  tff(c_140, plain, (~v6_relat_2('#skF_5')), inference(splitLeft, [status(thm)], [c_122])).
% 2.38/1.34  tff(c_146, plain, (~v2_wellord1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_6, c_140])).
% 2.38/1.34  tff(c_153, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_146])).
% 2.38/1.34  tff(c_155, plain, (v6_relat_2('#skF_5')), inference(splitRight, [status(thm)], [c_122])).
% 2.38/1.34  tff(c_118, plain, (r2_hidden(k4_tarski('#skF_4', '#skF_3'), '#skF_5') | '#skF_3'='#skF_4' | ~r2_hidden('#skF_4', k3_relat_1('#skF_5')) | ~r2_hidden('#skF_3', k3_relat_1('#skF_5')) | ~v6_relat_2('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_100, c_36])).
% 2.38/1.34  tff(c_126, plain, (r2_hidden(k4_tarski('#skF_4', '#skF_3'), '#skF_5') | '#skF_3'='#skF_4' | ~v6_relat_2('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_38, c_118])).
% 2.38/1.34  tff(c_157, plain, (r2_hidden(k4_tarski('#skF_4', '#skF_3'), '#skF_5') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_155, c_126])).
% 2.38/1.34  tff(c_158, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_157])).
% 2.38/1.34  tff(c_161, plain, (~r2_hidden(k4_tarski('#skF_4', '#skF_4'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_158, c_36])).
% 2.38/1.34  tff(c_195, plain, (~r2_hidden('#skF_4', k3_relat_1('#skF_5')) | ~v2_wellord1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_192, c_161])).
% 2.38/1.34  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_195])).
% 2.38/1.34  tff(c_201, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_157])).
% 2.38/1.34  tff(c_46, plain, (~r2_hidden('#skF_4', k1_wellord1('#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.38/1.34  tff(c_154, plain, ('#skF_3'='#skF_4' | r2_hidden(k4_tarski('#skF_4', '#skF_3'), '#skF_5')), inference(splitRight, [status(thm)], [c_122])).
% 2.38/1.34  tff(c_202, plain, (r2_hidden(k4_tarski('#skF_4', '#skF_3'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_201, c_154])).
% 2.38/1.34  tff(c_28, plain, (![C_11, A_9, B_10]: (r1_tarski(k1_wellord1(C_11, A_9), k1_wellord1(C_11, B_10)) | ~r2_hidden(k4_tarski(A_9, B_10), C_11) | ~r2_hidden(B_10, k3_relat_1(C_11)) | ~r2_hidden(A_9, k3_relat_1(C_11)) | ~v2_wellord1(C_11) | ~v1_relat_1(C_11))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.38/1.34  tff(c_222, plain, (![A_54, C_55, B_56]: (r2_hidden(A_54, k1_wellord1(C_55, B_56)) | B_56=A_54 | ~r1_tarski(k1_wellord1(C_55, A_54), k1_wellord1(C_55, B_56)) | ~r2_hidden(B_56, k3_relat_1(C_55)) | ~r2_hidden(A_54, k3_relat_1(C_55)) | ~v2_wellord1(C_55) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.38/1.34  tff(c_236, plain, (![A_57, C_58, B_59]: (r2_hidden(A_57, k1_wellord1(C_58, B_59)) | B_59=A_57 | ~r2_hidden(k4_tarski(A_57, B_59), C_58) | ~r2_hidden(B_59, k3_relat_1(C_58)) | ~r2_hidden(A_57, k3_relat_1(C_58)) | ~v2_wellord1(C_58) | ~v1_relat_1(C_58))), inference(resolution, [status(thm)], [c_28, c_222])).
% 2.38/1.34  tff(c_245, plain, (r2_hidden('#skF_4', k1_wellord1('#skF_5', '#skF_3')) | '#skF_3'='#skF_4' | ~r2_hidden('#skF_3', k3_relat_1('#skF_5')) | ~r2_hidden('#skF_4', k3_relat_1('#skF_5')) | ~v2_wellord1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_202, c_236])).
% 2.38/1.34  tff(c_260, plain, (r2_hidden('#skF_4', k1_wellord1('#skF_5', '#skF_3')) | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_38, c_40, c_245])).
% 2.38/1.34  tff(c_262, plain, $false, inference(negUnitSimplification, [status(thm)], [c_201, c_46, c_260])).
% 2.38/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.34  
% 2.38/1.34  Inference rules
% 2.38/1.34  ----------------------
% 2.38/1.34  #Ref     : 0
% 2.38/1.34  #Sup     : 32
% 2.38/1.34  #Fact    : 2
% 2.38/1.34  #Define  : 0
% 2.38/1.34  #Split   : 2
% 2.38/1.34  #Chain   : 0
% 2.38/1.34  #Close   : 0
% 2.38/1.34  
% 2.38/1.34  Ordering : KBO
% 2.38/1.34  
% 2.38/1.34  Simplification rules
% 2.38/1.34  ----------------------
% 2.38/1.34  #Subsume      : 4
% 2.38/1.34  #Demod        : 33
% 2.38/1.34  #Tautology    : 17
% 2.38/1.34  #SimpNegUnit  : 3
% 2.38/1.34  #BackRed      : 5
% 2.38/1.34  
% 2.38/1.34  #Partial instantiations: 0
% 2.38/1.34  #Strategies tried      : 1
% 2.38/1.34  
% 2.38/1.34  Timing (in seconds)
% 2.38/1.34  ----------------------
% 2.38/1.34  Preprocessing        : 0.33
% 2.38/1.34  Parsing              : 0.17
% 2.38/1.34  CNF conversion       : 0.02
% 2.38/1.34  Main loop            : 0.21
% 2.38/1.34  Inferencing          : 0.09
% 2.38/1.34  Reduction            : 0.06
% 2.38/1.34  Demodulation         : 0.04
% 2.38/1.34  BG Simplification    : 0.02
% 2.38/1.34  Subsumption          : 0.04
% 2.38/1.34  Abstraction          : 0.01
% 2.38/1.34  MUC search           : 0.00
% 2.38/1.34  Cooper               : 0.00
% 2.38/1.34  Total                : 0.58
% 2.38/1.34  Index Insertion      : 0.00
% 2.38/1.34  Index Deletion       : 0.00
% 2.38/1.34  Index Matching       : 0.00
% 2.38/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
