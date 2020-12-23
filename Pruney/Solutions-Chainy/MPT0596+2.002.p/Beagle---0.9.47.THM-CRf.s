%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:11 EST 2020

% Result     : Theorem 4.78s
% Output     : CNFRefutation 4.95s
% Verified   : 
% Statistics : Number of formulae       :   56 (  69 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :   98 ( 137 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ! [C] :
            ( v1_relat_1(C)
           => ( r1_tarski(k2_relat_1(B),k1_relat_1(k7_relat_1(C,A)))
             => k5_relat_1(B,k7_relat_1(C,A)) = k5_relat_1(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_34,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_30,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_33,plain,(
    ! [A_27,B_28] :
      ( ~ r2_hidden('#skF_1'(A_27,B_28),B_28)
      | r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_38,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_33])).

tff(c_26,plain,(
    r1_tarski(k2_relat_1('#skF_3'),k1_relat_1(k7_relat_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_49,plain,(
    ! [C_32,B_33,A_34] :
      ( r2_hidden(C_32,B_33)
      | ~ r2_hidden(C_32,A_34)
      | ~ r1_tarski(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_159,plain,(
    ! [A_51,B_52,B_53] :
      ( r2_hidden('#skF_1'(A_51,B_52),B_53)
      | ~ r1_tarski(A_51,B_53)
      | r1_tarski(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_6,c_49])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_303,plain,(
    ! [A_73,B_74,B_75,B_76] :
      ( r2_hidden('#skF_1'(A_73,B_74),B_75)
      | ~ r1_tarski(B_76,B_75)
      | ~ r1_tarski(A_73,B_76)
      | r1_tarski(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_159,c_2])).

tff(c_484,plain,(
    ! [A_93,B_94] :
      ( r2_hidden('#skF_1'(A_93,B_94),k1_relat_1(k7_relat_1('#skF_4','#skF_2')))
      | ~ r1_tarski(A_93,k2_relat_1('#skF_3'))
      | r1_tarski(A_93,B_94) ) ),
    inference(resolution,[status(thm)],[c_26,c_303])).

tff(c_20,plain,(
    ! [A_18,B_19,C_20] :
      ( r2_hidden(A_18,B_19)
      | ~ r2_hidden(A_18,k1_relat_1(k7_relat_1(C_20,B_19)))
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_490,plain,(
    ! [A_93,B_94] :
      ( r2_hidden('#skF_1'(A_93,B_94),'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(A_93,k2_relat_1('#skF_3'))
      | r1_tarski(A_93,B_94) ) ),
    inference(resolution,[status(thm)],[c_484,c_20])).

tff(c_518,plain,(
    ! [A_96,B_97] :
      ( r2_hidden('#skF_1'(A_96,B_97),'#skF_2')
      | ~ r1_tarski(A_96,k2_relat_1('#skF_3'))
      | r1_tarski(A_96,B_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_490])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_527,plain,(
    ! [A_98] :
      ( ~ r1_tarski(A_98,k2_relat_1('#skF_3'))
      | r1_tarski(A_98,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_518,c_4])).

tff(c_537,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_527])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k8_relat_1(A_9,B_10) = B_10
      | ~ r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_542,plain,
    ( k8_relat_1('#skF_2','#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_537,c_12])).

tff(c_546,plain,(
    k8_relat_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_542])).

tff(c_22,plain,(
    ! [A_21,B_22] :
      ( k5_relat_1(k6_relat_1(A_21),B_22) = k7_relat_1(B_22,A_21)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_6] : v1_relat_1(k6_relat_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( k5_relat_1(B_8,k6_relat_1(A_7)) = k8_relat_1(A_7,B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_266,plain,(
    ! [A_70,B_71,C_72] :
      ( k5_relat_1(k5_relat_1(A_70,B_71),C_72) = k5_relat_1(A_70,k5_relat_1(B_71,C_72))
      | ~ v1_relat_1(C_72)
      | ~ v1_relat_1(B_71)
      | ~ v1_relat_1(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_288,plain,(
    ! [B_8,A_7,C_72] :
      ( k5_relat_1(B_8,k5_relat_1(k6_relat_1(A_7),C_72)) = k5_relat_1(k8_relat_1(A_7,B_8),C_72)
      | ~ v1_relat_1(C_72)
      | ~ v1_relat_1(k6_relat_1(A_7))
      | ~ v1_relat_1(B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_266])).

tff(c_355,plain,(
    ! [B_83,A_84,C_85] :
      ( k5_relat_1(B_83,k5_relat_1(k6_relat_1(A_84),C_85)) = k5_relat_1(k8_relat_1(A_84,B_83),C_85)
      | ~ v1_relat_1(C_85)
      | ~ v1_relat_1(B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_288])).

tff(c_2861,plain,(
    ! [A_232,B_233,B_234] :
      ( k5_relat_1(k8_relat_1(A_232,B_233),B_234) = k5_relat_1(B_233,k7_relat_1(B_234,A_232))
      | ~ v1_relat_1(B_234)
      | ~ v1_relat_1(B_233)
      | ~ v1_relat_1(B_234) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_355])).

tff(c_2927,plain,(
    ! [B_234] :
      ( k5_relat_1('#skF_3',k7_relat_1(B_234,'#skF_2')) = k5_relat_1('#skF_3',B_234)
      | ~ v1_relat_1(B_234)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(B_234) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_2861])).

tff(c_2976,plain,(
    ! [B_235] :
      ( k5_relat_1('#skF_3',k7_relat_1(B_235,'#skF_2')) = k5_relat_1('#skF_3',B_235)
      | ~ v1_relat_1(B_235) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2927])).

tff(c_24,plain,(
    k5_relat_1('#skF_3',k7_relat_1('#skF_4','#skF_2')) != k5_relat_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2994,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2976,c_24])).

tff(c_3018,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2994])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.78/1.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.95/1.91  
% 4.95/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.95/1.92  %$ r2_hidden > r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.95/1.92  
% 4.95/1.92  %Foreground sorts:
% 4.95/1.92  
% 4.95/1.92  
% 4.95/1.92  %Background operators:
% 4.95/1.92  
% 4.95/1.92  
% 4.95/1.92  %Foreground operators:
% 4.95/1.92  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 4.95/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.95/1.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.95/1.92  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.95/1.92  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.95/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.95/1.92  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.95/1.92  tff('#skF_2', type, '#skF_2': $i).
% 4.95/1.92  tff('#skF_3', type, '#skF_3': $i).
% 4.95/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.95/1.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.95/1.92  tff('#skF_4', type, '#skF_4': $i).
% 4.95/1.92  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.95/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.95/1.92  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.95/1.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.95/1.92  
% 4.95/1.93  tff(f_76, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(k2_relat_1(B), k1_relat_1(k7_relat_1(C, A))) => (k5_relat_1(B, k7_relat_1(C, A)) = k5_relat_1(B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t200_relat_1)).
% 4.95/1.93  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.95/1.93  tff(f_62, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_relat_1)).
% 4.95/1.93  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 4.95/1.93  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 4.95/1.93  tff(f_34, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 4.95/1.93  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 4.95/1.93  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 4.95/1.93  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.95/1.93  tff(c_30, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.95/1.93  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.95/1.93  tff(c_33, plain, (![A_27, B_28]: (~r2_hidden('#skF_1'(A_27, B_28), B_28) | r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.95/1.93  tff(c_38, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_33])).
% 4.95/1.93  tff(c_26, plain, (r1_tarski(k2_relat_1('#skF_3'), k1_relat_1(k7_relat_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.95/1.93  tff(c_49, plain, (![C_32, B_33, A_34]: (r2_hidden(C_32, B_33) | ~r2_hidden(C_32, A_34) | ~r1_tarski(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.95/1.93  tff(c_159, plain, (![A_51, B_52, B_53]: (r2_hidden('#skF_1'(A_51, B_52), B_53) | ~r1_tarski(A_51, B_53) | r1_tarski(A_51, B_52))), inference(resolution, [status(thm)], [c_6, c_49])).
% 4.95/1.93  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.95/1.93  tff(c_303, plain, (![A_73, B_74, B_75, B_76]: (r2_hidden('#skF_1'(A_73, B_74), B_75) | ~r1_tarski(B_76, B_75) | ~r1_tarski(A_73, B_76) | r1_tarski(A_73, B_74))), inference(resolution, [status(thm)], [c_159, c_2])).
% 4.95/1.93  tff(c_484, plain, (![A_93, B_94]: (r2_hidden('#skF_1'(A_93, B_94), k1_relat_1(k7_relat_1('#skF_4', '#skF_2'))) | ~r1_tarski(A_93, k2_relat_1('#skF_3')) | r1_tarski(A_93, B_94))), inference(resolution, [status(thm)], [c_26, c_303])).
% 4.95/1.93  tff(c_20, plain, (![A_18, B_19, C_20]: (r2_hidden(A_18, B_19) | ~r2_hidden(A_18, k1_relat_1(k7_relat_1(C_20, B_19))) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.95/1.93  tff(c_490, plain, (![A_93, B_94]: (r2_hidden('#skF_1'(A_93, B_94), '#skF_2') | ~v1_relat_1('#skF_4') | ~r1_tarski(A_93, k2_relat_1('#skF_3')) | r1_tarski(A_93, B_94))), inference(resolution, [status(thm)], [c_484, c_20])).
% 4.95/1.93  tff(c_518, plain, (![A_96, B_97]: (r2_hidden('#skF_1'(A_96, B_97), '#skF_2') | ~r1_tarski(A_96, k2_relat_1('#skF_3')) | r1_tarski(A_96, B_97))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_490])).
% 4.95/1.93  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.95/1.93  tff(c_527, plain, (![A_98]: (~r1_tarski(A_98, k2_relat_1('#skF_3')) | r1_tarski(A_98, '#skF_2'))), inference(resolution, [status(thm)], [c_518, c_4])).
% 4.95/1.93  tff(c_537, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_38, c_527])).
% 4.95/1.93  tff(c_12, plain, (![A_9, B_10]: (k8_relat_1(A_9, B_10)=B_10 | ~r1_tarski(k2_relat_1(B_10), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.95/1.93  tff(c_542, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_537, c_12])).
% 4.95/1.93  tff(c_546, plain, (k8_relat_1('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_542])).
% 4.95/1.93  tff(c_22, plain, (![A_21, B_22]: (k5_relat_1(k6_relat_1(A_21), B_22)=k7_relat_1(B_22, A_21) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.95/1.93  tff(c_8, plain, (![A_6]: (v1_relat_1(k6_relat_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.95/1.93  tff(c_10, plain, (![B_8, A_7]: (k5_relat_1(B_8, k6_relat_1(A_7))=k8_relat_1(A_7, B_8) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.95/1.93  tff(c_266, plain, (![A_70, B_71, C_72]: (k5_relat_1(k5_relat_1(A_70, B_71), C_72)=k5_relat_1(A_70, k5_relat_1(B_71, C_72)) | ~v1_relat_1(C_72) | ~v1_relat_1(B_71) | ~v1_relat_1(A_70))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.95/1.93  tff(c_288, plain, (![B_8, A_7, C_72]: (k5_relat_1(B_8, k5_relat_1(k6_relat_1(A_7), C_72))=k5_relat_1(k8_relat_1(A_7, B_8), C_72) | ~v1_relat_1(C_72) | ~v1_relat_1(k6_relat_1(A_7)) | ~v1_relat_1(B_8) | ~v1_relat_1(B_8))), inference(superposition, [status(thm), theory('equality')], [c_10, c_266])).
% 4.95/1.93  tff(c_355, plain, (![B_83, A_84, C_85]: (k5_relat_1(B_83, k5_relat_1(k6_relat_1(A_84), C_85))=k5_relat_1(k8_relat_1(A_84, B_83), C_85) | ~v1_relat_1(C_85) | ~v1_relat_1(B_83))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_288])).
% 4.95/1.93  tff(c_2861, plain, (![A_232, B_233, B_234]: (k5_relat_1(k8_relat_1(A_232, B_233), B_234)=k5_relat_1(B_233, k7_relat_1(B_234, A_232)) | ~v1_relat_1(B_234) | ~v1_relat_1(B_233) | ~v1_relat_1(B_234))), inference(superposition, [status(thm), theory('equality')], [c_22, c_355])).
% 4.95/1.93  tff(c_2927, plain, (![B_234]: (k5_relat_1('#skF_3', k7_relat_1(B_234, '#skF_2'))=k5_relat_1('#skF_3', B_234) | ~v1_relat_1(B_234) | ~v1_relat_1('#skF_3') | ~v1_relat_1(B_234))), inference(superposition, [status(thm), theory('equality')], [c_546, c_2861])).
% 4.95/1.93  tff(c_2976, plain, (![B_235]: (k5_relat_1('#skF_3', k7_relat_1(B_235, '#skF_2'))=k5_relat_1('#skF_3', B_235) | ~v1_relat_1(B_235))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2927])).
% 4.95/1.93  tff(c_24, plain, (k5_relat_1('#skF_3', k7_relat_1('#skF_4', '#skF_2'))!=k5_relat_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.95/1.93  tff(c_2994, plain, (~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2976, c_24])).
% 4.95/1.93  tff(c_3018, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_2994])).
% 4.95/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.95/1.93  
% 4.95/1.93  Inference rules
% 4.95/1.93  ----------------------
% 4.95/1.93  #Ref     : 0
% 4.95/1.93  #Sup     : 666
% 4.95/1.93  #Fact    : 0
% 4.95/1.93  #Define  : 0
% 4.95/1.93  #Split   : 2
% 4.95/1.93  #Chain   : 0
% 4.95/1.93  #Close   : 0
% 4.95/1.93  
% 4.95/1.93  Ordering : KBO
% 4.95/1.93  
% 4.95/1.93  Simplification rules
% 4.95/1.93  ----------------------
% 4.95/1.93  #Subsume      : 61
% 4.95/1.93  #Demod        : 310
% 4.95/1.93  #Tautology    : 119
% 4.95/1.93  #SimpNegUnit  : 0
% 4.95/1.93  #BackRed      : 0
% 4.95/1.93  
% 4.95/1.93  #Partial instantiations: 0
% 4.95/1.93  #Strategies tried      : 1
% 4.95/1.93  
% 4.95/1.93  Timing (in seconds)
% 4.95/1.93  ----------------------
% 4.95/1.93  Preprocessing        : 0.28
% 4.95/1.93  Parsing              : 0.16
% 4.95/1.93  CNF conversion       : 0.02
% 4.95/1.93  Main loop            : 0.89
% 4.95/1.93  Inferencing          : 0.32
% 4.95/1.93  Reduction            : 0.29
% 4.95/1.93  Demodulation         : 0.21
% 4.95/1.93  BG Simplification    : 0.04
% 4.95/1.93  Subsumption          : 0.19
% 4.95/1.93  Abstraction          : 0.05
% 4.95/1.93  MUC search           : 0.00
% 4.95/1.93  Cooper               : 0.00
% 4.95/1.93  Total                : 1.19
% 4.95/1.93  Index Insertion      : 0.00
% 4.95/1.93  Index Deletion       : 0.00
% 4.95/1.93  Index Matching       : 0.00
% 4.95/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
