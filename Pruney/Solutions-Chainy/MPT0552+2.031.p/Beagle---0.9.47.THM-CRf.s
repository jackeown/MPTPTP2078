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
% DateTime   : Thu Dec  3 10:01:01 EST 2020

% Result     : Theorem 21.92s
% Output     : CNFRefutation 22.00s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 181 expanded)
%              Number of leaves         :   23 (  67 expanded)
%              Depth                    :    9
%              Number of atoms          :  116 ( 397 expanded)
%              Number of equality atoms :    8 (  32 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( v1_relat_1(k7_relat_1(A_15,B_16))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28795,plain,(
    ! [C_529,A_530,B_531] :
      ( k3_xboole_0(k7_relat_1(C_529,A_530),k7_relat_1(C_529,B_531)) = k7_relat_1(C_529,k3_xboole_0(A_530,B_531))
      | ~ v1_relat_1(C_529) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k3_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30314,plain,(
    ! [C_563,A_564,B_565,B_566] :
      ( r1_tarski(k7_relat_1(C_563,k3_xboole_0(A_564,B_565)),B_566)
      | ~ r1_tarski(k7_relat_1(C_563,A_564),B_566)
      | ~ v1_relat_1(C_563) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28795,c_10])).

tff(c_30394,plain,(
    ! [C_563,B_2,A_1,B_566] :
      ( r1_tarski(k7_relat_1(C_563,k3_xboole_0(B_2,A_1)),B_566)
      | ~ r1_tarski(k7_relat_1(C_563,A_1),B_566)
      | ~ v1_relat_1(C_563) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_30314])).

tff(c_24,plain,(
    ! [B_23,A_22] :
      ( k2_relat_1(k7_relat_1(B_23,A_22)) = k9_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_476,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(k2_relat_1(A_68),k2_relat_1(B_69))
      | ~ r1_tarski(A_68,B_69)
      | ~ v1_relat_1(B_69)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_32892,plain,(
    ! [A_621,B_622,A_623] :
      ( r1_tarski(k2_relat_1(A_621),k9_relat_1(B_622,A_623))
      | ~ r1_tarski(A_621,k7_relat_1(B_622,A_623))
      | ~ v1_relat_1(k7_relat_1(B_622,A_623))
      | ~ v1_relat_1(A_621)
      | ~ v1_relat_1(B_622) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_476])).

tff(c_56474,plain,(
    ! [B_980,A_981,B_982,A_983] :
      ( r1_tarski(k9_relat_1(B_980,A_981),k9_relat_1(B_982,A_983))
      | ~ r1_tarski(k7_relat_1(B_980,A_981),k7_relat_1(B_982,A_983))
      | ~ v1_relat_1(k7_relat_1(B_982,A_983))
      | ~ v1_relat_1(k7_relat_1(B_980,A_981))
      | ~ v1_relat_1(B_982)
      | ~ v1_relat_1(B_980) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_32892])).

tff(c_1025,plain,(
    ! [C_82,A_83,B_84] :
      ( k3_xboole_0(k7_relat_1(C_82,A_83),k7_relat_1(C_82,B_84)) = k7_relat_1(C_82,k3_xboole_0(A_83,B_84))
      | ~ v1_relat_1(C_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1071,plain,(
    ! [C_82,A_83,B_84,B_6] :
      ( r1_tarski(k7_relat_1(C_82,k3_xboole_0(A_83,B_84)),B_6)
      | ~ r1_tarski(k7_relat_1(C_82,A_83),B_6)
      | ~ v1_relat_1(C_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1025,c_10])).

tff(c_5149,plain,(
    ! [A_177,B_178,A_179] :
      ( r1_tarski(k2_relat_1(A_177),k9_relat_1(B_178,A_179))
      | ~ r1_tarski(A_177,k7_relat_1(B_178,A_179))
      | ~ v1_relat_1(k7_relat_1(B_178,A_179))
      | ~ v1_relat_1(A_177)
      | ~ v1_relat_1(B_178) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_476])).

tff(c_27791,plain,(
    ! [B_511,A_512,B_513,A_514] :
      ( r1_tarski(k9_relat_1(B_511,A_512),k9_relat_1(B_513,A_514))
      | ~ r1_tarski(k7_relat_1(B_511,A_512),k7_relat_1(B_513,A_514))
      | ~ v1_relat_1(k7_relat_1(B_513,A_514))
      | ~ v1_relat_1(k7_relat_1(B_511,A_512))
      | ~ v1_relat_1(B_513)
      | ~ v1_relat_1(B_511) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_5149])).

tff(c_191,plain,(
    ! [A_56,B_57,C_58] :
      ( r1_tarski(A_56,k3_xboole_0(B_57,C_58))
      | ~ r1_tarski(A_56,C_58)
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_218,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_191,c_30])).

tff(c_746,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_218])).

tff(c_27816,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_27791,c_746])).

tff(c_27838,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_27816])).

tff(c_28470,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_27838])).

tff(c_28473,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_28470])).

tff(c_28477,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28473])).

tff(c_28478,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_27838])).

tff(c_28480,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_28478])).

tff(c_28486,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1071,c_28480])).

tff(c_28496,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8,c_28486])).

tff(c_28497,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_28478])).

tff(c_28501,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_28497])).

tff(c_28505,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28501])).

tff(c_28506,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_218])).

tff(c_56520,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_56474,c_28506])).

tff(c_56565,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_56520])).

tff(c_57523,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_56565])).

tff(c_57526,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_57523])).

tff(c_57530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_57526])).

tff(c_57531,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_56565])).

tff(c_69579,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_57531])).

tff(c_69582,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_2'),k7_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30394,c_69579])).

tff(c_69592,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_8,c_69582])).

tff(c_69593,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_57531])).

tff(c_69597,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_69593])).

tff(c_69601,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_69597])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:52:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 21.92/11.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.92/11.49  
% 21.92/11.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 21.92/11.49  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 21.92/11.49  
% 21.92/11.49  %Foreground sorts:
% 21.92/11.49  
% 21.92/11.49  
% 21.92/11.49  %Background operators:
% 21.92/11.49  
% 21.92/11.49  
% 21.92/11.49  %Foreground operators:
% 21.92/11.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.92/11.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 21.92/11.49  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 21.92/11.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.92/11.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 21.92/11.49  tff('#skF_2', type, '#skF_2': $i).
% 21.92/11.49  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 21.92/11.49  tff('#skF_3', type, '#skF_3': $i).
% 21.92/11.49  tff('#skF_1', type, '#skF_1': $i).
% 21.92/11.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.92/11.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 21.92/11.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.92/11.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 21.92/11.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 21.92/11.49  
% 22.00/11.50  tff(f_79, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 22.00/11.50  tff(f_51, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 22.00/11.50  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 22.00/11.50  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 22.00/11.50  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_relat_1)).
% 22.00/11.50  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 22.00/11.50  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 22.00/11.50  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 22.00/11.50  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 22.00/11.50  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 22.00/11.50  tff(c_18, plain, (![A_15, B_16]: (v1_relat_1(k7_relat_1(A_15, B_16)) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 22.00/11.50  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 22.00/11.50  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 22.00/11.50  tff(c_28795, plain, (![C_529, A_530, B_531]: (k3_xboole_0(k7_relat_1(C_529, A_530), k7_relat_1(C_529, B_531))=k7_relat_1(C_529, k3_xboole_0(A_530, B_531)) | ~v1_relat_1(C_529))), inference(cnfTransformation, [status(thm)], [f_59])).
% 22.00/11.50  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(k3_xboole_0(A_5, C_7), B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 22.00/11.50  tff(c_30314, plain, (![C_563, A_564, B_565, B_566]: (r1_tarski(k7_relat_1(C_563, k3_xboole_0(A_564, B_565)), B_566) | ~r1_tarski(k7_relat_1(C_563, A_564), B_566) | ~v1_relat_1(C_563))), inference(superposition, [status(thm), theory('equality')], [c_28795, c_10])).
% 22.00/11.50  tff(c_30394, plain, (![C_563, B_2, A_1, B_566]: (r1_tarski(k7_relat_1(C_563, k3_xboole_0(B_2, A_1)), B_566) | ~r1_tarski(k7_relat_1(C_563, A_1), B_566) | ~v1_relat_1(C_563))), inference(superposition, [status(thm), theory('equality')], [c_2, c_30314])).
% 22.00/11.50  tff(c_24, plain, (![B_23, A_22]: (k2_relat_1(k7_relat_1(B_23, A_22))=k9_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 22.00/11.50  tff(c_476, plain, (![A_68, B_69]: (r1_tarski(k2_relat_1(A_68), k2_relat_1(B_69)) | ~r1_tarski(A_68, B_69) | ~v1_relat_1(B_69) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_74])).
% 22.00/11.50  tff(c_32892, plain, (![A_621, B_622, A_623]: (r1_tarski(k2_relat_1(A_621), k9_relat_1(B_622, A_623)) | ~r1_tarski(A_621, k7_relat_1(B_622, A_623)) | ~v1_relat_1(k7_relat_1(B_622, A_623)) | ~v1_relat_1(A_621) | ~v1_relat_1(B_622))), inference(superposition, [status(thm), theory('equality')], [c_24, c_476])).
% 22.00/11.50  tff(c_56474, plain, (![B_980, A_981, B_982, A_983]: (r1_tarski(k9_relat_1(B_980, A_981), k9_relat_1(B_982, A_983)) | ~r1_tarski(k7_relat_1(B_980, A_981), k7_relat_1(B_982, A_983)) | ~v1_relat_1(k7_relat_1(B_982, A_983)) | ~v1_relat_1(k7_relat_1(B_980, A_981)) | ~v1_relat_1(B_982) | ~v1_relat_1(B_980))), inference(superposition, [status(thm), theory('equality')], [c_24, c_32892])).
% 22.00/11.50  tff(c_1025, plain, (![C_82, A_83, B_84]: (k3_xboole_0(k7_relat_1(C_82, A_83), k7_relat_1(C_82, B_84))=k7_relat_1(C_82, k3_xboole_0(A_83, B_84)) | ~v1_relat_1(C_82))), inference(cnfTransformation, [status(thm)], [f_59])).
% 22.00/11.50  tff(c_1071, plain, (![C_82, A_83, B_84, B_6]: (r1_tarski(k7_relat_1(C_82, k3_xboole_0(A_83, B_84)), B_6) | ~r1_tarski(k7_relat_1(C_82, A_83), B_6) | ~v1_relat_1(C_82))), inference(superposition, [status(thm), theory('equality')], [c_1025, c_10])).
% 22.00/11.50  tff(c_5149, plain, (![A_177, B_178, A_179]: (r1_tarski(k2_relat_1(A_177), k9_relat_1(B_178, A_179)) | ~r1_tarski(A_177, k7_relat_1(B_178, A_179)) | ~v1_relat_1(k7_relat_1(B_178, A_179)) | ~v1_relat_1(A_177) | ~v1_relat_1(B_178))), inference(superposition, [status(thm), theory('equality')], [c_24, c_476])).
% 22.00/11.50  tff(c_27791, plain, (![B_511, A_512, B_513, A_514]: (r1_tarski(k9_relat_1(B_511, A_512), k9_relat_1(B_513, A_514)) | ~r1_tarski(k7_relat_1(B_511, A_512), k7_relat_1(B_513, A_514)) | ~v1_relat_1(k7_relat_1(B_513, A_514)) | ~v1_relat_1(k7_relat_1(B_511, A_512)) | ~v1_relat_1(B_513) | ~v1_relat_1(B_511))), inference(superposition, [status(thm), theory('equality')], [c_24, c_5149])).
% 22.00/11.50  tff(c_191, plain, (![A_56, B_57, C_58]: (r1_tarski(A_56, k3_xboole_0(B_57, C_58)) | ~r1_tarski(A_56, C_58) | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_45])).
% 22.00/11.50  tff(c_30, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 22.00/11.50  tff(c_218, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_191, c_30])).
% 22.00/11.50  tff(c_746, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_218])).
% 22.00/11.50  tff(c_27816, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_27791, c_746])).
% 22.00/11.50  tff(c_27838, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_27816])).
% 22.00/11.50  tff(c_28470, plain, (~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_27838])).
% 22.00/11.50  tff(c_28473, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_28470])).
% 22.00/11.50  tff(c_28477, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_28473])).
% 22.00/11.50  tff(c_28478, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_27838])).
% 22.00/11.50  tff(c_28480, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_28478])).
% 22.00/11.50  tff(c_28486, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1071, c_28480])).
% 22.00/11.50  tff(c_28496, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_8, c_28486])).
% 22.00/11.50  tff(c_28497, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_28478])).
% 22.00/11.50  tff(c_28501, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_28497])).
% 22.00/11.50  tff(c_28505, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_28501])).
% 22.00/11.50  tff(c_28506, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_218])).
% 22.00/11.50  tff(c_56520, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_56474, c_28506])).
% 22.00/11.50  tff(c_56565, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_56520])).
% 22.00/11.50  tff(c_57523, plain, (~v1_relat_1(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_56565])).
% 22.00/11.50  tff(c_57526, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_57523])).
% 22.00/11.50  tff(c_57530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_57526])).
% 22.00/11.50  tff(c_57531, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_56565])).
% 22.00/11.50  tff(c_69579, plain, (~r1_tarski(k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k7_relat_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_57531])).
% 22.00/11.50  tff(c_69582, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_2'), k7_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30394, c_69579])).
% 22.00/11.50  tff(c_69592, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_8, c_69582])).
% 22.00/11.50  tff(c_69593, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_57531])).
% 22.00/11.50  tff(c_69597, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_69593])).
% 22.00/11.50  tff(c_69601, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_69597])).
% 22.00/11.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.00/11.50  
% 22.00/11.50  Inference rules
% 22.00/11.50  ----------------------
% 22.00/11.50  #Ref     : 0
% 22.00/11.50  #Sup     : 18871
% 22.00/11.50  #Fact    : 0
% 22.00/11.50  #Define  : 0
% 22.00/11.50  #Split   : 7
% 22.00/11.50  #Chain   : 0
% 22.00/11.50  #Close   : 0
% 22.00/11.50  
% 22.00/11.50  Ordering : KBO
% 22.00/11.50  
% 22.00/11.50  Simplification rules
% 22.00/11.50  ----------------------
% 22.00/11.50  #Subsume      : 4660
% 22.00/11.50  #Demod        : 7570
% 22.00/11.50  #Tautology    : 3816
% 22.00/11.50  #SimpNegUnit  : 0
% 22.00/11.50  #BackRed      : 0
% 22.00/11.50  
% 22.00/11.50  #Partial instantiations: 0
% 22.00/11.50  #Strategies tried      : 1
% 22.00/11.50  
% 22.00/11.50  Timing (in seconds)
% 22.00/11.50  ----------------------
% 22.32/11.54  Preprocessing        : 0.27
% 22.32/11.54  Parsing              : 0.15
% 22.32/11.54  CNF conversion       : 0.02
% 22.32/11.54  Main loop            : 10.44
% 22.32/11.54  Inferencing          : 1.39
% 22.32/11.54  Reduction            : 4.69
% 22.32/11.54  Demodulation         : 4.19
% 22.32/11.54  BG Simplification    : 0.23
% 22.32/11.54  Subsumption          : 3.57
% 22.32/11.54  Abstraction          : 0.36
% 22.32/11.54  MUC search           : 0.00
% 22.32/11.54  Cooper               : 0.00
% 22.32/11.54  Total                : 10.74
% 22.32/11.54  Index Insertion      : 0.00
% 22.32/11.54  Index Deletion       : 0.00
% 22.32/11.54  Index Matching       : 0.00
% 22.32/11.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
