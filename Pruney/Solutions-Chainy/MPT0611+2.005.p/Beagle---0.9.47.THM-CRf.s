%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:40 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 139 expanded)
%              Number of leaves         :   28 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :  105 ( 304 expanded)
%              Number of equality atoms :   23 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_117,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k2_relat_1(A),k2_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t215_relat_1)).

tff(f_99,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_107,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_58,plain,(
    ! [A_38,B_39] :
      ( r1_xboole_0(A_38,B_39)
      | k3_xboole_0(A_38,B_39) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_65,plain,(
    k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_42])).

tff(c_48,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_46,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_44,plain,(
    r1_xboole_0(k2_relat_1('#skF_3'),k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_66,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    k3_xboole_0(k2_relat_1('#skF_3'),k2_relat_1('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_66])).

tff(c_631,plain,(
    ! [A_98,B_99] :
      ( r1_tarski(k2_relat_1(k3_xboole_0(A_98,B_99)),k3_xboole_0(k2_relat_1(A_98),k2_relat_1(B_99)))
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_676,plain,
    ( r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_631])).

tff(c_680,plain,(
    r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_676])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_1'(A_5,B_6),B_6)
      | r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_50,plain,(
    ! [B_36,A_37] :
      ( r1_xboole_0(B_36,A_37)
      | ~ r1_xboole_0(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_53,plain,(
    r1_xboole_0(k2_relat_1('#skF_4'),k2_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_50])).

tff(c_274,plain,(
    ! [B_65,A_66] :
      ( k10_relat_1(B_65,A_66) = k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(B_65),A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_294,plain,
    ( k10_relat_1('#skF_4',k2_relat_1('#skF_3')) = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_53,c_274])).

tff(c_303,plain,(
    k10_relat_1('#skF_4',k2_relat_1('#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_294])).

tff(c_1114,plain,(
    ! [A_136,B_137,C_138] :
      ( r2_hidden('#skF_2'(A_136,B_137,C_138),k2_relat_1(C_138))
      | ~ r2_hidden(A_136,k10_relat_1(C_138,B_137))
      | ~ v1_relat_1(C_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_416,plain,(
    ! [A_82,B_83,C_84] :
      ( r2_hidden('#skF_2'(A_82,B_83,C_84),B_83)
      | ~ r2_hidden(A_82,k10_relat_1(C_84,B_83))
      | ~ v1_relat_1(C_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_150,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,B_57)
      | ~ r2_hidden(C_58,A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_162,plain,(
    ! [C_58] :
      ( ~ r2_hidden(C_58,k2_relat_1('#skF_4'))
      | ~ r2_hidden(C_58,k2_relat_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_44,c_150])).

tff(c_427,plain,(
    ! [A_82,C_84] :
      ( ~ r2_hidden('#skF_2'(A_82,k2_relat_1('#skF_3'),C_84),k2_relat_1('#skF_4'))
      | ~ r2_hidden(A_82,k10_relat_1(C_84,k2_relat_1('#skF_3')))
      | ~ v1_relat_1(C_84) ) ),
    inference(resolution,[status(thm)],[c_416,c_162])).

tff(c_1118,plain,(
    ! [A_136] :
      ( ~ r2_hidden(A_136,k10_relat_1('#skF_4',k2_relat_1('#skF_3')))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1114,c_427])).

tff(c_1141,plain,(
    ! [A_139] : ~ r2_hidden(A_139,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_303,c_1118])).

tff(c_1171,plain,(
    ! [A_141] : r1_xboole_0(A_141,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_1141])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( k1_xboole_0 = A_10
      | ~ r1_xboole_0(B_11,C_12)
      | ~ r1_tarski(A_10,C_12)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1902,plain,(
    ! [A_177,A_178] :
      ( k1_xboole_0 = A_177
      | ~ r1_tarski(A_177,k1_xboole_0)
      | ~ r1_tarski(A_177,A_178) ) ),
    inference(resolution,[status(thm)],[c_1171,c_14])).

tff(c_1915,plain,(
    ! [A_178] :
      ( k2_relat_1(k3_xboole_0('#skF_3','#skF_4')) = k1_xboole_0
      | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),A_178) ) ),
    inference(resolution,[status(thm)],[c_680,c_1902])).

tff(c_2139,plain,(
    ! [A_178] : ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_3','#skF_4')),A_178) ),
    inference(splitLeft,[status(thm)],[c_1915])).

tff(c_2141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2139,c_680])).

tff(c_2142,plain,(
    k2_relat_1(k3_xboole_0('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1915])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k3_xboole_0(A_13,B_14))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_110,plain,(
    ! [A_43] :
      ( k2_relat_1(A_43) != k1_xboole_0
      | k1_xboole_0 = A_43
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_120,plain,(
    ! [A_13,B_14] :
      ( k2_relat_1(k3_xboole_0(A_13,B_14)) != k1_xboole_0
      | k3_xboole_0(A_13,B_14) = k1_xboole_0
      | ~ v1_relat_1(A_13) ) ),
    inference(resolution,[status(thm)],[c_16,c_110])).

tff(c_2168,plain,
    ( k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2142,c_120])).

tff(c_2204,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2168])).

tff(c_2206,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_2204])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:48:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.83/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.64  
% 3.83/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.64  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k8_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 3.83/1.64  
% 3.83/1.64  %Foreground sorts:
% 3.83/1.64  
% 3.83/1.64  
% 3.83/1.64  %Background operators:
% 3.83/1.64  
% 3.83/1.64  
% 3.83/1.64  %Foreground operators:
% 3.83/1.64  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.83/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.83/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.83/1.64  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.83/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.83/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.83/1.64  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.83/1.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.83/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.83/1.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.83/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.83/1.64  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.83/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.83/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.83/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.83/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.83/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.83/1.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.83/1.64  
% 3.83/1.66  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.83/1.66  tff(f_117, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k2_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t215_relat_1)).
% 3.83/1.66  tff(f_99, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_relat_1)).
% 3.83/1.66  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.83/1.66  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.83/1.66  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 3.83/1.66  tff(f_86, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 3.83/1.66  tff(f_59, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 3.83/1.66  tff(f_63, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 3.83/1.66  tff(f_107, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.83/1.66  tff(c_58, plain, (![A_38, B_39]: (r1_xboole_0(A_38, B_39) | k3_xboole_0(A_38, B_39)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.83/1.66  tff(c_42, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.83/1.66  tff(c_65, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_42])).
% 3.83/1.66  tff(c_48, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.83/1.66  tff(c_46, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.83/1.66  tff(c_44, plain, (r1_xboole_0(k2_relat_1('#skF_3'), k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.83/1.66  tff(c_66, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=k1_xboole_0 | ~r1_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.83/1.66  tff(c_78, plain, (k3_xboole_0(k2_relat_1('#skF_3'), k2_relat_1('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_66])).
% 3.83/1.66  tff(c_631, plain, (![A_98, B_99]: (r1_tarski(k2_relat_1(k3_xboole_0(A_98, B_99)), k3_xboole_0(k2_relat_1(A_98), k2_relat_1(B_99))) | ~v1_relat_1(B_99) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.83/1.66  tff(c_676, plain, (r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k1_xboole_0) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_78, c_631])).
% 3.83/1.66  tff(c_680, plain, (r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_676])).
% 3.83/1.66  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_1'(A_5, B_6), B_6) | r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.83/1.66  tff(c_50, plain, (![B_36, A_37]: (r1_xboole_0(B_36, A_37) | ~r1_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.83/1.66  tff(c_53, plain, (r1_xboole_0(k2_relat_1('#skF_4'), k2_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_44, c_50])).
% 3.83/1.66  tff(c_274, plain, (![B_65, A_66]: (k10_relat_1(B_65, A_66)=k1_xboole_0 | ~r1_xboole_0(k2_relat_1(B_65), A_66) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.83/1.66  tff(c_294, plain, (k10_relat_1('#skF_4', k2_relat_1('#skF_3'))=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_53, c_274])).
% 3.83/1.66  tff(c_303, plain, (k10_relat_1('#skF_4', k2_relat_1('#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_294])).
% 3.83/1.66  tff(c_1114, plain, (![A_136, B_137, C_138]: (r2_hidden('#skF_2'(A_136, B_137, C_138), k2_relat_1(C_138)) | ~r2_hidden(A_136, k10_relat_1(C_138, B_137)) | ~v1_relat_1(C_138))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.83/1.66  tff(c_416, plain, (![A_82, B_83, C_84]: (r2_hidden('#skF_2'(A_82, B_83, C_84), B_83) | ~r2_hidden(A_82, k10_relat_1(C_84, B_83)) | ~v1_relat_1(C_84))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.83/1.66  tff(c_150, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, B_57) | ~r2_hidden(C_58, A_56))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.83/1.66  tff(c_162, plain, (![C_58]: (~r2_hidden(C_58, k2_relat_1('#skF_4')) | ~r2_hidden(C_58, k2_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_44, c_150])).
% 3.83/1.66  tff(c_427, plain, (![A_82, C_84]: (~r2_hidden('#skF_2'(A_82, k2_relat_1('#skF_3'), C_84), k2_relat_1('#skF_4')) | ~r2_hidden(A_82, k10_relat_1(C_84, k2_relat_1('#skF_3'))) | ~v1_relat_1(C_84))), inference(resolution, [status(thm)], [c_416, c_162])).
% 3.83/1.66  tff(c_1118, plain, (![A_136]: (~r2_hidden(A_136, k10_relat_1('#skF_4', k2_relat_1('#skF_3'))) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_1114, c_427])).
% 3.83/1.66  tff(c_1141, plain, (![A_139]: (~r2_hidden(A_139, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_303, c_1118])).
% 3.83/1.66  tff(c_1171, plain, (![A_141]: (r1_xboole_0(A_141, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_1141])).
% 3.83/1.66  tff(c_14, plain, (![A_10, B_11, C_12]: (k1_xboole_0=A_10 | ~r1_xboole_0(B_11, C_12) | ~r1_tarski(A_10, C_12) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.83/1.66  tff(c_1902, plain, (![A_177, A_178]: (k1_xboole_0=A_177 | ~r1_tarski(A_177, k1_xboole_0) | ~r1_tarski(A_177, A_178))), inference(resolution, [status(thm)], [c_1171, c_14])).
% 3.83/1.66  tff(c_1915, plain, (![A_178]: (k2_relat_1(k3_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0 | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), A_178))), inference(resolution, [status(thm)], [c_680, c_1902])).
% 3.83/1.66  tff(c_2139, plain, (![A_178]: (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_3', '#skF_4')), A_178))), inference(splitLeft, [status(thm)], [c_1915])).
% 3.83/1.66  tff(c_2141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2139, c_680])).
% 3.83/1.66  tff(c_2142, plain, (k2_relat_1(k3_xboole_0('#skF_3', '#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_1915])).
% 3.83/1.66  tff(c_16, plain, (![A_13, B_14]: (v1_relat_1(k3_xboole_0(A_13, B_14)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.83/1.66  tff(c_110, plain, (![A_43]: (k2_relat_1(A_43)!=k1_xboole_0 | k1_xboole_0=A_43 | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.83/1.66  tff(c_120, plain, (![A_13, B_14]: (k2_relat_1(k3_xboole_0(A_13, B_14))!=k1_xboole_0 | k3_xboole_0(A_13, B_14)=k1_xboole_0 | ~v1_relat_1(A_13))), inference(resolution, [status(thm)], [c_16, c_110])).
% 3.83/1.66  tff(c_2168, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2142, c_120])).
% 3.83/1.66  tff(c_2204, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2168])).
% 3.83/1.66  tff(c_2206, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_2204])).
% 3.83/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.83/1.66  
% 3.83/1.66  Inference rules
% 3.83/1.66  ----------------------
% 3.83/1.66  #Ref     : 0
% 3.83/1.66  #Sup     : 524
% 3.83/1.66  #Fact    : 0
% 3.83/1.66  #Define  : 0
% 3.83/1.66  #Split   : 11
% 3.83/1.66  #Chain   : 0
% 3.83/1.66  #Close   : 0
% 3.83/1.66  
% 3.83/1.66  Ordering : KBO
% 3.83/1.66  
% 3.83/1.66  Simplification rules
% 3.83/1.66  ----------------------
% 3.83/1.66  #Subsume      : 80
% 3.83/1.66  #Demod        : 198
% 3.83/1.66  #Tautology    : 205
% 3.83/1.66  #SimpNegUnit  : 9
% 3.83/1.66  #BackRed      : 4
% 3.83/1.66  
% 3.83/1.66  #Partial instantiations: 0
% 3.83/1.66  #Strategies tried      : 1
% 3.83/1.66  
% 3.83/1.66  Timing (in seconds)
% 3.83/1.66  ----------------------
% 3.83/1.66  Preprocessing        : 0.31
% 3.83/1.66  Parsing              : 0.17
% 3.83/1.66  CNF conversion       : 0.02
% 3.83/1.66  Main loop            : 0.57
% 3.83/1.66  Inferencing          : 0.20
% 3.83/1.66  Reduction            : 0.18
% 3.83/1.66  Demodulation         : 0.12
% 3.83/1.66  BG Simplification    : 0.03
% 3.83/1.66  Subsumption          : 0.13
% 3.83/1.66  Abstraction          : 0.03
% 3.83/1.66  MUC search           : 0.00
% 3.83/1.66  Cooper               : 0.00
% 3.83/1.66  Total                : 0.92
% 3.83/1.66  Index Insertion      : 0.00
% 3.83/1.66  Index Deletion       : 0.00
% 3.83/1.66  Index Matching       : 0.00
% 3.83/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
