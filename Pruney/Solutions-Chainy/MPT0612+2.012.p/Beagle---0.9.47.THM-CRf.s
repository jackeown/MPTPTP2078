%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:43 EST 2020

% Result     : Theorem 11.01s
% Output     : CNFRefutation 11.14s
% Verified   : 
% Statistics : Number of formulae       :   52 (  65 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   84 ( 117 expanded)
%              Number of equality atoms :   14 (  22 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_56,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k6_subset_1(C,k7_relat_1(C,B)),A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(k1_relat_1(C),A)
       => k6_subset_1(C,k7_relat_1(C,B)) = k7_relat_1(C,k6_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t211_relat_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_xboole_0(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(c_18,plain,(
    ! [B_12] : r1_tarski(B_12,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_34,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_32,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_82,plain,(
    ! [C_45,B_46,A_47] :
      ( r2_hidden(C_45,B_46)
      | ~ r2_hidden(C_45,A_47)
      | ~ r1_tarski(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_213,plain,(
    ! [A_82,B_83,B_84] :
      ( r2_hidden('#skF_2'(A_82,B_83),B_84)
      | ~ r1_tarski(B_83,B_84)
      | r1_xboole_0(A_82,B_83) ) ),
    inference(resolution,[status(thm)],[c_10,c_82])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1915,plain,(
    ! [A_210,B_211,B_212,B_213] :
      ( r2_hidden('#skF_2'(A_210,B_211),B_212)
      | ~ r1_tarski(B_213,B_212)
      | ~ r1_tarski(B_211,B_213)
      | r1_xboole_0(A_210,B_211) ) ),
    inference(resolution,[status(thm)],[c_213,c_2])).

tff(c_2009,plain,(
    ! [A_218,B_219] :
      ( r2_hidden('#skF_2'(A_218,B_219),'#skF_4')
      | ~ r1_tarski(B_219,'#skF_3')
      | r1_xboole_0(A_218,B_219) ) ),
    inference(resolution,[status(thm)],[c_32,c_1915])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_49,plain,(
    ! [A_29,C_30,B_31] :
      ( r1_xboole_0(A_29,C_30)
      | ~ r1_tarski(A_29,k4_xboole_0(B_31,C_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_54,plain,(
    ! [B_31,C_30] : r1_xboole_0(k4_xboole_0(B_31,C_30),C_30) ),
    inference(resolution,[status(thm)],[c_18,c_49])).

tff(c_121,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r2_hidden(C_58,B_57)
      | ~ r2_hidden(C_58,A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_128,plain,(
    ! [C_59,C_60,B_61] :
      ( ~ r2_hidden(C_59,C_60)
      | ~ r2_hidden(C_59,k4_xboole_0(B_61,C_60)) ) ),
    inference(resolution,[status(thm)],[c_54,c_121])).

tff(c_143,plain,(
    ! [B_61,C_60,B_7] :
      ( ~ r2_hidden('#skF_2'(k4_xboole_0(B_61,C_60),B_7),C_60)
      | r1_xboole_0(k4_xboole_0(B_61,C_60),B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_128])).

tff(c_2022,plain,(
    ! [B_219,B_61] :
      ( ~ r1_tarski(B_219,'#skF_3')
      | r1_xboole_0(k4_xboole_0(B_61,'#skF_4'),B_219) ) ),
    inference(resolution,[status(thm)],[c_2009,c_143])).

tff(c_24,plain,(
    ! [A_16,B_17] : k6_subset_1(A_16,B_17) = k4_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    ! [C_23,A_21,B_22] :
      ( k7_relat_1(C_23,k6_subset_1(A_21,B_22)) = k6_subset_1(C_23,k7_relat_1(C_23,B_22))
      | ~ r1_tarski(k1_relat_1(C_23),A_21)
      | ~ v1_relat_1(C_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_301,plain,(
    ! [C_109,A_110,B_111] :
      ( k7_relat_1(C_109,k4_xboole_0(A_110,B_111)) = k4_xboole_0(C_109,k7_relat_1(C_109,B_111))
      | ~ r1_tarski(k1_relat_1(C_109),A_110)
      | ~ v1_relat_1(C_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_28])).

tff(c_426,plain,(
    ! [C_140,B_141] :
      ( k7_relat_1(C_140,k4_xboole_0(k1_relat_1(C_140),B_141)) = k4_xboole_0(C_140,k7_relat_1(C_140,B_141))
      | ~ v1_relat_1(C_140) ) ),
    inference(resolution,[status(thm)],[c_18,c_301])).

tff(c_26,plain,(
    ! [C_20,A_18,B_19] :
      ( k7_relat_1(k7_relat_1(C_20,A_18),B_19) = k1_xboole_0
      | ~ r1_xboole_0(A_18,B_19)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2308,plain,(
    ! [C_245,B_246,B_247] :
      ( k7_relat_1(k4_xboole_0(C_245,k7_relat_1(C_245,B_246)),B_247) = k1_xboole_0
      | ~ r1_xboole_0(k4_xboole_0(k1_relat_1(C_245),B_246),B_247)
      | ~ v1_relat_1(C_245)
      | ~ v1_relat_1(C_245) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_26])).

tff(c_29036,plain,(
    ! [C_859,B_860] :
      ( k7_relat_1(k4_xboole_0(C_859,k7_relat_1(C_859,'#skF_4')),B_860) = k1_xboole_0
      | ~ v1_relat_1(C_859)
      | ~ r1_tarski(B_860,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2022,c_2308])).

tff(c_30,plain,(
    k7_relat_1(k6_subset_1('#skF_5',k7_relat_1('#skF_5','#skF_4')),'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_35,plain,(
    k7_relat_1(k4_xboole_0('#skF_5',k7_relat_1('#skF_5','#skF_4')),'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_30])).

tff(c_29080,plain,
    ( ~ v1_relat_1('#skF_5')
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_29036,c_35])).

tff(c_29133,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_34,c_29080])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:28:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.01/4.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.01/4.44  
% 11.01/4.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.01/4.44  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 11.01/4.44  
% 11.01/4.44  %Foreground sorts:
% 11.01/4.44  
% 11.01/4.44  
% 11.01/4.44  %Background operators:
% 11.01/4.44  
% 11.01/4.44  
% 11.01/4.44  %Foreground operators:
% 11.01/4.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.01/4.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.01/4.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.01/4.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 11.01/4.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.01/4.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.01/4.44  tff('#skF_5', type, '#skF_5': $i).
% 11.01/4.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.01/4.44  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 11.01/4.44  tff('#skF_3', type, '#skF_3': $i).
% 11.01/4.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.01/4.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 11.01/4.44  tff('#skF_4', type, '#skF_4': $i).
% 11.01/4.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.01/4.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.01/4.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.01/4.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 11.01/4.44  
% 11.14/4.46  tff(f_56, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 11.14/4.46  tff(f_83, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k6_subset_1(C, k7_relat_1(C, B)), A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t216_relat_1)).
% 11.14/4.46  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 11.14/4.46  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 11.14/4.46  tff(f_62, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 11.14/4.46  tff(f_64, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 11.14/4.46  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(k1_relat_1(C), A) => (k6_subset_1(C, k7_relat_1(C, B)) = k7_relat_1(C, k6_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t211_relat_1)).
% 11.14/4.46  tff(f_70, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 11.14/4.46  tff(c_18, plain, (![B_12]: (r1_tarski(B_12, B_12))), inference(cnfTransformation, [status(thm)], [f_56])).
% 11.14/4.46  tff(c_34, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.14/4.46  tff(c_32, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.14/4.46  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.14/4.46  tff(c_82, plain, (![C_45, B_46, A_47]: (r2_hidden(C_45, B_46) | ~r2_hidden(C_45, A_47) | ~r1_tarski(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.14/4.46  tff(c_213, plain, (![A_82, B_83, B_84]: (r2_hidden('#skF_2'(A_82, B_83), B_84) | ~r1_tarski(B_83, B_84) | r1_xboole_0(A_82, B_83))), inference(resolution, [status(thm)], [c_10, c_82])).
% 11.14/4.46  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 11.14/4.46  tff(c_1915, plain, (![A_210, B_211, B_212, B_213]: (r2_hidden('#skF_2'(A_210, B_211), B_212) | ~r1_tarski(B_213, B_212) | ~r1_tarski(B_211, B_213) | r1_xboole_0(A_210, B_211))), inference(resolution, [status(thm)], [c_213, c_2])).
% 11.14/4.46  tff(c_2009, plain, (![A_218, B_219]: (r2_hidden('#skF_2'(A_218, B_219), '#skF_4') | ~r1_tarski(B_219, '#skF_3') | r1_xboole_0(A_218, B_219))), inference(resolution, [status(thm)], [c_32, c_1915])).
% 11.14/4.46  tff(c_12, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.14/4.46  tff(c_49, plain, (![A_29, C_30, B_31]: (r1_xboole_0(A_29, C_30) | ~r1_tarski(A_29, k4_xboole_0(B_31, C_30)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 11.14/4.46  tff(c_54, plain, (![B_31, C_30]: (r1_xboole_0(k4_xboole_0(B_31, C_30), C_30))), inference(resolution, [status(thm)], [c_18, c_49])).
% 11.14/4.46  tff(c_121, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r2_hidden(C_58, B_57) | ~r2_hidden(C_58, A_56))), inference(cnfTransformation, [status(thm)], [f_50])).
% 11.14/4.46  tff(c_128, plain, (![C_59, C_60, B_61]: (~r2_hidden(C_59, C_60) | ~r2_hidden(C_59, k4_xboole_0(B_61, C_60)))), inference(resolution, [status(thm)], [c_54, c_121])).
% 11.14/4.46  tff(c_143, plain, (![B_61, C_60, B_7]: (~r2_hidden('#skF_2'(k4_xboole_0(B_61, C_60), B_7), C_60) | r1_xboole_0(k4_xboole_0(B_61, C_60), B_7))), inference(resolution, [status(thm)], [c_12, c_128])).
% 11.14/4.46  tff(c_2022, plain, (![B_219, B_61]: (~r1_tarski(B_219, '#skF_3') | r1_xboole_0(k4_xboole_0(B_61, '#skF_4'), B_219))), inference(resolution, [status(thm)], [c_2009, c_143])).
% 11.14/4.46  tff(c_24, plain, (![A_16, B_17]: (k6_subset_1(A_16, B_17)=k4_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_64])).
% 11.14/4.46  tff(c_28, plain, (![C_23, A_21, B_22]: (k7_relat_1(C_23, k6_subset_1(A_21, B_22))=k6_subset_1(C_23, k7_relat_1(C_23, B_22)) | ~r1_tarski(k1_relat_1(C_23), A_21) | ~v1_relat_1(C_23))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.14/4.46  tff(c_301, plain, (![C_109, A_110, B_111]: (k7_relat_1(C_109, k4_xboole_0(A_110, B_111))=k4_xboole_0(C_109, k7_relat_1(C_109, B_111)) | ~r1_tarski(k1_relat_1(C_109), A_110) | ~v1_relat_1(C_109))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_28])).
% 11.14/4.46  tff(c_426, plain, (![C_140, B_141]: (k7_relat_1(C_140, k4_xboole_0(k1_relat_1(C_140), B_141))=k4_xboole_0(C_140, k7_relat_1(C_140, B_141)) | ~v1_relat_1(C_140))), inference(resolution, [status(thm)], [c_18, c_301])).
% 11.14/4.46  tff(c_26, plain, (![C_20, A_18, B_19]: (k7_relat_1(k7_relat_1(C_20, A_18), B_19)=k1_xboole_0 | ~r1_xboole_0(A_18, B_19) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_70])).
% 11.14/4.46  tff(c_2308, plain, (![C_245, B_246, B_247]: (k7_relat_1(k4_xboole_0(C_245, k7_relat_1(C_245, B_246)), B_247)=k1_xboole_0 | ~r1_xboole_0(k4_xboole_0(k1_relat_1(C_245), B_246), B_247) | ~v1_relat_1(C_245) | ~v1_relat_1(C_245))), inference(superposition, [status(thm), theory('equality')], [c_426, c_26])).
% 11.14/4.46  tff(c_29036, plain, (![C_859, B_860]: (k7_relat_1(k4_xboole_0(C_859, k7_relat_1(C_859, '#skF_4')), B_860)=k1_xboole_0 | ~v1_relat_1(C_859) | ~r1_tarski(B_860, '#skF_3'))), inference(resolution, [status(thm)], [c_2022, c_2308])).
% 11.14/4.46  tff(c_30, plain, (k7_relat_1(k6_subset_1('#skF_5', k7_relat_1('#skF_5', '#skF_4')), '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 11.14/4.46  tff(c_35, plain, (k7_relat_1(k4_xboole_0('#skF_5', k7_relat_1('#skF_5', '#skF_4')), '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_24, c_30])).
% 11.14/4.46  tff(c_29080, plain, (~v1_relat_1('#skF_5') | ~r1_tarski('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_29036, c_35])).
% 11.14/4.46  tff(c_29133, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_34, c_29080])).
% 11.14/4.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.14/4.46  
% 11.14/4.46  Inference rules
% 11.14/4.46  ----------------------
% 11.14/4.46  #Ref     : 0
% 11.14/4.46  #Sup     : 7686
% 11.14/4.46  #Fact    : 0
% 11.14/4.46  #Define  : 0
% 11.14/4.46  #Split   : 5
% 11.14/4.46  #Chain   : 0
% 11.14/4.46  #Close   : 0
% 11.14/4.46  
% 11.14/4.46  Ordering : KBO
% 11.14/4.46  
% 11.14/4.46  Simplification rules
% 11.14/4.46  ----------------------
% 11.14/4.46  #Subsume      : 2468
% 11.14/4.46  #Demod        : 9957
% 11.14/4.46  #Tautology    : 4171
% 11.14/4.46  #SimpNegUnit  : 0
% 11.14/4.46  #BackRed      : 32
% 11.14/4.46  
% 11.14/4.46  #Partial instantiations: 0
% 11.14/4.46  #Strategies tried      : 1
% 11.14/4.46  
% 11.14/4.46  Timing (in seconds)
% 11.14/4.46  ----------------------
% 11.14/4.46  Preprocessing        : 0.32
% 11.14/4.46  Parsing              : 0.17
% 11.14/4.46  CNF conversion       : 0.02
% 11.14/4.46  Main loop            : 3.37
% 11.14/4.46  Inferencing          : 0.67
% 11.14/4.46  Reduction            : 1.59
% 11.14/4.46  Demodulation         : 1.34
% 11.14/4.46  BG Simplification    : 0.06
% 11.14/4.46  Subsumption          : 0.88
% 11.14/4.46  Abstraction          : 0.12
% 11.14/4.46  MUC search           : 0.00
% 11.14/4.46  Cooper               : 0.00
% 11.14/4.46  Total                : 3.72
% 11.14/4.46  Index Insertion      : 0.00
% 11.14/4.46  Index Deletion       : 0.00
% 11.14/4.46  Index Matching       : 0.00
% 11.14/4.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
