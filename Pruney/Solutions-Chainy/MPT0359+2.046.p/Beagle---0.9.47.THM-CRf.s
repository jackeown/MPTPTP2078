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
% DateTime   : Thu Dec  3 09:56:15 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 146 expanded)
%              Number of leaves         :   28 (  58 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 208 expanded)
%              Number of equality atoms :   31 (  93 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_67,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_69,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_79,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_22,plain,(
    ! [A_13] : k1_subset_1(A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24,plain,(
    ! [A_14] : k2_subset_1(A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_26,plain,(
    ! [A_15] : m1_subset_1(k1_subset_1(A_15),k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_32,plain,(
    ! [A_20] : k3_subset_1(A_20,k1_subset_1(A_20)) = k2_subset_1(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_34,plain,(
    ! [A_21] :
      ( r1_tarski(k1_subset_1(A_21),k3_subset_1(A_21,k1_subset_1(A_21)))
      | ~ m1_subset_1(k1_subset_1(A_21),k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_47,plain,(
    ! [A_21] :
      ( r1_tarski(k1_subset_1(A_21),k2_subset_1(A_21))
      | ~ m1_subset_1(k1_subset_1(A_21),k1_zfmisc_1(A_21)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34])).

tff(c_49,plain,(
    ! [A_21] : r1_tarski(k1_subset_1(A_21),k2_subset_1(A_21)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_47])).

tff(c_51,plain,(
    ! [A_21] : r1_tarski(k1_subset_1(A_21),A_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_49])).

tff(c_54,plain,(
    ! [A_21] : r1_tarski(k1_xboole_0,A_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_51])).

tff(c_14,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_112,plain,(
    ! [B_36,A_37] :
      ( ~ r1_xboole_0(B_36,A_37)
      | ~ r1_tarski(B_36,A_37)
      | v1_xboole_0(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_115,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_112])).

tff(c_118,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_115])).

tff(c_53,plain,(
    ! [A_20] : k3_subset_1(A_20,k1_subset_1(A_20)) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_32])).

tff(c_56,plain,(
    ! [A_20] : k3_subset_1(A_20,k1_xboole_0) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_53])).

tff(c_55,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26])).

tff(c_193,plain,(
    ! [A_54,B_55] :
      ( k3_subset_1(A_54,k3_subset_1(A_54,B_55)) = B_55
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_199,plain,(
    ! [A_15] : k3_subset_1(A_15,k3_subset_1(A_15,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55,c_193])).

tff(c_203,plain,(
    ! [A_15] : k3_subset_1(A_15,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_199])).

tff(c_102,plain,(
    ! [A_32,B_33] :
      ( r2_hidden('#skF_1'(A_32,B_33),A_32)
      | r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( ~ v1_xboole_0(B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_107,plain,(
    ! [A_34,B_35] :
      ( ~ v1_xboole_0(A_34)
      | r1_tarski(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_102,c_20])).

tff(c_40,plain,
    ( k2_subset_1('#skF_2') != '#skF_3'
    | ~ r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_52,plain,
    ( '#skF_2' != '#skF_3'
    | ~ r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_40])).

tff(c_88,plain,(
    ~ r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3')
    | k2_subset_1('#skF_2') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_50,plain,
    ( r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_46])).

tff(c_95,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_50])).

tff(c_96,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_88])).

tff(c_111,plain,(
    ~ v1_xboole_0(k3_subset_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_107,c_96])).

tff(c_204,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_111])).

tff(c_208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_204])).

tff(c_209,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k3_subset_1(A_16,B_17),k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_210,plain,(
    r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_310,plain,(
    ! [A_76,B_77] :
      ( k3_subset_1(A_76,k3_subset_1(A_76,B_77)) = B_77
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_317,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_310])).

tff(c_36,plain,(
    ! [A_21,B_22] :
      ( k1_subset_1(A_21) = B_22
      | ~ r1_tarski(B_22,k3_subset_1(A_21,B_22))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_361,plain,(
    ! [B_82,A_83] :
      ( k1_xboole_0 = B_82
      | ~ r1_tarski(B_82,k3_subset_1(A_83,B_82))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_83)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_36])).

tff(c_364,plain,
    ( k3_subset_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ r1_tarski(k3_subset_1('#skF_2','#skF_3'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_361])).

tff(c_380,plain,
    ( k3_subset_1('#skF_2','#skF_3') = k1_xboole_0
    | ~ m1_subset_1(k3_subset_1('#skF_2','#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_364])).

tff(c_418,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_2','#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_380])).

tff(c_421,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_418])).

tff(c_425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_421])).

tff(c_426,plain,(
    k3_subset_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_380])).

tff(c_428,plain,(
    k3_subset_1('#skF_2',k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_317])).

tff(c_459,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_428,c_56])).

tff(c_471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_459])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 09:56:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.36  
% 2.33/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.36  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.33/1.36  
% 2.33/1.36  %Foreground sorts:
% 2.33/1.36  
% 2.33/1.36  
% 2.33/1.36  %Background operators:
% 2.33/1.36  
% 2.33/1.36  
% 2.33/1.36  %Foreground operators:
% 2.33/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.33/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.36  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.33/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.33/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.33/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.33/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.36  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.33/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.33/1.36  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.33/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.33/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.33/1.36  
% 2.33/1.38  tff(f_65, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.33/1.38  tff(f_67, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.33/1.38  tff(f_69, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 2.33/1.38  tff(f_79, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.33/1.38  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.33/1.38  tff(f_50, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.33/1.38  tff(f_58, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.33/1.38  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.33/1.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.33/1.38  tff(f_63, axiom, (![A, B]: ~(r2_hidden(A, B) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_boole)).
% 2.33/1.38  tff(f_92, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 2.33/1.38  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.33/1.38  tff(c_22, plain, (![A_13]: (k1_subset_1(A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.33/1.38  tff(c_24, plain, (![A_14]: (k2_subset_1(A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.33/1.38  tff(c_26, plain, (![A_15]: (m1_subset_1(k1_subset_1(A_15), k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.33/1.38  tff(c_32, plain, (![A_20]: (k3_subset_1(A_20, k1_subset_1(A_20))=k2_subset_1(A_20))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.33/1.38  tff(c_34, plain, (![A_21]: (r1_tarski(k1_subset_1(A_21), k3_subset_1(A_21, k1_subset_1(A_21))) | ~m1_subset_1(k1_subset_1(A_21), k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.33/1.38  tff(c_47, plain, (![A_21]: (r1_tarski(k1_subset_1(A_21), k2_subset_1(A_21)) | ~m1_subset_1(k1_subset_1(A_21), k1_zfmisc_1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34])).
% 2.33/1.38  tff(c_49, plain, (![A_21]: (r1_tarski(k1_subset_1(A_21), k2_subset_1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_47])).
% 2.33/1.38  tff(c_51, plain, (![A_21]: (r1_tarski(k1_subset_1(A_21), A_21))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_49])).
% 2.33/1.38  tff(c_54, plain, (![A_21]: (r1_tarski(k1_xboole_0, A_21))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_51])).
% 2.33/1.38  tff(c_14, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.33/1.38  tff(c_112, plain, (![B_36, A_37]: (~r1_xboole_0(B_36, A_37) | ~r1_tarski(B_36, A_37) | v1_xboole_0(B_36))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.33/1.38  tff(c_115, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_112])).
% 2.33/1.38  tff(c_118, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_115])).
% 2.33/1.38  tff(c_53, plain, (![A_20]: (k3_subset_1(A_20, k1_subset_1(A_20))=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_32])).
% 2.33/1.38  tff(c_56, plain, (![A_20]: (k3_subset_1(A_20, k1_xboole_0)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_53])).
% 2.33/1.38  tff(c_55, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26])).
% 2.33/1.38  tff(c_193, plain, (![A_54, B_55]: (k3_subset_1(A_54, k3_subset_1(A_54, B_55))=B_55 | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.33/1.38  tff(c_199, plain, (![A_15]: (k3_subset_1(A_15, k3_subset_1(A_15, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_55, c_193])).
% 2.33/1.38  tff(c_203, plain, (![A_15]: (k3_subset_1(A_15, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_56, c_199])).
% 2.33/1.38  tff(c_102, plain, (![A_32, B_33]: (r2_hidden('#skF_1'(A_32, B_33), A_32) | r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.33/1.38  tff(c_20, plain, (![B_12, A_11]: (~v1_xboole_0(B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.33/1.38  tff(c_107, plain, (![A_34, B_35]: (~v1_xboole_0(A_34) | r1_tarski(A_34, B_35))), inference(resolution, [status(thm)], [c_102, c_20])).
% 2.33/1.38  tff(c_40, plain, (k2_subset_1('#skF_2')!='#skF_3' | ~r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.33/1.38  tff(c_52, plain, ('#skF_2'!='#skF_3' | ~r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_40])).
% 2.33/1.38  tff(c_88, plain, (~r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_52])).
% 2.33/1.38  tff(c_46, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3') | k2_subset_1('#skF_2')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.33/1.38  tff(c_50, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_46])).
% 2.33/1.38  tff(c_95, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_88, c_50])).
% 2.33/1.38  tff(c_96, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_95, c_88])).
% 2.33/1.38  tff(c_111, plain, (~v1_xboole_0(k3_subset_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_107, c_96])).
% 2.33/1.38  tff(c_204, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_203, c_111])).
% 2.33/1.38  tff(c_208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_118, c_204])).
% 2.33/1.38  tff(c_209, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_52])).
% 2.33/1.38  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.33/1.38  tff(c_28, plain, (![A_16, B_17]: (m1_subset_1(k3_subset_1(A_16, B_17), k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.33/1.38  tff(c_210, plain, (r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_52])).
% 2.33/1.38  tff(c_310, plain, (![A_76, B_77]: (k3_subset_1(A_76, k3_subset_1(A_76, B_77))=B_77 | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.33/1.38  tff(c_317, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_38, c_310])).
% 2.33/1.38  tff(c_36, plain, (![A_21, B_22]: (k1_subset_1(A_21)=B_22 | ~r1_tarski(B_22, k3_subset_1(A_21, B_22)) | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.33/1.38  tff(c_361, plain, (![B_82, A_83]: (k1_xboole_0=B_82 | ~r1_tarski(B_82, k3_subset_1(A_83, B_82)) | ~m1_subset_1(B_82, k1_zfmisc_1(A_83)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_36])).
% 2.33/1.38  tff(c_364, plain, (k3_subset_1('#skF_2', '#skF_3')=k1_xboole_0 | ~r1_tarski(k3_subset_1('#skF_2', '#skF_3'), '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_317, c_361])).
% 2.33/1.38  tff(c_380, plain, (k3_subset_1('#skF_2', '#skF_3')=k1_xboole_0 | ~m1_subset_1(k3_subset_1('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_364])).
% 2.33/1.38  tff(c_418, plain, (~m1_subset_1(k3_subset_1('#skF_2', '#skF_3'), k1_zfmisc_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_380])).
% 2.33/1.38  tff(c_421, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_418])).
% 2.33/1.38  tff(c_425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_421])).
% 2.33/1.38  tff(c_426, plain, (k3_subset_1('#skF_2', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_380])).
% 2.33/1.38  tff(c_428, plain, (k3_subset_1('#skF_2', k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_426, c_317])).
% 2.33/1.38  tff(c_459, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_428, c_56])).
% 2.33/1.38  tff(c_471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_209, c_459])).
% 2.33/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.38  
% 2.33/1.38  Inference rules
% 2.33/1.38  ----------------------
% 2.33/1.38  #Ref     : 0
% 2.33/1.38  #Sup     : 85
% 2.33/1.38  #Fact    : 0
% 2.33/1.38  #Define  : 0
% 2.33/1.38  #Split   : 3
% 2.33/1.38  #Chain   : 0
% 2.33/1.38  #Close   : 0
% 2.33/1.38  
% 2.33/1.38  Ordering : KBO
% 2.33/1.38  
% 2.33/1.38  Simplification rules
% 2.33/1.38  ----------------------
% 2.33/1.38  #Subsume      : 12
% 2.33/1.38  #Demod        : 50
% 2.33/1.38  #Tautology    : 47
% 2.33/1.38  #SimpNegUnit  : 3
% 2.33/1.38  #BackRed      : 7
% 2.33/1.38  
% 2.33/1.38  #Partial instantiations: 0
% 2.33/1.38  #Strategies tried      : 1
% 2.33/1.38  
% 2.33/1.38  Timing (in seconds)
% 2.33/1.38  ----------------------
% 2.33/1.38  Preprocessing        : 0.29
% 2.33/1.39  Parsing              : 0.16
% 2.33/1.39  CNF conversion       : 0.02
% 2.33/1.39  Main loop            : 0.31
% 2.59/1.39  Inferencing          : 0.11
% 2.59/1.39  Reduction            : 0.10
% 2.59/1.39  Demodulation         : 0.07
% 2.59/1.39  BG Simplification    : 0.01
% 2.59/1.39  Subsumption          : 0.06
% 2.59/1.39  Abstraction          : 0.01
% 2.59/1.39  MUC search           : 0.00
% 2.59/1.39  Cooper               : 0.00
% 2.59/1.39  Total                : 0.64
% 2.59/1.39  Index Insertion      : 0.00
% 2.59/1.39  Index Deletion       : 0.00
% 2.59/1.39  Index Matching       : 0.00
% 2.59/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
