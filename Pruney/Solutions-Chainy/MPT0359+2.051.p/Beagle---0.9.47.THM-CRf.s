%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:16 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 143 expanded)
%              Number of leaves         :   27 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :   85 ( 217 expanded)
%              Number of equality atoms :   32 (  99 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_45,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_59,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(c_16,plain,(
    ! [A_11] : k2_subset_1(A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,
    ( k2_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_42,plain,
    ( '#skF_2' != '#skF_1'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_32])).

tff(c_76,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_38,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | k2_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_41,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_38])).

tff(c_77,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_41])).

tff(c_78,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_77,c_76])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_79,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_30])).

tff(c_104,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k3_subset_1(A_34,B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_108,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_subset_1('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_79,c_104])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_145,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_tarski(k5_xboole_0(A_43,C_44),B_45)
      | ~ r1_tarski(C_44,B_45)
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_162,plain,(
    ! [A_46,B_47,B_48] :
      ( r1_tarski(k4_xboole_0(A_46,B_47),B_48)
      | ~ r1_tarski(k3_xboole_0(A_46,B_47),B_48)
      | ~ r1_tarski(A_46,B_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_145])).

tff(c_179,plain,(
    ! [B_49] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_1'),B_49)
      | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_1'),B_49)
      | ~ r1_tarski('#skF_1',B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_162])).

tff(c_183,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_179])).

tff(c_190,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_183])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_190])).

tff(c_193,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_14,plain,(
    ! [A_10] : k1_subset_1(A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_18] : k3_subset_1(A_18,k1_subset_1(A_18)) = k2_subset_1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_40,plain,(
    ! [A_18] : k3_subset_1(A_18,k1_subset_1(A_18)) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_24])).

tff(c_45,plain,(
    ! [A_18] : k3_subset_1(A_18,k1_xboole_0) = A_18 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_40])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k3_subset_1(A_14,B_15),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_194,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_221,plain,(
    ! [A_56,B_57] :
      ( k3_subset_1(A_56,k3_subset_1(A_56,B_57)) = B_57
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_224,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_221])).

tff(c_28,plain,(
    ! [A_19,B_20] :
      ( k1_subset_1(A_19) = B_20
      | ~ r1_tarski(B_20,k3_subset_1(A_19,B_20))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_266,plain,(
    ! [B_66,A_67] :
      ( k1_xboole_0 = B_66
      | ~ r1_tarski(B_66,k3_subset_1(A_67,B_66))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_28])).

tff(c_273,plain,
    ( k3_subset_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_266])).

tff(c_279,plain,
    ( k3_subset_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_273])).

tff(c_281,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_279])).

tff(c_284,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_281])).

tff(c_288,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_284])).

tff(c_289,plain,(
    k3_subset_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_292,plain,(
    k3_subset_1('#skF_1',k1_xboole_0) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_224])).

tff(c_295,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_292])).

tff(c_297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_295])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.26  
% 2.09/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.27  %$ r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.09/1.27  
% 2.09/1.27  %Foreground sorts:
% 2.09/1.27  
% 2.09/1.27  
% 2.09/1.27  %Background operators:
% 2.09/1.27  
% 2.09/1.27  
% 2.09/1.27  %Foreground operators:
% 2.09/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.09/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.27  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.09/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.27  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.09/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.27  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.09/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.27  
% 2.09/1.28  tff(f_45, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.09/1.28  tff(f_72, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 2.09/1.28  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.09/1.28  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.09/1.28  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.09/1.28  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.09/1.28  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 2.09/1.28  tff(f_43, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.09/1.28  tff(f_59, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.09/1.28  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.09/1.28  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.09/1.28  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.09/1.28  tff(c_16, plain, (![A_11]: (k2_subset_1(A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.09/1.28  tff(c_32, plain, (k2_subset_1('#skF_1')!='#skF_2' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.09/1.28  tff(c_42, plain, ('#skF_2'!='#skF_1' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_32])).
% 2.09/1.28  tff(c_76, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_42])).
% 2.09/1.28  tff(c_38, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | k2_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.09/1.28  tff(c_41, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_38])).
% 2.09/1.28  tff(c_77, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_76, c_41])).
% 2.09/1.28  tff(c_78, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_77, c_77, c_76])).
% 2.09/1.28  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.09/1.28  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.09/1.28  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.09/1.28  tff(c_79, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_30])).
% 2.09/1.28  tff(c_104, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k3_subset_1(A_34, B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.09/1.28  tff(c_108, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_subset_1('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_79, c_104])).
% 2.09/1.28  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.09/1.28  tff(c_145, plain, (![A_43, C_44, B_45]: (r1_tarski(k5_xboole_0(A_43, C_44), B_45) | ~r1_tarski(C_44, B_45) | ~r1_tarski(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.09/1.28  tff(c_162, plain, (![A_46, B_47, B_48]: (r1_tarski(k4_xboole_0(A_46, B_47), B_48) | ~r1_tarski(k3_xboole_0(A_46, B_47), B_48) | ~r1_tarski(A_46, B_48))), inference(superposition, [status(thm), theory('equality')], [c_8, c_145])).
% 2.09/1.28  tff(c_179, plain, (![B_49]: (r1_tarski(k3_subset_1('#skF_1', '#skF_1'), B_49) | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_1'), B_49) | ~r1_tarski('#skF_1', B_49))), inference(superposition, [status(thm), theory('equality')], [c_108, c_162])).
% 2.09/1.28  tff(c_183, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1') | ~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_12, c_179])).
% 2.09/1.28  tff(c_190, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_183])).
% 2.09/1.28  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_190])).
% 2.09/1.28  tff(c_193, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_42])).
% 2.09/1.28  tff(c_14, plain, (![A_10]: (k1_subset_1(A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.09/1.28  tff(c_24, plain, (![A_18]: (k3_subset_1(A_18, k1_subset_1(A_18))=k2_subset_1(A_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.09/1.28  tff(c_40, plain, (![A_18]: (k3_subset_1(A_18, k1_subset_1(A_18))=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_24])).
% 2.09/1.28  tff(c_45, plain, (![A_18]: (k3_subset_1(A_18, k1_xboole_0)=A_18)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_40])).
% 2.09/1.28  tff(c_20, plain, (![A_14, B_15]: (m1_subset_1(k3_subset_1(A_14, B_15), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.09/1.28  tff(c_194, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_42])).
% 2.09/1.28  tff(c_221, plain, (![A_56, B_57]: (k3_subset_1(A_56, k3_subset_1(A_56, B_57))=B_57 | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.09/1.28  tff(c_224, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_30, c_221])).
% 2.09/1.28  tff(c_28, plain, (![A_19, B_20]: (k1_subset_1(A_19)=B_20 | ~r1_tarski(B_20, k3_subset_1(A_19, B_20)) | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.09/1.28  tff(c_266, plain, (![B_66, A_67]: (k1_xboole_0=B_66 | ~r1_tarski(B_66, k3_subset_1(A_67, B_66)) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_28])).
% 2.09/1.28  tff(c_273, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_224, c_266])).
% 2.09/1.28  tff(c_279, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0 | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_273])).
% 2.09/1.28  tff(c_281, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_279])).
% 2.09/1.28  tff(c_284, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_281])).
% 2.09/1.28  tff(c_288, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_284])).
% 2.09/1.28  tff(c_289, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_279])).
% 2.09/1.28  tff(c_292, plain, (k3_subset_1('#skF_1', k1_xboole_0)='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_289, c_224])).
% 2.09/1.28  tff(c_295, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_45, c_292])).
% 2.09/1.28  tff(c_297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_193, c_295])).
% 2.09/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.28  
% 2.09/1.28  Inference rules
% 2.09/1.28  ----------------------
% 2.09/1.28  #Ref     : 0
% 2.09/1.28  #Sup     : 56
% 2.09/1.28  #Fact    : 0
% 2.09/1.28  #Define  : 0
% 2.09/1.28  #Split   : 3
% 2.09/1.28  #Chain   : 0
% 2.09/1.28  #Close   : 0
% 2.09/1.28  
% 2.09/1.28  Ordering : KBO
% 2.09/1.28  
% 2.09/1.28  Simplification rules
% 2.09/1.28  ----------------------
% 2.09/1.28  #Subsume      : 1
% 2.09/1.28  #Demod        : 26
% 2.09/1.28  #Tautology    : 30
% 2.09/1.28  #SimpNegUnit  : 4
% 2.09/1.28  #BackRed      : 6
% 2.09/1.28  
% 2.09/1.28  #Partial instantiations: 0
% 2.09/1.28  #Strategies tried      : 1
% 2.09/1.28  
% 2.09/1.28  Timing (in seconds)
% 2.09/1.28  ----------------------
% 2.09/1.29  Preprocessing        : 0.30
% 2.09/1.29  Parsing              : 0.16
% 2.09/1.29  CNF conversion       : 0.02
% 2.09/1.29  Main loop            : 0.22
% 2.09/1.29  Inferencing          : 0.07
% 2.09/1.29  Reduction            : 0.07
% 2.09/1.29  Demodulation         : 0.05
% 2.09/1.29  BG Simplification    : 0.01
% 2.09/1.29  Subsumption          : 0.04
% 2.09/1.29  Abstraction          : 0.01
% 2.09/1.29  MUC search           : 0.00
% 2.09/1.29  Cooper               : 0.00
% 2.09/1.29  Total                : 0.55
% 2.09/1.29  Index Insertion      : 0.00
% 2.09/1.29  Index Deletion       : 0.00
% 2.09/1.29  Index Matching       : 0.00
% 2.09/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
