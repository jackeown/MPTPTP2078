%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:15 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 130 expanded)
%              Number of leaves         :   27 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 198 expanded)
%              Number of equality atoms :   32 (  90 expanded)
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_47,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_61,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k3_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_12] : k2_subset_1(A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_38,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | k2_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_41,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_38])).

tff(c_74,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_41])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_75,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_30])).

tff(c_123,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(A_39,B_40) = k3_subset_1(A_39,B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_131,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_subset_1('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_75,c_123])).

tff(c_8,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_136,plain,(
    ! [A_41,C_42,B_43] :
      ( r1_tarski(k5_xboole_0(A_41,C_42),B_43)
      | ~ r1_tarski(C_42,B_43)
      | ~ r1_tarski(A_41,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_178,plain,(
    ! [A_49,B_50,B_51] :
      ( r1_tarski(k4_xboole_0(A_49,B_50),B_51)
      | ~ r1_tarski(k3_xboole_0(A_49,B_50),B_51)
      | ~ r1_tarski(A_49,B_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_136])).

tff(c_195,plain,(
    ! [B_52] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_1'),B_52)
      | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_1'),B_52)
      | ~ r1_tarski('#skF_1',B_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_178])).

tff(c_206,plain,(
    ! [B_53] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_1'),B_53)
      | ~ r1_tarski('#skF_1',B_53) ) ),
    inference(resolution,[status(thm)],[c_10,c_195])).

tff(c_32,plain,
    ( k2_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_42,plain,
    ( '#skF_2' != '#skF_1'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_32])).

tff(c_82,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_74,c_74,c_42])).

tff(c_219,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_206,c_82])).

tff(c_226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_219])).

tff(c_228,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_41])).

tff(c_14,plain,(
    ! [A_11] : k1_subset_1(A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [A_19] : k3_subset_1(A_19,k1_subset_1(A_19)) = k2_subset_1(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_40,plain,(
    ! [A_19] : k3_subset_1(A_19,k1_subset_1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_24])).

tff(c_45,plain,(
    ! [A_19] : k3_subset_1(A_19,k1_xboole_0) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_40])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k3_subset_1(A_15,B_16),k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_227,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_41])).

tff(c_260,plain,(
    ! [A_64,B_65] :
      ( k3_subset_1(A_64,k3_subset_1(A_64,B_65)) = B_65
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_266,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_260])).

tff(c_28,plain,(
    ! [A_20,B_21] :
      ( k1_subset_1(A_20) = B_21
      | ~ r1_tarski(B_21,k3_subset_1(A_20,B_21))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_289,plain,(
    ! [B_69,A_70] :
      ( k1_xboole_0 = B_69
      | ~ r1_tarski(B_69,k3_subset_1(A_70,B_69))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_70)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_28])).

tff(c_292,plain,
    ( k3_subset_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_289])).

tff(c_301,plain,
    ( k3_subset_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_292])).

tff(c_304,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_301])).

tff(c_307,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_304])).

tff(c_311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_307])).

tff(c_312,plain,(
    k3_subset_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_301])).

tff(c_315,plain,(
    k3_subset_1('#skF_1',k1_xboole_0) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_312,c_266])).

tff(c_318,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_315])).

tff(c_320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_228,c_318])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:58:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.24  
% 2.16/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.24  %$ r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.16/1.24  
% 2.16/1.24  %Foreground sorts:
% 2.16/1.24  
% 2.16/1.24  
% 2.16/1.24  %Background operators:
% 2.16/1.24  
% 2.16/1.24  
% 2.16/1.24  %Foreground operators:
% 2.16/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.16/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.24  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.16/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.24  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.16/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.24  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.16/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.24  
% 2.16/1.26  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.16/1.26  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 2.16/1.26  tff(f_47, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.16/1.26  tff(f_74, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 2.16/1.26  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.16/1.26  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.16/1.26  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 2.16/1.26  tff(f_45, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 2.16/1.26  tff(f_61, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 2.16/1.26  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.16/1.26  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.16/1.26  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 2.16/1.26  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.26  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(k3_xboole_0(A_5, C_7), B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.26  tff(c_16, plain, (![A_12]: (k2_subset_1(A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.16/1.26  tff(c_38, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | k2_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.16/1.26  tff(c_41, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_38])).
% 2.16/1.26  tff(c_74, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_41])).
% 2.16/1.26  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.16/1.26  tff(c_75, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_30])).
% 2.16/1.26  tff(c_123, plain, (![A_39, B_40]: (k4_xboole_0(A_39, B_40)=k3_subset_1(A_39, B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.16/1.26  tff(c_131, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_subset_1('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_75, c_123])).
% 2.16/1.26  tff(c_8, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.16/1.26  tff(c_136, plain, (![A_41, C_42, B_43]: (r1_tarski(k5_xboole_0(A_41, C_42), B_43) | ~r1_tarski(C_42, B_43) | ~r1_tarski(A_41, B_43))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.16/1.26  tff(c_178, plain, (![A_49, B_50, B_51]: (r1_tarski(k4_xboole_0(A_49, B_50), B_51) | ~r1_tarski(k3_xboole_0(A_49, B_50), B_51) | ~r1_tarski(A_49, B_51))), inference(superposition, [status(thm), theory('equality')], [c_8, c_136])).
% 2.16/1.26  tff(c_195, plain, (![B_52]: (r1_tarski(k3_subset_1('#skF_1', '#skF_1'), B_52) | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_1'), B_52) | ~r1_tarski('#skF_1', B_52))), inference(superposition, [status(thm), theory('equality')], [c_131, c_178])).
% 2.16/1.26  tff(c_206, plain, (![B_53]: (r1_tarski(k3_subset_1('#skF_1', '#skF_1'), B_53) | ~r1_tarski('#skF_1', B_53))), inference(resolution, [status(thm)], [c_10, c_195])).
% 2.16/1.26  tff(c_32, plain, (k2_subset_1('#skF_1')!='#skF_2' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.16/1.26  tff(c_42, plain, ('#skF_2'!='#skF_1' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_32])).
% 2.16/1.26  tff(c_82, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_74, c_74, c_42])).
% 2.16/1.26  tff(c_219, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_206, c_82])).
% 2.16/1.26  tff(c_226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_219])).
% 2.16/1.26  tff(c_228, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_41])).
% 2.16/1.26  tff(c_14, plain, (![A_11]: (k1_subset_1(A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.16/1.26  tff(c_24, plain, (![A_19]: (k3_subset_1(A_19, k1_subset_1(A_19))=k2_subset_1(A_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.16/1.26  tff(c_40, plain, (![A_19]: (k3_subset_1(A_19, k1_subset_1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_24])).
% 2.16/1.26  tff(c_45, plain, (![A_19]: (k3_subset_1(A_19, k1_xboole_0)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_40])).
% 2.16/1.26  tff(c_20, plain, (![A_15, B_16]: (m1_subset_1(k3_subset_1(A_15, B_16), k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.16/1.26  tff(c_227, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitRight, [status(thm)], [c_41])).
% 2.16/1.26  tff(c_260, plain, (![A_64, B_65]: (k3_subset_1(A_64, k3_subset_1(A_64, B_65))=B_65 | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.16/1.26  tff(c_266, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_30, c_260])).
% 2.16/1.26  tff(c_28, plain, (![A_20, B_21]: (k1_subset_1(A_20)=B_21 | ~r1_tarski(B_21, k3_subset_1(A_20, B_21)) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.16/1.26  tff(c_289, plain, (![B_69, A_70]: (k1_xboole_0=B_69 | ~r1_tarski(B_69, k3_subset_1(A_70, B_69)) | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_28])).
% 2.16/1.26  tff(c_292, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_266, c_289])).
% 2.16/1.26  tff(c_301, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0 | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_292])).
% 2.16/1.26  tff(c_304, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_301])).
% 2.16/1.26  tff(c_307, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_304])).
% 2.16/1.26  tff(c_311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_307])).
% 2.16/1.26  tff(c_312, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_301])).
% 2.16/1.26  tff(c_315, plain, (k3_subset_1('#skF_1', k1_xboole_0)='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_312, c_266])).
% 2.16/1.26  tff(c_318, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_45, c_315])).
% 2.16/1.26  tff(c_320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_228, c_318])).
% 2.16/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.26  
% 2.16/1.26  Inference rules
% 2.16/1.26  ----------------------
% 2.16/1.26  #Ref     : 0
% 2.16/1.26  #Sup     : 60
% 2.16/1.26  #Fact    : 0
% 2.16/1.26  #Define  : 0
% 2.16/1.26  #Split   : 3
% 2.16/1.26  #Chain   : 0
% 2.16/1.26  #Close   : 0
% 2.16/1.26  
% 2.16/1.26  Ordering : KBO
% 2.16/1.26  
% 2.16/1.26  Simplification rules
% 2.16/1.26  ----------------------
% 2.16/1.26  #Subsume      : 3
% 2.16/1.26  #Demod        : 27
% 2.16/1.26  #Tautology    : 30
% 2.16/1.26  #SimpNegUnit  : 1
% 2.16/1.26  #BackRed      : 5
% 2.16/1.26  
% 2.16/1.26  #Partial instantiations: 0
% 2.16/1.26  #Strategies tried      : 1
% 2.16/1.26  
% 2.16/1.26  Timing (in seconds)
% 2.16/1.26  ----------------------
% 2.16/1.26  Preprocessing        : 0.30
% 2.16/1.26  Parsing              : 0.16
% 2.16/1.26  CNF conversion       : 0.02
% 2.16/1.26  Main loop            : 0.21
% 2.16/1.26  Inferencing          : 0.07
% 2.16/1.26  Reduction            : 0.06
% 2.16/1.26  Demodulation         : 0.05
% 2.16/1.26  BG Simplification    : 0.01
% 2.16/1.26  Subsumption          : 0.05
% 2.16/1.26  Abstraction          : 0.01
% 2.16/1.26  MUC search           : 0.00
% 2.16/1.26  Cooper               : 0.00
% 2.16/1.26  Total                : 0.53
% 2.16/1.26  Index Insertion      : 0.00
% 2.16/1.26  Index Deletion       : 0.00
% 2.16/1.26  Index Matching       : 0.00
% 2.16/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
