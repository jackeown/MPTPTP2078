%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:27 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   69 (  81 expanded)
%              Number of leaves         :   32 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 (  88 expanded)
%              Number of equality atoms :   43 (  50 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_49,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_22,plain,(
    ! [A_22] : k2_subset_1(A_22) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_32,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_35,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_32])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_487,plain,(
    ! [A_73,B_74] :
      ( k3_subset_1(A_73,k3_subset_1(A_73,B_74)) = B_74
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_493,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_34,c_487])).

tff(c_459,plain,(
    ! [A_71,B_72] :
      ( m1_subset_1(k3_subset_1(A_71,B_72),k1_zfmisc_1(A_71))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = k3_subset_1(A_23,B_24)
      | ~ m1_subset_1(B_24,k1_zfmisc_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_567,plain,(
    ! [A_83,B_84] :
      ( k4_xboole_0(A_83,k3_subset_1(A_83,B_84)) = k3_subset_1(A_83,k3_subset_1(A_83,B_84))
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(resolution,[status(thm)],[c_459,c_24])).

tff(c_571,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_567])).

tff(c_574,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_571])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_164,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = A_45
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_302,plain,(
    ! [A_62,B_63] : k3_xboole_0(k4_xboole_0(A_62,B_63),A_62) = k4_xboole_0(A_62,B_63) ),
    inference(resolution,[status(thm)],[c_10,c_164])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_112,plain,(
    ! [A_39,B_40] : k2_xboole_0(A_39,k3_xboole_0(A_39,B_40)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_121,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_112])).

tff(c_314,plain,(
    ! [A_62,B_63] : k2_xboole_0(A_62,k4_xboole_0(A_62,B_63)) = A_62 ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_121])).

tff(c_591,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_574,c_314])).

tff(c_14,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_169,plain,(
    ! [A_47,B_48] : k3_tarski(k2_tarski(A_47,B_48)) = k2_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_184,plain,(
    ! [B_49,A_50] : k3_tarski(k2_tarski(B_49,A_50)) = k2_xboole_0(A_50,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_169])).

tff(c_20,plain,(
    ! [A_20,B_21] : k3_tarski(k2_tarski(A_20,B_21)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_190,plain,(
    ! [B_49,A_50] : k2_xboole_0(B_49,A_50) = k2_xboole_0(A_50,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_20])).

tff(c_364,plain,(
    ! [A_67,B_68] :
      ( k4_xboole_0(A_67,B_68) = k3_subset_1(A_67,B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_368,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_364])).

tff(c_12,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_378,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_12])).

tff(c_385,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_378])).

tff(c_632,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_591,c_385])).

tff(c_26,plain,(
    ! [A_25,B_26] :
      ( m1_subset_1(k3_subset_1(A_25,B_26),k1_zfmisc_1(A_25))
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_515,plain,(
    ! [A_77,B_78,C_79] :
      ( k4_subset_1(A_77,B_78,C_79) = k2_xboole_0(B_78,C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(A_77))
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_735,plain,(
    ! [A_87,B_88,B_89] :
      ( k4_subset_1(A_87,B_88,k3_subset_1(A_87,B_89)) = k2_xboole_0(B_88,k3_subset_1(A_87,B_89))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_87)) ) ),
    inference(resolution,[status(thm)],[c_26,c_515])).

tff(c_745,plain,(
    ! [B_90] :
      ( k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1',B_90)) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1',B_90))
      | ~ m1_subset_1(B_90,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_34,c_735])).

tff(c_752,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_745])).

tff(c_755,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_632,c_752])).

tff(c_757,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_755])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.36  
% 2.65/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.36  %$ r1_tarski > m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.65/1.36  
% 2.65/1.36  %Foreground sorts:
% 2.65/1.36  
% 2.65/1.36  
% 2.65/1.36  %Background operators:
% 2.65/1.36  
% 2.65/1.36  
% 2.65/1.36  %Foreground operators:
% 2.65/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.65/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.65/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.65/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.65/1.36  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.65/1.36  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.65/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.65/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.65/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.65/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.65/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.65/1.36  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.65/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.36  
% 2.65/1.37  tff(f_49, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.65/1.37  tff(f_72, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 2.65/1.37  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.65/1.37  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.65/1.37  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.65/1.37  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.65/1.37  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.65/1.37  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.65/1.37  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.65/1.37  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.65/1.37  tff(f_47, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.65/1.37  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.65/1.37  tff(f_67, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.65/1.37  tff(c_22, plain, (![A_22]: (k2_subset_1(A_22)=A_22)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.65/1.37  tff(c_32, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.65/1.37  tff(c_35, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_32])).
% 2.65/1.37  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.65/1.37  tff(c_487, plain, (![A_73, B_74]: (k3_subset_1(A_73, k3_subset_1(A_73, B_74))=B_74 | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.65/1.37  tff(c_493, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_34, c_487])).
% 2.65/1.37  tff(c_459, plain, (![A_71, B_72]: (m1_subset_1(k3_subset_1(A_71, B_72), k1_zfmisc_1(A_71)) | ~m1_subset_1(B_72, k1_zfmisc_1(A_71)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.65/1.37  tff(c_24, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=k3_subset_1(A_23, B_24) | ~m1_subset_1(B_24, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.65/1.37  tff(c_567, plain, (![A_83, B_84]: (k4_xboole_0(A_83, k3_subset_1(A_83, B_84))=k3_subset_1(A_83, k3_subset_1(A_83, B_84)) | ~m1_subset_1(B_84, k1_zfmisc_1(A_83)))), inference(resolution, [status(thm)], [c_459, c_24])).
% 2.65/1.37  tff(c_571, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_567])).
% 2.65/1.37  tff(c_574, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_493, c_571])).
% 2.65/1.37  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.65/1.37  tff(c_164, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=A_45 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.65/1.37  tff(c_302, plain, (![A_62, B_63]: (k3_xboole_0(k4_xboole_0(A_62, B_63), A_62)=k4_xboole_0(A_62, B_63))), inference(resolution, [status(thm)], [c_10, c_164])).
% 2.65/1.37  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.65/1.37  tff(c_112, plain, (![A_39, B_40]: (k2_xboole_0(A_39, k3_xboole_0(A_39, B_40))=A_39)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.37  tff(c_121, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k3_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_112])).
% 2.65/1.37  tff(c_314, plain, (![A_62, B_63]: (k2_xboole_0(A_62, k4_xboole_0(A_62, B_63))=A_62)), inference(superposition, [status(thm), theory('equality')], [c_302, c_121])).
% 2.65/1.37  tff(c_591, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_574, c_314])).
% 2.65/1.37  tff(c_14, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.65/1.37  tff(c_169, plain, (![A_47, B_48]: (k3_tarski(k2_tarski(A_47, B_48))=k2_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.65/1.37  tff(c_184, plain, (![B_49, A_50]: (k3_tarski(k2_tarski(B_49, A_50))=k2_xboole_0(A_50, B_49))), inference(superposition, [status(thm), theory('equality')], [c_14, c_169])).
% 2.65/1.37  tff(c_20, plain, (![A_20, B_21]: (k3_tarski(k2_tarski(A_20, B_21))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.65/1.37  tff(c_190, plain, (![B_49, A_50]: (k2_xboole_0(B_49, A_50)=k2_xboole_0(A_50, B_49))), inference(superposition, [status(thm), theory('equality')], [c_184, c_20])).
% 2.65/1.37  tff(c_364, plain, (![A_67, B_68]: (k4_xboole_0(A_67, B_68)=k3_subset_1(A_67, B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.65/1.37  tff(c_368, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_364])).
% 2.65/1.37  tff(c_12, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.65/1.37  tff(c_378, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_368, c_12])).
% 2.65/1.37  tff(c_385, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_378])).
% 2.65/1.37  tff(c_632, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_591, c_385])).
% 2.65/1.37  tff(c_26, plain, (![A_25, B_26]: (m1_subset_1(k3_subset_1(A_25, B_26), k1_zfmisc_1(A_25)) | ~m1_subset_1(B_26, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.65/1.37  tff(c_515, plain, (![A_77, B_78, C_79]: (k4_subset_1(A_77, B_78, C_79)=k2_xboole_0(B_78, C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(A_77)) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.65/1.37  tff(c_735, plain, (![A_87, B_88, B_89]: (k4_subset_1(A_87, B_88, k3_subset_1(A_87, B_89))=k2_xboole_0(B_88, k3_subset_1(A_87, B_89)) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)) | ~m1_subset_1(B_89, k1_zfmisc_1(A_87)))), inference(resolution, [status(thm)], [c_26, c_515])).
% 2.65/1.37  tff(c_745, plain, (![B_90]: (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', B_90))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', B_90)) | ~m1_subset_1(B_90, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_34, c_735])).
% 2.65/1.37  tff(c_752, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_745])).
% 2.65/1.37  tff(c_755, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_632, c_752])).
% 2.65/1.37  tff(c_757, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_755])).
% 2.65/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.37  
% 2.65/1.37  Inference rules
% 2.65/1.37  ----------------------
% 2.65/1.37  #Ref     : 0
% 2.65/1.37  #Sup     : 189
% 2.65/1.37  #Fact    : 0
% 2.65/1.37  #Define  : 0
% 2.65/1.37  #Split   : 0
% 2.65/1.37  #Chain   : 0
% 2.65/1.37  #Close   : 0
% 2.65/1.37  
% 2.65/1.37  Ordering : KBO
% 2.65/1.37  
% 2.65/1.37  Simplification rules
% 2.65/1.37  ----------------------
% 2.65/1.37  #Subsume      : 2
% 2.65/1.37  #Demod        : 81
% 2.65/1.37  #Tautology    : 150
% 2.65/1.37  #SimpNegUnit  : 1
% 2.65/1.37  #BackRed      : 2
% 2.65/1.37  
% 2.65/1.37  #Partial instantiations: 0
% 2.65/1.37  #Strategies tried      : 1
% 2.65/1.37  
% 2.65/1.37  Timing (in seconds)
% 2.65/1.37  ----------------------
% 2.65/1.38  Preprocessing        : 0.30
% 2.65/1.38  Parsing              : 0.16
% 2.65/1.38  CNF conversion       : 0.02
% 2.65/1.38  Main loop            : 0.32
% 2.65/1.38  Inferencing          : 0.12
% 2.65/1.38  Reduction            : 0.11
% 2.65/1.38  Demodulation         : 0.09
% 2.65/1.38  BG Simplification    : 0.02
% 2.65/1.38  Subsumption          : 0.05
% 2.65/1.38  Abstraction          : 0.02
% 2.65/1.38  MUC search           : 0.00
% 2.65/1.38  Cooper               : 0.00
% 2.65/1.38  Total                : 0.65
% 2.65/1.38  Index Insertion      : 0.00
% 2.65/1.38  Index Deletion       : 0.00
% 2.65/1.38  Index Matching       : 0.00
% 2.65/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
