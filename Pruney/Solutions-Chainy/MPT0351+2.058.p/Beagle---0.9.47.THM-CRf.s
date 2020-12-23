%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:44 EST 2020

% Result     : Theorem 6.47s
% Output     : CNFRefutation 6.47s
% Verified   : 
% Statistics : Number of formulae       :   71 (  83 expanded)
%              Number of leaves         :   38 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   68 (  82 expanded)
%              Number of equality atoms :   32 (  43 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_76,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_81,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_61,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_78,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_42,plain,(
    ! [A_48] : k2_subset_1(A_48) = A_48 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_50,plain,(
    k4_subset_1('#skF_1','#skF_2',k2_subset_1('#skF_1')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_53,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_50])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_101,plain,(
    ! [B_60,A_61] : k5_xboole_0(B_60,A_61) = k5_xboole_0(A_61,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_117,plain,(
    ! [A_61] : k5_xboole_0(k1_xboole_0,A_61) = A_61 ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_8])).

tff(c_12,plain,(
    ! [A_11] : k5_xboole_0(A_11,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_439,plain,(
    ! [A_94,B_95,C_96] : k5_xboole_0(k5_xboole_0(A_94,B_95),C_96) = k5_xboole_0(A_94,k5_xboole_0(B_95,C_96)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_492,plain,(
    ! [A_11,C_96] : k5_xboole_0(A_11,k5_xboole_0(A_11,C_96)) = k5_xboole_0(k1_xboole_0,C_96) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_439])).

tff(c_506,plain,(
    ! [A_97,C_98] : k5_xboole_0(A_97,k5_xboole_0(A_97,C_98)) = C_98 ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_492])).

tff(c_546,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_506])).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_46,plain,(
    ! [A_50] : ~ v1_xboole_0(k1_zfmisc_1(A_50)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_277,plain,(
    ! [B_81,A_82] :
      ( r2_hidden(B_81,A_82)
      | ~ m1_subset_1(B_81,A_82)
      | v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_32,plain,(
    ! [A_45] : k3_tarski(k1_zfmisc_1(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_240,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(A_67,k3_tarski(B_68))
      | ~ r2_hidden(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_243,plain,(
    ! [A_67,A_45] :
      ( r1_tarski(A_67,A_45)
      | ~ r2_hidden(A_67,k1_zfmisc_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_240])).

tff(c_284,plain,(
    ! [B_81,A_45] :
      ( r1_tarski(B_81,A_45)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_45))
      | v1_xboole_0(k1_zfmisc_1(A_45)) ) ),
    inference(resolution,[status(thm)],[c_277,c_243])).

tff(c_289,plain,(
    ! [B_83,A_84] :
      ( r1_tarski(B_83,A_84)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_84)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_284])).

tff(c_302,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_289])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_320,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_302,c_6])).

tff(c_645,plain,(
    ! [A_101,B_102] : k5_xboole_0(k5_xboole_0(A_101,B_102),k3_xboole_0(A_101,B_102)) = k2_xboole_0(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_700,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2','#skF_1'),'#skF_2') = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_645])).

tff(c_737,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_546,c_4,c_4,c_700])).

tff(c_44,plain,(
    ! [A_49] : m1_subset_1(k2_subset_1(A_49),k1_zfmisc_1(A_49)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_54,plain,(
    ! [A_49] : m1_subset_1(A_49,k1_zfmisc_1(A_49)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44])).

tff(c_1311,plain,(
    ! [A_130,B_131,C_132] :
      ( k4_subset_1(A_130,B_131,C_132) = k2_xboole_0(B_131,C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(A_130))
      | ~ m1_subset_1(B_131,k1_zfmisc_1(A_130)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8202,plain,(
    ! [A_216,B_217] :
      ( k4_subset_1(A_216,B_217,A_216) = k2_xboole_0(B_217,A_216)
      | ~ m1_subset_1(B_217,k1_zfmisc_1(A_216)) ) ),
    inference(resolution,[status(thm)],[c_54,c_1311])).

tff(c_8209,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_8202])).

tff(c_8214,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_8209])).

tff(c_8216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_8214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:42:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.47/2.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.47/2.52  
% 6.47/2.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.47/2.53  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.47/2.53  
% 6.47/2.53  %Foreground sorts:
% 6.47/2.53  
% 6.47/2.53  
% 6.47/2.53  %Background operators:
% 6.47/2.53  
% 6.47/2.53  
% 6.47/2.53  %Foreground operators:
% 6.47/2.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.47/2.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.47/2.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.47/2.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.47/2.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.47/2.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.47/2.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.47/2.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.47/2.53  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 6.47/2.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.47/2.53  tff('#skF_2', type, '#skF_2': $i).
% 6.47/2.53  tff('#skF_1', type, '#skF_1': $i).
% 6.47/2.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.47/2.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.47/2.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.47/2.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.47/2.53  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.47/2.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.47/2.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.47/2.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.47/2.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.47/2.53  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.47/2.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.47/2.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.47/2.53  
% 6.47/2.54  tff(f_76, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 6.47/2.54  tff(f_92, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 6.47/2.54  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.47/2.54  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 6.47/2.54  tff(f_39, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.47/2.54  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.47/2.54  tff(f_81, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 6.47/2.54  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 6.47/2.54  tff(f_61, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 6.47/2.54  tff(f_57, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 6.47/2.54  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.47/2.54  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 6.47/2.54  tff(f_78, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 6.47/2.54  tff(f_87, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 6.47/2.54  tff(c_42, plain, (![A_48]: (k2_subset_1(A_48)=A_48)), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.47/2.54  tff(c_50, plain, (k4_subset_1('#skF_1', '#skF_2', k2_subset_1('#skF_1'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.47/2.54  tff(c_53, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_50])).
% 6.47/2.54  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.47/2.54  tff(c_101, plain, (![B_60, A_61]: (k5_xboole_0(B_60, A_61)=k5_xboole_0(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.47/2.54  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.47/2.54  tff(c_117, plain, (![A_61]: (k5_xboole_0(k1_xboole_0, A_61)=A_61)), inference(superposition, [status(thm), theory('equality')], [c_101, c_8])).
% 6.47/2.54  tff(c_12, plain, (![A_11]: (k5_xboole_0(A_11, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.47/2.54  tff(c_439, plain, (![A_94, B_95, C_96]: (k5_xboole_0(k5_xboole_0(A_94, B_95), C_96)=k5_xboole_0(A_94, k5_xboole_0(B_95, C_96)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.47/2.54  tff(c_492, plain, (![A_11, C_96]: (k5_xboole_0(A_11, k5_xboole_0(A_11, C_96))=k5_xboole_0(k1_xboole_0, C_96))), inference(superposition, [status(thm), theory('equality')], [c_12, c_439])).
% 6.47/2.54  tff(c_506, plain, (![A_97, C_98]: (k5_xboole_0(A_97, k5_xboole_0(A_97, C_98))=C_98)), inference(demodulation, [status(thm), theory('equality')], [c_117, c_492])).
% 6.47/2.54  tff(c_546, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_506])).
% 6.47/2.54  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.47/2.54  tff(c_46, plain, (![A_50]: (~v1_xboole_0(k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.47/2.54  tff(c_277, plain, (![B_81, A_82]: (r2_hidden(B_81, A_82) | ~m1_subset_1(B_81, A_82) | v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.47/2.54  tff(c_32, plain, (![A_45]: (k3_tarski(k1_zfmisc_1(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.47/2.54  tff(c_240, plain, (![A_67, B_68]: (r1_tarski(A_67, k3_tarski(B_68)) | ~r2_hidden(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.47/2.54  tff(c_243, plain, (![A_67, A_45]: (r1_tarski(A_67, A_45) | ~r2_hidden(A_67, k1_zfmisc_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_240])).
% 6.47/2.54  tff(c_284, plain, (![B_81, A_45]: (r1_tarski(B_81, A_45) | ~m1_subset_1(B_81, k1_zfmisc_1(A_45)) | v1_xboole_0(k1_zfmisc_1(A_45)))), inference(resolution, [status(thm)], [c_277, c_243])).
% 6.47/2.54  tff(c_289, plain, (![B_83, A_84]: (r1_tarski(B_83, A_84) | ~m1_subset_1(B_83, k1_zfmisc_1(A_84)))), inference(negUnitSimplification, [status(thm)], [c_46, c_284])).
% 6.47/2.54  tff(c_302, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_289])).
% 6.47/2.54  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.47/2.54  tff(c_320, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_302, c_6])).
% 6.47/2.54  tff(c_645, plain, (![A_101, B_102]: (k5_xboole_0(k5_xboole_0(A_101, B_102), k3_xboole_0(A_101, B_102))=k2_xboole_0(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.47/2.54  tff(c_700, plain, (k5_xboole_0(k5_xboole_0('#skF_2', '#skF_1'), '#skF_2')=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_320, c_645])).
% 6.47/2.54  tff(c_737, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_546, c_4, c_4, c_700])).
% 6.47/2.54  tff(c_44, plain, (![A_49]: (m1_subset_1(k2_subset_1(A_49), k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.47/2.54  tff(c_54, plain, (![A_49]: (m1_subset_1(A_49, k1_zfmisc_1(A_49)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44])).
% 6.47/2.54  tff(c_1311, plain, (![A_130, B_131, C_132]: (k4_subset_1(A_130, B_131, C_132)=k2_xboole_0(B_131, C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(A_130)) | ~m1_subset_1(B_131, k1_zfmisc_1(A_130)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.47/2.54  tff(c_8202, plain, (![A_216, B_217]: (k4_subset_1(A_216, B_217, A_216)=k2_xboole_0(B_217, A_216) | ~m1_subset_1(B_217, k1_zfmisc_1(A_216)))), inference(resolution, [status(thm)], [c_54, c_1311])).
% 6.47/2.54  tff(c_8209, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_8202])).
% 6.47/2.54  tff(c_8214, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_737, c_8209])).
% 6.47/2.54  tff(c_8216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_8214])).
% 6.47/2.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.47/2.54  
% 6.47/2.54  Inference rules
% 6.47/2.54  ----------------------
% 6.47/2.54  #Ref     : 0
% 6.47/2.54  #Sup     : 1996
% 6.47/2.54  #Fact    : 0
% 6.47/2.54  #Define  : 0
% 6.47/2.54  #Split   : 0
% 6.47/2.54  #Chain   : 0
% 6.47/2.54  #Close   : 0
% 6.47/2.54  
% 6.47/2.54  Ordering : KBO
% 6.47/2.54  
% 6.47/2.54  Simplification rules
% 6.47/2.54  ----------------------
% 6.47/2.54  #Subsume      : 159
% 6.47/2.54  #Demod        : 1931
% 6.47/2.54  #Tautology    : 1117
% 6.47/2.54  #SimpNegUnit  : 6
% 6.47/2.54  #BackRed      : 0
% 6.47/2.54  
% 6.47/2.54  #Partial instantiations: 0
% 6.47/2.54  #Strategies tried      : 1
% 6.47/2.54  
% 6.47/2.54  Timing (in seconds)
% 6.47/2.54  ----------------------
% 6.47/2.54  Preprocessing        : 0.34
% 6.47/2.54  Parsing              : 0.19
% 6.47/2.54  CNF conversion       : 0.02
% 6.47/2.54  Main loop            : 1.42
% 6.47/2.54  Inferencing          : 0.37
% 6.47/2.54  Reduction            : 0.73
% 6.47/2.54  Demodulation         : 0.64
% 6.47/2.54  BG Simplification    : 0.05
% 6.47/2.54  Subsumption          : 0.20
% 6.47/2.54  Abstraction          : 0.07
% 6.47/2.54  MUC search           : 0.00
% 6.47/2.54  Cooper               : 0.00
% 6.47/2.54  Total                : 1.80
% 6.47/2.54  Index Insertion      : 0.00
% 6.47/2.54  Index Deletion       : 0.00
% 6.47/2.54  Index Matching       : 0.00
% 6.47/2.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
