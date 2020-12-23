%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:27 EST 2020

% Result     : Theorem 5.08s
% Output     : CNFRefutation 5.16s
% Verified   : 
% Statistics : Number of formulae       :   77 (  86 expanded)
%              Number of leaves         :   38 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :   80 (  95 expanded)
%              Number of equality atoms :   43 (  48 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_58,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_50,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_56,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_32,plain,(
    ! [A_29] : k2_subset_1(A_29) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_42,plain,(
    k4_subset_1('#skF_2','#skF_3',k3_subset_1('#skF_2','#skF_3')) != k2_subset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_45,plain,(
    k4_subset_1('#skF_2','#skF_3',k3_subset_1('#skF_2','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_42])).

tff(c_24,plain,(
    ! [B_21,A_20] : k2_tarski(B_21,A_20) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_145,plain,(
    ! [A_53,B_54] : k3_tarski(k2_tarski(A_53,B_54)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_160,plain,(
    ! [B_55,A_56] : k3_tarski(k2_tarski(B_55,A_56)) = k2_xboole_0(A_56,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_145])).

tff(c_30,plain,(
    ! [A_27,B_28] : k3_tarski(k2_tarski(A_27,B_28)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_166,plain,(
    ! [B_55,A_56] : k2_xboole_0(B_55,A_56) = k2_xboole_0(A_56,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_30])).

tff(c_18,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_482,plain,(
    ! [C_86,A_87,B_88] :
      ( r2_hidden(C_86,A_87)
      | ~ r2_hidden(C_86,B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2934,plain,(
    ! [A_138,B_139,A_140] :
      ( r2_hidden('#skF_1'(A_138,B_139),A_140)
      | ~ m1_subset_1(A_138,k1_zfmisc_1(A_140))
      | r1_tarski(A_138,B_139) ) ),
    inference(resolution,[status(thm)],[c_8,c_482])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2946,plain,(
    ! [A_141,A_142] :
      ( ~ m1_subset_1(A_141,k1_zfmisc_1(A_142))
      | r1_tarski(A_141,A_142) ) ),
    inference(resolution,[status(thm)],[c_2934,c_6])).

tff(c_2954,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_2946])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = k1_xboole_0
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2958,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2954,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_217,plain,(
    ! [A_59,B_60] : k5_xboole_0(A_59,k3_xboole_0(A_59,B_60)) = k4_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_226,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_217])).

tff(c_491,plain,(
    ! [A_91,B_92] : k5_xboole_0(k5_xboole_0(A_91,B_92),k3_xboole_0(A_91,B_92)) = k2_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] : k5_xboole_0(k5_xboole_0(A_15,B_16),C_17) = k5_xboole_0(A_15,k5_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_503,plain,(
    ! [A_91,B_92] : k5_xboole_0(A_91,k5_xboole_0(B_92,k3_xboole_0(A_91,B_92))) = k2_xboole_0(A_91,B_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_20])).

tff(c_537,plain,(
    ! [A_91,B_92] : k5_xboole_0(A_91,k4_xboole_0(B_92,A_91)) = k2_xboole_0(A_91,B_92) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_503])).

tff(c_2962,plain,(
    k5_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2958,c_537])).

tff(c_2968,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_18,c_2962])).

tff(c_466,plain,(
    ! [A_84,B_85] :
      ( k4_xboole_0(A_84,B_85) = k3_subset_1(A_84,B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_470,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k3_subset_1('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_466])).

tff(c_16,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_474,plain,(
    k2_xboole_0('#skF_3',k3_subset_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_16])).

tff(c_2975,plain,(
    k2_xboole_0('#skF_3',k3_subset_1('#skF_2','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2968,c_474])).

tff(c_36,plain,(
    ! [A_32,B_33] :
      ( m1_subset_1(k3_subset_1(A_32,B_33),k1_zfmisc_1(A_32))
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_691,plain,(
    ! [A_98,B_99,C_100] :
      ( k4_subset_1(A_98,B_99,C_100) = k2_xboole_0(B_99,C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(A_98))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_4964,plain,(
    ! [A_173,B_174,B_175] :
      ( k4_subset_1(A_173,B_174,k3_subset_1(A_173,B_175)) = k2_xboole_0(B_174,k3_subset_1(A_173,B_175))
      | ~ m1_subset_1(B_174,k1_zfmisc_1(A_173))
      | ~ m1_subset_1(B_175,k1_zfmisc_1(A_173)) ) ),
    inference(resolution,[status(thm)],[c_36,c_691])).

tff(c_5064,plain,(
    ! [B_176] :
      ( k4_subset_1('#skF_2','#skF_3',k3_subset_1('#skF_2',B_176)) = k2_xboole_0('#skF_3',k3_subset_1('#skF_2',B_176))
      | ~ m1_subset_1(B_176,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_44,c_4964])).

tff(c_5071,plain,(
    k4_subset_1('#skF_2','#skF_3',k3_subset_1('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k3_subset_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_5064])).

tff(c_5074,plain,(
    k4_subset_1('#skF_2','#skF_3',k3_subset_1('#skF_2','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2975,c_5071])).

tff(c_5076,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_5074])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:29:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.08/2.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.08/2.14  
% 5.08/2.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.08/2.14  %$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.08/2.14  
% 5.08/2.14  %Foreground sorts:
% 5.08/2.14  
% 5.08/2.14  
% 5.08/2.14  %Background operators:
% 5.08/2.14  
% 5.08/2.14  
% 5.08/2.14  %Foreground operators:
% 5.08/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.08/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.08/2.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.08/2.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.08/2.14  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.08/2.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.08/2.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.08/2.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.08/2.14  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.08/2.14  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.08/2.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.08/2.14  tff('#skF_2', type, '#skF_2': $i).
% 5.08/2.14  tff('#skF_3', type, '#skF_3': $i).
% 5.08/2.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.08/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.08/2.14  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.08/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.08/2.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.08/2.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.08/2.14  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.08/2.14  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.08/2.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.08/2.14  
% 5.16/2.15  tff(f_58, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.16/2.15  tff(f_84, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 5.16/2.15  tff(f_50, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.16/2.15  tff(f_56, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.16/2.15  tff(f_44, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 5.16/2.15  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.16/2.15  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 5.16/2.15  tff(f_38, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.16/2.15  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.16/2.15  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.16/2.15  tff(f_48, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 5.16/2.15  tff(f_46, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.16/2.15  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.16/2.15  tff(f_42, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.16/2.15  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.16/2.15  tff(f_79, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.16/2.15  tff(c_32, plain, (![A_29]: (k2_subset_1(A_29)=A_29)), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.16/2.15  tff(c_42, plain, (k4_subset_1('#skF_2', '#skF_3', k3_subset_1('#skF_2', '#skF_3'))!=k2_subset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.16/2.15  tff(c_45, plain, (k4_subset_1('#skF_2', '#skF_3', k3_subset_1('#skF_2', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_42])).
% 5.16/2.15  tff(c_24, plain, (![B_21, A_20]: (k2_tarski(B_21, A_20)=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.16/2.15  tff(c_145, plain, (![A_53, B_54]: (k3_tarski(k2_tarski(A_53, B_54))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.16/2.15  tff(c_160, plain, (![B_55, A_56]: (k3_tarski(k2_tarski(B_55, A_56))=k2_xboole_0(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_24, c_145])).
% 5.16/2.15  tff(c_30, plain, (![A_27, B_28]: (k3_tarski(k2_tarski(A_27, B_28))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.16/2.15  tff(c_166, plain, (![B_55, A_56]: (k2_xboole_0(B_55, A_56)=k2_xboole_0(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_160, c_30])).
% 5.16/2.15  tff(c_18, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.16/2.15  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.16/2.15  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.16/2.15  tff(c_482, plain, (![C_86, A_87, B_88]: (r2_hidden(C_86, A_87) | ~r2_hidden(C_86, B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.16/2.15  tff(c_2934, plain, (![A_138, B_139, A_140]: (r2_hidden('#skF_1'(A_138, B_139), A_140) | ~m1_subset_1(A_138, k1_zfmisc_1(A_140)) | r1_tarski(A_138, B_139))), inference(resolution, [status(thm)], [c_8, c_482])).
% 5.16/2.15  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 5.16/2.15  tff(c_2946, plain, (![A_141, A_142]: (~m1_subset_1(A_141, k1_zfmisc_1(A_142)) | r1_tarski(A_141, A_142))), inference(resolution, [status(thm)], [c_2934, c_6])).
% 5.16/2.15  tff(c_2954, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_2946])).
% 5.16/2.15  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=k1_xboole_0 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.16/2.15  tff(c_2958, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_2954, c_12])).
% 5.16/2.15  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.16/2.15  tff(c_217, plain, (![A_59, B_60]: (k5_xboole_0(A_59, k3_xboole_0(A_59, B_60))=k4_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.16/2.15  tff(c_226, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_217])).
% 5.16/2.15  tff(c_491, plain, (![A_91, B_92]: (k5_xboole_0(k5_xboole_0(A_91, B_92), k3_xboole_0(A_91, B_92))=k2_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.16/2.15  tff(c_20, plain, (![A_15, B_16, C_17]: (k5_xboole_0(k5_xboole_0(A_15, B_16), C_17)=k5_xboole_0(A_15, k5_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.16/2.15  tff(c_503, plain, (![A_91, B_92]: (k5_xboole_0(A_91, k5_xboole_0(B_92, k3_xboole_0(A_91, B_92)))=k2_xboole_0(A_91, B_92))), inference(superposition, [status(thm), theory('equality')], [c_491, c_20])).
% 5.16/2.15  tff(c_537, plain, (![A_91, B_92]: (k5_xboole_0(A_91, k4_xboole_0(B_92, A_91))=k2_xboole_0(A_91, B_92))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_503])).
% 5.16/2.15  tff(c_2962, plain, (k5_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2958, c_537])).
% 5.16/2.15  tff(c_2968, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_18, c_2962])).
% 5.16/2.15  tff(c_466, plain, (![A_84, B_85]: (k4_xboole_0(A_84, B_85)=k3_subset_1(A_84, B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.16/2.15  tff(c_470, plain, (k4_xboole_0('#skF_2', '#skF_3')=k3_subset_1('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_466])).
% 5.16/2.15  tff(c_16, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.16/2.15  tff(c_474, plain, (k2_xboole_0('#skF_3', k3_subset_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_470, c_16])).
% 5.16/2.15  tff(c_2975, plain, (k2_xboole_0('#skF_3', k3_subset_1('#skF_2', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2968, c_474])).
% 5.16/2.15  tff(c_36, plain, (![A_32, B_33]: (m1_subset_1(k3_subset_1(A_32, B_33), k1_zfmisc_1(A_32)) | ~m1_subset_1(B_33, k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.16/2.15  tff(c_691, plain, (![A_98, B_99, C_100]: (k4_subset_1(A_98, B_99, C_100)=k2_xboole_0(B_99, C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(A_98)) | ~m1_subset_1(B_99, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.16/2.15  tff(c_4964, plain, (![A_173, B_174, B_175]: (k4_subset_1(A_173, B_174, k3_subset_1(A_173, B_175))=k2_xboole_0(B_174, k3_subset_1(A_173, B_175)) | ~m1_subset_1(B_174, k1_zfmisc_1(A_173)) | ~m1_subset_1(B_175, k1_zfmisc_1(A_173)))), inference(resolution, [status(thm)], [c_36, c_691])).
% 5.16/2.15  tff(c_5064, plain, (![B_176]: (k4_subset_1('#skF_2', '#skF_3', k3_subset_1('#skF_2', B_176))=k2_xboole_0('#skF_3', k3_subset_1('#skF_2', B_176)) | ~m1_subset_1(B_176, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_44, c_4964])).
% 5.16/2.15  tff(c_5071, plain, (k4_subset_1('#skF_2', '#skF_3', k3_subset_1('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k3_subset_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_5064])).
% 5.16/2.15  tff(c_5074, plain, (k4_subset_1('#skF_2', '#skF_3', k3_subset_1('#skF_2', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2975, c_5071])).
% 5.16/2.15  tff(c_5076, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_5074])).
% 5.16/2.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.16/2.15  
% 5.16/2.15  Inference rules
% 5.16/2.15  ----------------------
% 5.16/2.15  #Ref     : 0
% 5.16/2.15  #Sup     : 1201
% 5.16/2.15  #Fact    : 0
% 5.16/2.15  #Define  : 0
% 5.16/2.15  #Split   : 0
% 5.16/2.15  #Chain   : 0
% 5.16/2.15  #Close   : 0
% 5.16/2.15  
% 5.16/2.15  Ordering : KBO
% 5.16/2.15  
% 5.16/2.15  Simplification rules
% 5.16/2.15  ----------------------
% 5.16/2.15  #Subsume      : 20
% 5.16/2.15  #Demod        : 1478
% 5.16/2.15  #Tautology    : 701
% 5.16/2.15  #SimpNegUnit  : 1
% 5.16/2.15  #BackRed      : 38
% 5.16/2.15  
% 5.16/2.15  #Partial instantiations: 0
% 5.16/2.15  #Strategies tried      : 1
% 5.16/2.15  
% 5.16/2.15  Timing (in seconds)
% 5.16/2.15  ----------------------
% 5.16/2.16  Preprocessing        : 0.32
% 5.16/2.16  Parsing              : 0.17
% 5.16/2.16  CNF conversion       : 0.02
% 5.16/2.16  Main loop            : 0.97
% 5.16/2.16  Inferencing          : 0.29
% 5.16/2.16  Reduction            : 0.47
% 5.16/2.16  Demodulation         : 0.40
% 5.16/2.16  BG Simplification    : 0.04
% 5.16/2.16  Subsumption          : 0.12
% 5.16/2.16  Abstraction          : 0.05
% 5.16/2.16  MUC search           : 0.00
% 5.16/2.16  Cooper               : 0.00
% 5.16/2.16  Total                : 1.32
% 5.16/2.16  Index Insertion      : 0.00
% 5.16/2.16  Index Deletion       : 0.00
% 5.16/2.16  Index Matching       : 0.00
% 5.16/2.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
