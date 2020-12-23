%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:26 EST 2020

% Result     : Theorem 6.35s
% Output     : CNFRefutation 6.35s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 117 expanded)
%              Number of leaves         :   41 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :   89 ( 130 expanded)
%              Number of equality atoms :   47 (  72 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_58,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_84,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_46,plain,(
    ! [A_31] : k2_subset_1(A_31) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_56,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_59,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_56])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_164,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = A_51
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_169,plain,(
    ! [A_53] : k3_xboole_0(k1_xboole_0,A_53) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_164])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_174,plain,(
    ! [A_53] : k3_xboole_0(A_53,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_2])).

tff(c_383,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_395,plain,(
    ! [A_53] : k5_xboole_0(A_53,k1_xboole_0) = k4_xboole_0(A_53,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_383])).

tff(c_408,plain,(
    ! [A_53] : k4_xboole_0(A_53,k1_xboole_0) = A_53 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_395])).

tff(c_431,plain,(
    ! [A_82] : k4_xboole_0(A_82,k1_xboole_0) = A_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_395])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_441,plain,(
    ! [A_82] : k4_xboole_0(A_82,A_82) = k3_xboole_0(A_82,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_10])).

tff(c_451,plain,(
    ! [A_82] : k4_xboole_0(A_82,A_82) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_441])).

tff(c_18,plain,(
    ! [B_16,A_15] : k2_tarski(B_16,A_15) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_231,plain,(
    ! [A_57,B_58] : k3_tarski(k2_tarski(A_57,B_58)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_265,plain,(
    ! [A_65,B_66] : k3_tarski(k2_tarski(A_65,B_66)) = k2_xboole_0(B_66,A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_231])).

tff(c_36,plain,(
    ! [A_27,B_28] : k3_tarski(k2_tarski(A_27,B_28)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_271,plain,(
    ! [B_66,A_65] : k2_xboole_0(B_66,A_65) = k2_xboole_0(A_65,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_36])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_52,plain,(
    ! [A_36] : ~ v1_xboole_0(k1_zfmisc_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_322,plain,(
    ! [B_69,A_70] :
      ( r2_hidden(B_69,A_70)
      | ~ m1_subset_1(B_69,A_70)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    ! [C_26,A_22] :
      ( r1_tarski(C_26,A_22)
      | ~ r2_hidden(C_26,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_326,plain,(
    ! [B_69,A_22] :
      ( r1_tarski(B_69,A_22)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_22))
      | v1_xboole_0(k1_zfmisc_1(A_22)) ) ),
    inference(resolution,[status(thm)],[c_322,c_24])).

tff(c_330,plain,(
    ! [B_71,A_72] :
      ( r1_tarski(B_71,A_72)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_326])).

tff(c_339,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_330])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_343,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_339,c_6])).

tff(c_595,plain,(
    ! [A_94,B_95] :
      ( k4_xboole_0(A_94,B_95) = k3_subset_1(A_94,B_95)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_612,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_595])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] : k2_xboole_0(k4_xboole_0(A_10,B_11),k3_xboole_0(A_10,C_12)) = k4_xboole_0(A_10,k4_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_691,plain,(
    ! [C_99] : k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),k3_xboole_0('#skF_3',C_99)) = k4_xboole_0('#skF_3',k4_xboole_0('#skF_4',C_99)) ),
    inference(superposition,[status(thm),theory(equality)],[c_612,c_12])).

tff(c_868,plain,(
    ! [B_107] : k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),k3_xboole_0(B_107,'#skF_3')) = k4_xboole_0('#skF_3',k4_xboole_0('#skF_4',B_107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_691])).

tff(c_897,plain,(
    k4_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_4')) = k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_343,c_868])).

tff(c_915,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_451,c_271,c_897])).

tff(c_50,plain,(
    ! [A_34,B_35] :
      ( m1_subset_1(k3_subset_1(A_34,B_35),k1_zfmisc_1(A_34))
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1308,plain,(
    ! [A_125,B_126,C_127] :
      ( k4_subset_1(A_125,B_126,C_127) = k2_xboole_0(B_126,C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(A_125))
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6833,plain,(
    ! [A_217,B_218,B_219] :
      ( k4_subset_1(A_217,B_218,k3_subset_1(A_217,B_219)) = k2_xboole_0(B_218,k3_subset_1(A_217,B_219))
      | ~ m1_subset_1(B_218,k1_zfmisc_1(A_217))
      | ~ m1_subset_1(B_219,k1_zfmisc_1(A_217)) ) ),
    inference(resolution,[status(thm)],[c_50,c_1308])).

tff(c_7007,plain,(
    ! [B_222] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_222)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_222))
      | ~ m1_subset_1(B_222,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_58,c_6833])).

tff(c_7034,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_58,c_7007])).

tff(c_7046,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_7034])).

tff(c_7048,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_7046])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:11:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.35/2.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.35/2.31  
% 6.35/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.35/2.31  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 6.35/2.31  
% 6.35/2.31  %Foreground sorts:
% 6.35/2.31  
% 6.35/2.31  
% 6.35/2.31  %Background operators:
% 6.35/2.31  
% 6.35/2.31  
% 6.35/2.31  %Foreground operators:
% 6.35/2.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.35/2.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.35/2.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.35/2.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.35/2.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.35/2.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.35/2.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.35/2.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.35/2.31  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.35/2.31  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 6.35/2.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.35/2.31  tff('#skF_3', type, '#skF_3': $i).
% 6.35/2.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.35/2.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.35/2.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.35/2.31  tff('#skF_4', type, '#skF_4': $i).
% 6.35/2.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.35/2.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.35/2.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.35/2.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.35/2.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.35/2.31  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 6.35/2.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.35/2.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.35/2.31  
% 6.35/2.33  tff(f_73, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 6.35/2.33  tff(f_95, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 6.35/2.33  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 6.35/2.33  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.35/2.33  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.35/2.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.35/2.33  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.35/2.33  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.35/2.33  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.35/2.33  tff(f_58, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.35/2.33  tff(f_84, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 6.35/2.33  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 6.35/2.33  tff(f_56, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 6.35/2.33  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 6.35/2.33  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 6.35/2.33  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 6.35/2.33  tff(f_90, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 6.35/2.33  tff(c_46, plain, (![A_31]: (k2_subset_1(A_31)=A_31)), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.35/2.33  tff(c_56, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.35/2.33  tff(c_59, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_56])).
% 6.35/2.33  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.35/2.33  tff(c_8, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.35/2.33  tff(c_164, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=A_51 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.35/2.33  tff(c_169, plain, (![A_53]: (k3_xboole_0(k1_xboole_0, A_53)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_164])).
% 6.35/2.33  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.35/2.33  tff(c_174, plain, (![A_53]: (k3_xboole_0(A_53, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_169, c_2])).
% 6.35/2.33  tff(c_383, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.35/2.33  tff(c_395, plain, (![A_53]: (k5_xboole_0(A_53, k1_xboole_0)=k4_xboole_0(A_53, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_174, c_383])).
% 6.35/2.33  tff(c_408, plain, (![A_53]: (k4_xboole_0(A_53, k1_xboole_0)=A_53)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_395])).
% 6.35/2.33  tff(c_431, plain, (![A_82]: (k4_xboole_0(A_82, k1_xboole_0)=A_82)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_395])).
% 6.35/2.33  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.35/2.33  tff(c_441, plain, (![A_82]: (k4_xboole_0(A_82, A_82)=k3_xboole_0(A_82, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_431, c_10])).
% 6.35/2.33  tff(c_451, plain, (![A_82]: (k4_xboole_0(A_82, A_82)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_174, c_441])).
% 6.35/2.33  tff(c_18, plain, (![B_16, A_15]: (k2_tarski(B_16, A_15)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.35/2.33  tff(c_231, plain, (![A_57, B_58]: (k3_tarski(k2_tarski(A_57, B_58))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.35/2.33  tff(c_265, plain, (![A_65, B_66]: (k3_tarski(k2_tarski(A_65, B_66))=k2_xboole_0(B_66, A_65))), inference(superposition, [status(thm), theory('equality')], [c_18, c_231])).
% 6.35/2.33  tff(c_36, plain, (![A_27, B_28]: (k3_tarski(k2_tarski(A_27, B_28))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.35/2.33  tff(c_271, plain, (![B_66, A_65]: (k2_xboole_0(B_66, A_65)=k2_xboole_0(A_65, B_66))), inference(superposition, [status(thm), theory('equality')], [c_265, c_36])).
% 6.35/2.33  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.35/2.33  tff(c_52, plain, (![A_36]: (~v1_xboole_0(k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.35/2.33  tff(c_322, plain, (![B_69, A_70]: (r2_hidden(B_69, A_70) | ~m1_subset_1(B_69, A_70) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.35/2.33  tff(c_24, plain, (![C_26, A_22]: (r1_tarski(C_26, A_22) | ~r2_hidden(C_26, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.35/2.33  tff(c_326, plain, (![B_69, A_22]: (r1_tarski(B_69, A_22) | ~m1_subset_1(B_69, k1_zfmisc_1(A_22)) | v1_xboole_0(k1_zfmisc_1(A_22)))), inference(resolution, [status(thm)], [c_322, c_24])).
% 6.35/2.33  tff(c_330, plain, (![B_71, A_72]: (r1_tarski(B_71, A_72) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)))), inference(negUnitSimplification, [status(thm)], [c_52, c_326])).
% 6.35/2.33  tff(c_339, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_330])).
% 6.35/2.33  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.35/2.33  tff(c_343, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_339, c_6])).
% 6.35/2.33  tff(c_595, plain, (![A_94, B_95]: (k4_xboole_0(A_94, B_95)=k3_subset_1(A_94, B_95) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.35/2.33  tff(c_612, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_595])).
% 6.35/2.33  tff(c_12, plain, (![A_10, B_11, C_12]: (k2_xboole_0(k4_xboole_0(A_10, B_11), k3_xboole_0(A_10, C_12))=k4_xboole_0(A_10, k4_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.35/2.33  tff(c_691, plain, (![C_99]: (k2_xboole_0(k3_subset_1('#skF_3', '#skF_4'), k3_xboole_0('#skF_3', C_99))=k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', C_99)))), inference(superposition, [status(thm), theory('equality')], [c_612, c_12])).
% 6.35/2.33  tff(c_868, plain, (![B_107]: (k2_xboole_0(k3_subset_1('#skF_3', '#skF_4'), k3_xboole_0(B_107, '#skF_3'))=k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', B_107)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_691])).
% 6.35/2.33  tff(c_897, plain, (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_4'))=k2_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_343, c_868])).
% 6.35/2.33  tff(c_915, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_408, c_451, c_271, c_897])).
% 6.35/2.33  tff(c_50, plain, (![A_34, B_35]: (m1_subset_1(k3_subset_1(A_34, B_35), k1_zfmisc_1(A_34)) | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.35/2.33  tff(c_1308, plain, (![A_125, B_126, C_127]: (k4_subset_1(A_125, B_126, C_127)=k2_xboole_0(B_126, C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(A_125)) | ~m1_subset_1(B_126, k1_zfmisc_1(A_125)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.35/2.33  tff(c_6833, plain, (![A_217, B_218, B_219]: (k4_subset_1(A_217, B_218, k3_subset_1(A_217, B_219))=k2_xboole_0(B_218, k3_subset_1(A_217, B_219)) | ~m1_subset_1(B_218, k1_zfmisc_1(A_217)) | ~m1_subset_1(B_219, k1_zfmisc_1(A_217)))), inference(resolution, [status(thm)], [c_50, c_1308])).
% 6.35/2.33  tff(c_7007, plain, (![B_222]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_222))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_222)) | ~m1_subset_1(B_222, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_58, c_6833])).
% 6.35/2.33  tff(c_7034, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_58, c_7007])).
% 6.35/2.33  tff(c_7046, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_915, c_7034])).
% 6.35/2.33  tff(c_7048, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_7046])).
% 6.35/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.35/2.33  
% 6.35/2.33  Inference rules
% 6.35/2.33  ----------------------
% 6.35/2.33  #Ref     : 0
% 6.35/2.33  #Sup     : 1733
% 6.35/2.33  #Fact    : 0
% 6.35/2.33  #Define  : 0
% 6.35/2.33  #Split   : 0
% 6.35/2.33  #Chain   : 0
% 6.35/2.33  #Close   : 0
% 6.35/2.33  
% 6.35/2.33  Ordering : KBO
% 6.35/2.33  
% 6.35/2.33  Simplification rules
% 6.35/2.33  ----------------------
% 6.35/2.33  #Subsume      : 22
% 6.35/2.33  #Demod        : 1953
% 6.35/2.33  #Tautology    : 1126
% 6.35/2.33  #SimpNegUnit  : 15
% 6.35/2.33  #BackRed      : 8
% 6.35/2.33  
% 6.35/2.33  #Partial instantiations: 0
% 6.35/2.33  #Strategies tried      : 1
% 6.35/2.33  
% 6.35/2.33  Timing (in seconds)
% 6.35/2.33  ----------------------
% 6.35/2.33  Preprocessing        : 0.33
% 6.35/2.33  Parsing              : 0.17
% 6.35/2.33  CNF conversion       : 0.02
% 6.35/2.33  Main loop            : 1.24
% 6.35/2.33  Inferencing          : 0.34
% 6.35/2.33  Reduction            : 0.61
% 6.35/2.33  Demodulation         : 0.52
% 6.35/2.33  BG Simplification    : 0.04
% 6.35/2.33  Subsumption          : 0.18
% 6.35/2.33  Abstraction          : 0.05
% 6.35/2.33  MUC search           : 0.00
% 6.35/2.33  Cooper               : 0.00
% 6.35/2.33  Total                : 1.60
% 6.35/2.33  Index Insertion      : 0.00
% 6.35/2.33  Index Deletion       : 0.00
% 6.35/2.33  Index Matching       : 0.00
% 6.35/2.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
