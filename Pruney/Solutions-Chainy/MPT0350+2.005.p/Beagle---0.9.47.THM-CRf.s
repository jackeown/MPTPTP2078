%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:26 EST 2020

% Result     : Theorem 8.39s
% Output     : CNFRefutation 8.44s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 155 expanded)
%              Number of leaves         :   42 (  68 expanded)
%              Depth                    :   16
%              Number of atoms          :   99 ( 208 expanded)
%              Number of equality atoms :   57 (  87 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_92,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

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

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_58,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

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
    ! [A_32] : k2_subset_1(A_32) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_58,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_61,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_58])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_56,plain,(
    ! [A_41] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_41)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_52,plain,(
    ! [A_37] : ~ v1_xboole_0(k1_zfmisc_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_346,plain,(
    ! [B_80,A_81] :
      ( r2_hidden(B_80,A_81)
      | ~ m1_subset_1(B_80,A_81)
      | v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    ! [C_27,A_23] :
      ( r1_tarski(C_27,A_23)
      | ~ r2_hidden(C_27,k1_zfmisc_1(A_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_353,plain,(
    ! [B_80,A_23] :
      ( r1_tarski(B_80,A_23)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_23))
      | v1_xboole_0(k1_zfmisc_1(A_23)) ) ),
    inference(resolution,[status(thm)],[c_346,c_24])).

tff(c_395,plain,(
    ! [B_84,A_85] :
      ( r1_tarski(B_84,A_85)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_85)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_353])).

tff(c_413,plain,(
    ! [A_86] : r1_tarski(k1_xboole_0,A_86) ),
    inference(resolution,[status(thm)],[c_56,c_395])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_422,plain,(
    ! [A_87] : k3_xboole_0(k1_xboole_0,A_87) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_413,c_8])).

tff(c_515,plain,(
    ! [A_91] : k3_xboole_0(A_91,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_422])).

tff(c_18,plain,(
    ! [A_17,B_18] : k5_xboole_0(k5_xboole_0(A_17,B_18),k3_xboole_0(A_17,B_18)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_523,plain,(
    ! [A_91] : k5_xboole_0(k5_xboole_0(A_91,k1_xboole_0),k1_xboole_0) = k2_xboole_0(A_91,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_18])).

tff(c_556,plain,(
    ! [A_91] : k2_xboole_0(A_91,k1_xboole_0) = A_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_523])).

tff(c_20,plain,(
    ! [B_20,A_19] : k2_tarski(B_20,A_19) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_168,plain,(
    ! [A_57,B_58] : k3_tarski(k2_tarski(A_57,B_58)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_202,plain,(
    ! [A_65,B_66] : k3_tarski(k2_tarski(A_65,B_66)) = k2_xboole_0(B_66,A_65) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_168])).

tff(c_36,plain,(
    ! [A_28,B_29] : k3_tarski(k2_tarski(A_28,B_29)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_208,plain,(
    ! [B_66,A_65] : k2_xboole_0(B_66,A_65) = k2_xboole_0(A_65,B_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_36])).

tff(c_450,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_422])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_526,plain,(
    ! [A_91] : k5_xboole_0(A_91,k1_xboole_0) = k4_xboole_0(A_91,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_6])).

tff(c_603,plain,(
    ! [A_93] : k4_xboole_0(A_93,k1_xboole_0) = A_93 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_526])).

tff(c_12,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_616,plain,(
    ! [A_93] : k4_xboole_0(A_93,A_93) = k3_xboole_0(A_93,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_12])).

tff(c_627,plain,(
    ! [A_93] : k4_xboole_0(A_93,A_93) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_450,c_616])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_271,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(A_73,B_74)) = k4_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_286,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_271])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_412,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_395])).

tff(c_421,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_412,c_8])).

tff(c_466,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_6])).

tff(c_469,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k4_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_466])).

tff(c_943,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_469])).

tff(c_10,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_947,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_943,c_10])).

tff(c_953,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_208,c_947])).

tff(c_471,plain,(
    ! [A_88,B_89] :
      ( k4_xboole_0(A_88,B_89) = k3_subset_1(A_88,B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_488,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_471])).

tff(c_570,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_10])).

tff(c_957,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_953,c_570])).

tff(c_50,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(k3_subset_1(A_35,B_36),k1_zfmisc_1(A_35))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2218,plain,(
    ! [A_132,B_133,C_134] :
      ( k4_subset_1(A_132,B_133,C_134) = k2_xboole_0(B_133,C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(A_132))
      | ~ m1_subset_1(B_133,k1_zfmisc_1(A_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_12292,plain,(
    ! [A_275,B_276,B_277] :
      ( k4_subset_1(A_275,B_276,k3_subset_1(A_275,B_277)) = k2_xboole_0(B_276,k3_subset_1(A_275,B_277))
      | ~ m1_subset_1(B_276,k1_zfmisc_1(A_275))
      | ~ m1_subset_1(B_277,k1_zfmisc_1(A_275)) ) ),
    inference(resolution,[status(thm)],[c_50,c_2218])).

tff(c_12328,plain,(
    ! [B_278] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_278)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_278))
      | ~ m1_subset_1(B_278,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_60,c_12292])).

tff(c_12359,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_60,c_12328])).

tff(c_12375,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_957,c_12359])).

tff(c_12377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_12375])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:44:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.39/3.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.44/3.22  
% 8.44/3.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.44/3.23  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 8.44/3.23  
% 8.44/3.23  %Foreground sorts:
% 8.44/3.23  
% 8.44/3.23  
% 8.44/3.23  %Background operators:
% 8.44/3.23  
% 8.44/3.23  
% 8.44/3.23  %Foreground operators:
% 8.44/3.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.44/3.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.44/3.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.44/3.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.44/3.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.44/3.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.44/3.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.44/3.23  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.44/3.23  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.44/3.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.44/3.23  tff('#skF_3', type, '#skF_3': $i).
% 8.44/3.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.44/3.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.44/3.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.44/3.23  tff('#skF_4', type, '#skF_4': $i).
% 8.44/3.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.44/3.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.44/3.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.44/3.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.44/3.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.44/3.23  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 8.44/3.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.44/3.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.44/3.23  
% 8.44/3.26  tff(f_73, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 8.44/3.26  tff(f_97, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 8.44/3.26  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 8.44/3.26  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 8.44/3.26  tff(f_92, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 8.44/3.26  tff(f_84, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 8.44/3.26  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 8.44/3.26  tff(f_56, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 8.44/3.26  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.44/3.26  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 8.44/3.26  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 8.44/3.26  tff(f_58, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 8.44/3.26  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 8.44/3.26  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 8.44/3.26  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 8.44/3.26  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.44/3.26  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 8.44/3.26  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 8.44/3.26  tff(f_90, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.44/3.26  tff(c_46, plain, (![A_32]: (k2_subset_1(A_32)=A_32)), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.44/3.26  tff(c_58, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.44/3.26  tff(c_61, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_58])).
% 8.44/3.26  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.44/3.26  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.44/3.26  tff(c_56, plain, (![A_41]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.44/3.26  tff(c_52, plain, (![A_37]: (~v1_xboole_0(k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.44/3.26  tff(c_346, plain, (![B_80, A_81]: (r2_hidden(B_80, A_81) | ~m1_subset_1(B_80, A_81) | v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_71])).
% 8.44/3.26  tff(c_24, plain, (![C_27, A_23]: (r1_tarski(C_27, A_23) | ~r2_hidden(C_27, k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.44/3.26  tff(c_353, plain, (![B_80, A_23]: (r1_tarski(B_80, A_23) | ~m1_subset_1(B_80, k1_zfmisc_1(A_23)) | v1_xboole_0(k1_zfmisc_1(A_23)))), inference(resolution, [status(thm)], [c_346, c_24])).
% 8.44/3.26  tff(c_395, plain, (![B_84, A_85]: (r1_tarski(B_84, A_85) | ~m1_subset_1(B_84, k1_zfmisc_1(A_85)))), inference(negUnitSimplification, [status(thm)], [c_52, c_353])).
% 8.44/3.26  tff(c_413, plain, (![A_86]: (r1_tarski(k1_xboole_0, A_86))), inference(resolution, [status(thm)], [c_56, c_395])).
% 8.44/3.26  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.44/3.26  tff(c_422, plain, (![A_87]: (k3_xboole_0(k1_xboole_0, A_87)=k1_xboole_0)), inference(resolution, [status(thm)], [c_413, c_8])).
% 8.44/3.26  tff(c_515, plain, (![A_91]: (k3_xboole_0(A_91, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_422])).
% 8.44/3.26  tff(c_18, plain, (![A_17, B_18]: (k5_xboole_0(k5_xboole_0(A_17, B_18), k3_xboole_0(A_17, B_18))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.44/3.26  tff(c_523, plain, (![A_91]: (k5_xboole_0(k5_xboole_0(A_91, k1_xboole_0), k1_xboole_0)=k2_xboole_0(A_91, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_515, c_18])).
% 8.44/3.26  tff(c_556, plain, (![A_91]: (k2_xboole_0(A_91, k1_xboole_0)=A_91)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_523])).
% 8.44/3.26  tff(c_20, plain, (![B_20, A_19]: (k2_tarski(B_20, A_19)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.44/3.26  tff(c_168, plain, (![A_57, B_58]: (k3_tarski(k2_tarski(A_57, B_58))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.44/3.26  tff(c_202, plain, (![A_65, B_66]: (k3_tarski(k2_tarski(A_65, B_66))=k2_xboole_0(B_66, A_65))), inference(superposition, [status(thm), theory('equality')], [c_20, c_168])).
% 8.44/3.26  tff(c_36, plain, (![A_28, B_29]: (k3_tarski(k2_tarski(A_28, B_29))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.44/3.26  tff(c_208, plain, (![B_66, A_65]: (k2_xboole_0(B_66, A_65)=k2_xboole_0(A_65, B_66))), inference(superposition, [status(thm), theory('equality')], [c_202, c_36])).
% 8.44/3.26  tff(c_450, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_422])).
% 8.44/3.26  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.44/3.26  tff(c_526, plain, (![A_91]: (k5_xboole_0(A_91, k1_xboole_0)=k4_xboole_0(A_91, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_515, c_6])).
% 8.44/3.26  tff(c_603, plain, (![A_93]: (k4_xboole_0(A_93, k1_xboole_0)=A_93)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_526])).
% 8.44/3.26  tff(c_12, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.44/3.26  tff(c_616, plain, (![A_93]: (k4_xboole_0(A_93, A_93)=k3_xboole_0(A_93, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_603, c_12])).
% 8.44/3.26  tff(c_627, plain, (![A_93]: (k4_xboole_0(A_93, A_93)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_450, c_616])).
% 8.44/3.26  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.44/3.26  tff(c_271, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(A_73, B_74))=k4_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.44/3.26  tff(c_286, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_271])).
% 8.44/3.26  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 8.44/3.26  tff(c_412, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_395])).
% 8.44/3.26  tff(c_421, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_412, c_8])).
% 8.44/3.26  tff(c_466, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_421, c_6])).
% 8.44/3.26  tff(c_469, plain, (k4_xboole_0('#skF_4', '#skF_3')=k4_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_286, c_466])).
% 8.44/3.26  tff(c_943, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_627, c_469])).
% 8.44/3.26  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.44/3.26  tff(c_947, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_943, c_10])).
% 8.44/3.26  tff(c_953, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_556, c_208, c_947])).
% 8.44/3.26  tff(c_471, plain, (![A_88, B_89]: (k4_xboole_0(A_88, B_89)=k3_subset_1(A_88, B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.44/3.26  tff(c_488, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_471])).
% 8.44/3.26  tff(c_570, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_488, c_10])).
% 8.44/3.26  tff(c_957, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_953, c_570])).
% 8.44/3.26  tff(c_50, plain, (![A_35, B_36]: (m1_subset_1(k3_subset_1(A_35, B_36), k1_zfmisc_1(A_35)) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.44/3.26  tff(c_2218, plain, (![A_132, B_133, C_134]: (k4_subset_1(A_132, B_133, C_134)=k2_xboole_0(B_133, C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(A_132)) | ~m1_subset_1(B_133, k1_zfmisc_1(A_132)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 8.44/3.26  tff(c_12292, plain, (![A_275, B_276, B_277]: (k4_subset_1(A_275, B_276, k3_subset_1(A_275, B_277))=k2_xboole_0(B_276, k3_subset_1(A_275, B_277)) | ~m1_subset_1(B_276, k1_zfmisc_1(A_275)) | ~m1_subset_1(B_277, k1_zfmisc_1(A_275)))), inference(resolution, [status(thm)], [c_50, c_2218])).
% 8.44/3.26  tff(c_12328, plain, (![B_278]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_278))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_278)) | ~m1_subset_1(B_278, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_60, c_12292])).
% 8.44/3.26  tff(c_12359, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_60, c_12328])).
% 8.44/3.26  tff(c_12375, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_957, c_12359])).
% 8.44/3.26  tff(c_12377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_12375])).
% 8.44/3.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.44/3.26  
% 8.44/3.26  Inference rules
% 8.44/3.26  ----------------------
% 8.44/3.26  #Ref     : 0
% 8.44/3.26  #Sup     : 3042
% 8.44/3.26  #Fact    : 0
% 8.44/3.26  #Define  : 0
% 8.44/3.26  #Split   : 0
% 8.44/3.26  #Chain   : 0
% 8.44/3.26  #Close   : 0
% 8.44/3.26  
% 8.44/3.26  Ordering : KBO
% 8.44/3.26  
% 8.44/3.26  Simplification rules
% 8.44/3.26  ----------------------
% 8.44/3.26  #Subsume      : 51
% 8.44/3.26  #Demod        : 4296
% 8.44/3.26  #Tautology    : 2122
% 8.44/3.26  #SimpNegUnit  : 22
% 8.44/3.26  #BackRed      : 10
% 8.44/3.26  
% 8.44/3.26  #Partial instantiations: 0
% 8.44/3.26  #Strategies tried      : 1
% 8.44/3.26  
% 8.44/3.26  Timing (in seconds)
% 8.44/3.26  ----------------------
% 8.44/3.27  Preprocessing        : 0.35
% 8.44/3.27  Parsing              : 0.19
% 8.44/3.27  CNF conversion       : 0.02
% 8.44/3.27  Main loop            : 2.05
% 8.44/3.27  Inferencing          : 0.49
% 8.44/3.27  Reduction            : 1.12
% 8.44/3.27  Demodulation         : 0.97
% 8.44/3.27  BG Simplification    : 0.06
% 8.44/3.27  Subsumption          : 0.29
% 8.44/3.27  Abstraction          : 0.10
% 8.44/3.27  MUC search           : 0.00
% 8.44/3.27  Cooper               : 0.00
% 8.44/3.27  Total                : 2.48
% 8.44/3.27  Index Insertion      : 0.00
% 8.44/3.27  Index Deletion       : 0.00
% 8.44/3.27  Index Matching       : 0.00
% 8.44/3.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
