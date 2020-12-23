%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:27 EST 2020

% Result     : Theorem 8.84s
% Output     : CNFRefutation 8.84s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 126 expanded)
%              Number of leaves         :   42 (  61 expanded)
%              Depth                    :   12
%              Number of atoms          :   81 ( 129 expanded)
%              Number of equality atoms :   42 (  83 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_92,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_54,plain,(
    ! [A_54] : k2_subset_1(A_54) = A_54 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_64,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_67,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_64])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_413,plain,(
    ! [A_110,B_111,C_112] : k5_xboole_0(k5_xboole_0(A_110,B_111),C_112) = k5_xboole_0(A_110,k5_xboole_0(B_111,C_112)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_435,plain,(
    ! [A_110,B_111] : k5_xboole_0(A_110,k5_xboole_0(B_111,k5_xboole_0(A_110,B_111))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_14])).

tff(c_591,plain,(
    ! [A_116,C_117] : k5_xboole_0(A_116,k5_xboole_0(A_116,C_117)) = k5_xboole_0(k1_xboole_0,C_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_413])).

tff(c_665,plain,(
    ! [A_13] : k5_xboole_0(k1_xboole_0,A_13) = k5_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_591])).

tff(c_681,plain,(
    ! [A_13] : k5_xboole_0(k1_xboole_0,A_13) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_665])).

tff(c_468,plain,(
    ! [A_13,C_112] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_112)) = k5_xboole_0(k1_xboole_0,C_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_413])).

tff(c_768,plain,(
    ! [A_119,C_120] : k5_xboole_0(A_119,k5_xboole_0(A_119,C_120)) = C_120 ),
    inference(demodulation,[status(thm),theory(equality)],[c_681,c_468])).

tff(c_812,plain,(
    ! [B_111,A_110] : k5_xboole_0(B_111,k5_xboole_0(A_110,B_111)) = k5_xboole_0(A_110,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_768])).

tff(c_916,plain,(
    ! [B_125,A_126] : k5_xboole_0(B_125,k5_xboole_0(A_126,B_125)) = A_126 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_812])).

tff(c_851,plain,(
    ! [B_111,A_110] : k5_xboole_0(B_111,k5_xboole_0(A_110,B_111)) = A_110 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_812])).

tff(c_919,plain,(
    ! [A_126,B_125] : k5_xboole_0(k5_xboole_0(A_126,B_125),A_126) = B_125 ),
    inference(superposition,[status(thm),theory(equality)],[c_916,c_851])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_60,plain,(
    ! [A_59] : ~ v1_xboole_0(k1_zfmisc_1(A_59)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_211,plain,(
    ! [B_85,A_86] :
      ( r2_hidden(B_85,A_86)
      | ~ m1_subset_1(B_85,A_86)
      | v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_32,plain,(
    ! [C_49,A_45] :
      ( r1_tarski(C_49,A_45)
      | ~ r2_hidden(C_49,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_215,plain,(
    ! [B_85,A_45] :
      ( r1_tarski(B_85,A_45)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_45))
      | v1_xboole_0(k1_zfmisc_1(A_45)) ) ),
    inference(resolution,[status(thm)],[c_211,c_32])).

tff(c_287,plain,(
    ! [B_93,A_94] :
      ( r1_tarski(B_93,A_94)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_94)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_215])).

tff(c_296,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_287])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_300,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_296,c_6])).

tff(c_1347,plain,(
    ! [A_133,B_134] : k5_xboole_0(k5_xboole_0(A_133,B_134),k3_xboole_0(A_133,B_134)) = k2_xboole_0(A_133,B_134) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1429,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_3'),'#skF_4') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_1347])).

tff(c_1451,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_919,c_1429])).

tff(c_887,plain,(
    ! [A_123,B_124] :
      ( k4_xboole_0(A_123,B_124) = k3_subset_1(A_123,B_124)
      | ~ m1_subset_1(B_124,k1_zfmisc_1(A_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_904,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_887])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_909,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_904,c_8])).

tff(c_1452,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1451,c_909])).

tff(c_58,plain,(
    ! [A_57,B_58] :
      ( m1_subset_1(k3_subset_1(A_57,B_58),k1_zfmisc_1(A_57))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3434,plain,(
    ! [A_183,B_184,C_185] :
      ( k4_subset_1(A_183,B_184,C_185) = k2_xboole_0(B_184,C_185)
      | ~ m1_subset_1(C_185,k1_zfmisc_1(A_183))
      | ~ m1_subset_1(B_184,k1_zfmisc_1(A_183)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_14443,plain,(
    ! [A_307,B_308,B_309] :
      ( k4_subset_1(A_307,B_308,k3_subset_1(A_307,B_309)) = k2_xboole_0(B_308,k3_subset_1(A_307,B_309))
      | ~ m1_subset_1(B_308,k1_zfmisc_1(A_307))
      | ~ m1_subset_1(B_309,k1_zfmisc_1(A_307)) ) ),
    inference(resolution,[status(thm)],[c_58,c_3434])).

tff(c_14466,plain,(
    ! [B_310] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_310)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_310))
      | ~ m1_subset_1(B_310,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_66,c_14443])).

tff(c_14485,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_66,c_14466])).

tff(c_14493,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1452,c_14485])).

tff(c_14495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_14493])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n025.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 14:09:50 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.84/3.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.84/3.32  
% 8.84/3.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.84/3.32  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 8.84/3.32  
% 8.84/3.32  %Foreground sorts:
% 8.84/3.32  
% 8.84/3.32  
% 8.84/3.32  %Background operators:
% 8.84/3.32  
% 8.84/3.32  
% 8.84/3.32  %Foreground operators:
% 8.84/3.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.84/3.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.84/3.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.84/3.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.84/3.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 8.84/3.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.84/3.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.84/3.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.84/3.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.84/3.32  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 8.84/3.32  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 8.84/3.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.84/3.32  tff('#skF_3', type, '#skF_3': $i).
% 8.84/3.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.84/3.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.84/3.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 8.84/3.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.84/3.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.84/3.32  tff('#skF_4', type, '#skF_4': $i).
% 8.84/3.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.84/3.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.84/3.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.84/3.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.84/3.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 8.84/3.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.84/3.32  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 8.84/3.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.84/3.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.84/3.32  
% 8.84/3.33  tff(f_81, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 8.84/3.33  tff(f_103, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 8.84/3.33  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 8.84/3.33  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 8.84/3.33  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 8.84/3.33  tff(f_92, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 8.84/3.33  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 8.84/3.33  tff(f_64, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 8.84/3.33  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 8.84/3.33  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 8.84/3.33  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 8.84/3.33  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 8.84/3.33  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 8.84/3.33  tff(f_98, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 8.84/3.33  tff(c_54, plain, (![A_54]: (k2_subset_1(A_54)=A_54)), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.84/3.33  tff(c_64, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.84/3.33  tff(c_67, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_64])).
% 8.84/3.33  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.84/3.33  tff(c_413, plain, (![A_110, B_111, C_112]: (k5_xboole_0(k5_xboole_0(A_110, B_111), C_112)=k5_xboole_0(A_110, k5_xboole_0(B_111, C_112)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.84/3.33  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.84/3.33  tff(c_435, plain, (![A_110, B_111]: (k5_xboole_0(A_110, k5_xboole_0(B_111, k5_xboole_0(A_110, B_111)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_413, c_14])).
% 8.84/3.33  tff(c_591, plain, (![A_116, C_117]: (k5_xboole_0(A_116, k5_xboole_0(A_116, C_117))=k5_xboole_0(k1_xboole_0, C_117))), inference(superposition, [status(thm), theory('equality')], [c_14, c_413])).
% 8.84/3.33  tff(c_665, plain, (![A_13]: (k5_xboole_0(k1_xboole_0, A_13)=k5_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_591])).
% 8.84/3.33  tff(c_681, plain, (![A_13]: (k5_xboole_0(k1_xboole_0, A_13)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_665])).
% 8.84/3.33  tff(c_468, plain, (![A_13, C_112]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_112))=k5_xboole_0(k1_xboole_0, C_112))), inference(superposition, [status(thm), theory('equality')], [c_14, c_413])).
% 8.84/3.33  tff(c_768, plain, (![A_119, C_120]: (k5_xboole_0(A_119, k5_xboole_0(A_119, C_120))=C_120)), inference(demodulation, [status(thm), theory('equality')], [c_681, c_468])).
% 8.84/3.33  tff(c_812, plain, (![B_111, A_110]: (k5_xboole_0(B_111, k5_xboole_0(A_110, B_111))=k5_xboole_0(A_110, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_435, c_768])).
% 8.84/3.33  tff(c_916, plain, (![B_125, A_126]: (k5_xboole_0(B_125, k5_xboole_0(A_126, B_125))=A_126)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_812])).
% 8.84/3.33  tff(c_851, plain, (![B_111, A_110]: (k5_xboole_0(B_111, k5_xboole_0(A_110, B_111))=A_110)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_812])).
% 8.84/3.33  tff(c_919, plain, (![A_126, B_125]: (k5_xboole_0(k5_xboole_0(A_126, B_125), A_126)=B_125)), inference(superposition, [status(thm), theory('equality')], [c_916, c_851])).
% 8.84/3.33  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 8.84/3.33  tff(c_60, plain, (![A_59]: (~v1_xboole_0(k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.84/3.33  tff(c_211, plain, (![B_85, A_86]: (r2_hidden(B_85, A_86) | ~m1_subset_1(B_85, A_86) | v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.84/3.33  tff(c_32, plain, (![C_49, A_45]: (r1_tarski(C_49, A_45) | ~r2_hidden(C_49, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.84/3.33  tff(c_215, plain, (![B_85, A_45]: (r1_tarski(B_85, A_45) | ~m1_subset_1(B_85, k1_zfmisc_1(A_45)) | v1_xboole_0(k1_zfmisc_1(A_45)))), inference(resolution, [status(thm)], [c_211, c_32])).
% 8.84/3.33  tff(c_287, plain, (![B_93, A_94]: (r1_tarski(B_93, A_94) | ~m1_subset_1(B_93, k1_zfmisc_1(A_94)))), inference(negUnitSimplification, [status(thm)], [c_60, c_215])).
% 8.84/3.33  tff(c_296, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_287])).
% 8.84/3.33  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.84/3.33  tff(c_300, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_296, c_6])).
% 8.84/3.33  tff(c_1347, plain, (![A_133, B_134]: (k5_xboole_0(k5_xboole_0(A_133, B_134), k3_xboole_0(A_133, B_134))=k2_xboole_0(A_133, B_134))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.84/3.33  tff(c_1429, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_300, c_1347])).
% 8.84/3.33  tff(c_1451, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_919, c_1429])).
% 8.84/3.33  tff(c_887, plain, (![A_123, B_124]: (k4_xboole_0(A_123, B_124)=k3_subset_1(A_123, B_124) | ~m1_subset_1(B_124, k1_zfmisc_1(A_123)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 8.84/3.33  tff(c_904, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_887])).
% 8.84/3.33  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.84/3.33  tff(c_909, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_904, c_8])).
% 8.84/3.33  tff(c_1452, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1451, c_909])).
% 8.84/3.33  tff(c_58, plain, (![A_57, B_58]: (m1_subset_1(k3_subset_1(A_57, B_58), k1_zfmisc_1(A_57)) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.84/3.33  tff(c_3434, plain, (![A_183, B_184, C_185]: (k4_subset_1(A_183, B_184, C_185)=k2_xboole_0(B_184, C_185) | ~m1_subset_1(C_185, k1_zfmisc_1(A_183)) | ~m1_subset_1(B_184, k1_zfmisc_1(A_183)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.84/3.33  tff(c_14443, plain, (![A_307, B_308, B_309]: (k4_subset_1(A_307, B_308, k3_subset_1(A_307, B_309))=k2_xboole_0(B_308, k3_subset_1(A_307, B_309)) | ~m1_subset_1(B_308, k1_zfmisc_1(A_307)) | ~m1_subset_1(B_309, k1_zfmisc_1(A_307)))), inference(resolution, [status(thm)], [c_58, c_3434])).
% 8.84/3.33  tff(c_14466, plain, (![B_310]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_310))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_310)) | ~m1_subset_1(B_310, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_66, c_14443])).
% 8.84/3.33  tff(c_14485, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_14466])).
% 8.84/3.33  tff(c_14493, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1452, c_14485])).
% 8.84/3.33  tff(c_14495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_14493])).
% 8.84/3.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.84/3.33  
% 8.84/3.33  Inference rules
% 8.84/3.33  ----------------------
% 8.84/3.33  #Ref     : 0
% 8.84/3.33  #Sup     : 3542
% 8.84/3.33  #Fact    : 0
% 8.84/3.33  #Define  : 0
% 8.84/3.33  #Split   : 0
% 8.84/3.33  #Chain   : 0
% 8.84/3.33  #Close   : 0
% 8.84/3.33  
% 8.84/3.33  Ordering : KBO
% 8.84/3.33  
% 8.84/3.33  Simplification rules
% 8.84/3.33  ----------------------
% 8.84/3.33  #Subsume      : 165
% 8.84/3.33  #Demod        : 4877
% 8.84/3.33  #Tautology    : 2073
% 8.84/3.33  #SimpNegUnit  : 14
% 8.84/3.33  #BackRed      : 8
% 8.84/3.33  
% 8.84/3.33  #Partial instantiations: 0
% 8.84/3.33  #Strategies tried      : 1
% 8.84/3.33  
% 8.84/3.33  Timing (in seconds)
% 8.84/3.33  ----------------------
% 8.84/3.34  Preprocessing        : 0.34
% 8.84/3.34  Parsing              : 0.18
% 8.84/3.34  CNF conversion       : 0.02
% 8.84/3.34  Main loop            : 2.25
% 8.84/3.34  Inferencing          : 0.48
% 8.84/3.34  Reduction            : 1.28
% 8.84/3.34  Demodulation         : 1.13
% 8.84/3.34  BG Simplification    : 0.06
% 8.84/3.34  Subsumption          : 0.33
% 8.84/3.34  Abstraction          : 0.10
% 8.84/3.34  MUC search           : 0.00
% 8.84/3.34  Cooper               : 0.00
% 8.84/3.34  Total                : 2.62
% 8.84/3.34  Index Insertion      : 0.00
% 8.84/3.34  Index Deletion       : 0.00
% 8.84/3.34  Index Matching       : 0.00
% 8.84/3.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
