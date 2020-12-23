%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:40 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 4.34s
% Verified   : 
% Statistics : Number of formulae       :   86 (  99 expanded)
%              Number of leaves         :   46 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :   86 ( 106 expanded)
%              Number of equality atoms :   41 (  53 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_45,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_98,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_78,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_95,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_68,plain,(
    ! [A_56] : k2_subset_1(A_56) = A_56 ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_76,plain,(
    k4_subset_1('#skF_6','#skF_7',k2_subset_1('#skF_6')) != k2_subset_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_79,plain,(
    k4_subset_1('#skF_6','#skF_7','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_76])).

tff(c_28,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_9] :
      ( r2_hidden('#skF_3'(A_9),A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_260,plain,(
    ! [D_90,A_91,B_92] :
      ( r2_hidden(D_90,A_91)
      | ~ r2_hidden(D_90,k4_xboole_0(A_91,B_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_265,plain,(
    ! [A_91,B_92] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_91,B_92)),A_91)
      | k4_xboole_0(A_91,B_92) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_260])).

tff(c_266,plain,(
    ! [D_93,B_94,A_95] :
      ( ~ r2_hidden(D_93,B_94)
      | ~ r2_hidden(D_93,k4_xboole_0(A_95,B_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1465,plain,(
    ! [A_181,B_182] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_181,B_182)),B_182)
      | k4_xboole_0(A_181,B_182) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_266])).

tff(c_1488,plain,(
    ! [A_91] : k4_xboole_0(A_91,A_91) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_265,c_1465])).

tff(c_20,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_342,plain,(
    ! [A_105,B_106] : k5_xboole_0(A_105,k3_xboole_0(A_105,B_106)) = k4_xboole_0(A_105,B_106) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_354,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_342])).

tff(c_1509,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1488,c_354])).

tff(c_78,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_72,plain,(
    ! [A_58] : ~ v1_xboole_0(k1_zfmisc_1(A_58)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_288,plain,(
    ! [B_100,A_101] :
      ( r2_hidden(B_100,A_101)
      | ~ m1_subset_1(B_100,A_101)
      | v1_xboole_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_46,plain,(
    ! [C_51,A_47] :
      ( r1_tarski(C_51,A_47)
      | ~ r2_hidden(C_51,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_303,plain,(
    ! [B_100,A_47] :
      ( r1_tarski(B_100,A_47)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_47))
      | v1_xboole_0(k1_zfmisc_1(A_47)) ) ),
    inference(resolution,[status(thm)],[c_288,c_46])).

tff(c_310,plain,(
    ! [B_102,A_103] :
      ( r1_tarski(B_102,A_103)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_103)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_303])).

tff(c_327,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_78,c_310])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_337,plain,(
    k3_xboole_0('#skF_7','#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_327,c_26])).

tff(c_351,plain,(
    k5_xboole_0('#skF_7','#skF_7') = k4_xboole_0('#skF_7','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_342])).

tff(c_1538,plain,(
    k4_xboole_0('#skF_7','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1509,c_351])).

tff(c_30,plain,(
    ! [A_16,B_17] : k5_xboole_0(A_16,k4_xboole_0(B_17,A_16)) = k2_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1586,plain,(
    k5_xboole_0('#skF_6',k1_xboole_0) = k2_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1538,c_30])).

tff(c_1591,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1586])).

tff(c_32,plain,(
    ! [B_19,A_18] : k2_tarski(B_19,A_18) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_157,plain,(
    ! [A_78,B_79] : k3_tarski(k2_tarski(A_78,B_79)) = k2_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_194,plain,(
    ! [A_84,B_85] : k3_tarski(k2_tarski(A_84,B_85)) = k2_xboole_0(B_85,A_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_157])).

tff(c_58,plain,(
    ! [A_52,B_53] : k3_tarski(k2_tarski(A_52,B_53)) = k2_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_200,plain,(
    ! [B_85,A_84] : k2_xboole_0(B_85,A_84) = k2_xboole_0(A_84,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_58])).

tff(c_70,plain,(
    ! [A_57] : m1_subset_1(k2_subset_1(A_57),k1_zfmisc_1(A_57)) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_80,plain,(
    ! [A_57] : m1_subset_1(A_57,k1_zfmisc_1(A_57)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_70])).

tff(c_2411,plain,(
    ! [A_245,B_246,C_247] :
      ( k4_subset_1(A_245,B_246,C_247) = k2_xboole_0(B_246,C_247)
      | ~ m1_subset_1(C_247,k1_zfmisc_1(A_245))
      | ~ m1_subset_1(B_246,k1_zfmisc_1(A_245)) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2437,plain,(
    ! [A_248,B_249] :
      ( k4_subset_1(A_248,B_249,A_248) = k2_xboole_0(B_249,A_248)
      | ~ m1_subset_1(B_249,k1_zfmisc_1(A_248)) ) ),
    inference(resolution,[status(thm)],[c_80,c_2411])).

tff(c_2452,plain,(
    k4_subset_1('#skF_6','#skF_7','#skF_6') = k2_xboole_0('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_78,c_2437])).

tff(c_2464,plain,(
    k4_subset_1('#skF_6','#skF_7','#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1591,c_200,c_2452])).

tff(c_2466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_79,c_2464])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:14:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.98/1.77  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.78  
% 3.98/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.98/1.78  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5 > #skF_4
% 3.98/1.78  
% 3.98/1.78  %Foreground sorts:
% 3.98/1.78  
% 3.98/1.78  
% 3.98/1.78  %Background operators:
% 3.98/1.78  
% 3.98/1.78  
% 3.98/1.78  %Foreground operators:
% 3.98/1.78  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.98/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.98/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.98/1.78  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.98/1.78  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.98/1.78  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.98/1.78  tff('#skF_7', type, '#skF_7': $i).
% 3.98/1.78  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.98/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.98/1.78  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.98/1.78  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.98/1.78  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.98/1.78  tff('#skF_6', type, '#skF_6': $i).
% 3.98/1.78  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.98/1.78  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.98/1.78  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.98/1.78  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.98/1.78  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.98/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.98/1.78  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.98/1.78  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.98/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.98/1.78  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.98/1.78  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.98/1.78  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.98/1.78  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.98/1.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.98/1.78  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.98/1.78  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.98/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.98/1.78  
% 4.34/1.80  tff(f_93, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.34/1.80  tff(f_109, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 4.34/1.80  tff(f_53, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.34/1.80  tff(f_45, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.34/1.80  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.34/1.80  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.34/1.80  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.34/1.80  tff(f_98, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.34/1.80  tff(f_91, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.34/1.80  tff(f_76, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.34/1.80  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.34/1.80  tff(f_55, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.34/1.80  tff(f_57, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.34/1.80  tff(f_78, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.34/1.80  tff(f_95, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.34/1.80  tff(f_104, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.34/1.80  tff(c_68, plain, (![A_56]: (k2_subset_1(A_56)=A_56)), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.34/1.80  tff(c_76, plain, (k4_subset_1('#skF_6', '#skF_7', k2_subset_1('#skF_6'))!=k2_subset_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.34/1.80  tff(c_79, plain, (k4_subset_1('#skF_6', '#skF_7', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_76])).
% 4.34/1.80  tff(c_28, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.34/1.80  tff(c_22, plain, (![A_9]: (r2_hidden('#skF_3'(A_9), A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.34/1.80  tff(c_260, plain, (![D_90, A_91, B_92]: (r2_hidden(D_90, A_91) | ~r2_hidden(D_90, k4_xboole_0(A_91, B_92)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.34/1.80  tff(c_265, plain, (![A_91, B_92]: (r2_hidden('#skF_3'(k4_xboole_0(A_91, B_92)), A_91) | k4_xboole_0(A_91, B_92)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_260])).
% 4.34/1.80  tff(c_266, plain, (![D_93, B_94, A_95]: (~r2_hidden(D_93, B_94) | ~r2_hidden(D_93, k4_xboole_0(A_95, B_94)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.34/1.80  tff(c_1465, plain, (![A_181, B_182]: (~r2_hidden('#skF_3'(k4_xboole_0(A_181, B_182)), B_182) | k4_xboole_0(A_181, B_182)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_266])).
% 4.34/1.80  tff(c_1488, plain, (![A_91]: (k4_xboole_0(A_91, A_91)=k1_xboole_0)), inference(resolution, [status(thm)], [c_265, c_1465])).
% 4.34/1.80  tff(c_20, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.34/1.80  tff(c_342, plain, (![A_105, B_106]: (k5_xboole_0(A_105, k3_xboole_0(A_105, B_106))=k4_xboole_0(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.34/1.80  tff(c_354, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_20, c_342])).
% 4.34/1.80  tff(c_1509, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1488, c_354])).
% 4.34/1.80  tff(c_78, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.34/1.80  tff(c_72, plain, (![A_58]: (~v1_xboole_0(k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.34/1.80  tff(c_288, plain, (![B_100, A_101]: (r2_hidden(B_100, A_101) | ~m1_subset_1(B_100, A_101) | v1_xboole_0(A_101))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.34/1.80  tff(c_46, plain, (![C_51, A_47]: (r1_tarski(C_51, A_47) | ~r2_hidden(C_51, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.34/1.80  tff(c_303, plain, (![B_100, A_47]: (r1_tarski(B_100, A_47) | ~m1_subset_1(B_100, k1_zfmisc_1(A_47)) | v1_xboole_0(k1_zfmisc_1(A_47)))), inference(resolution, [status(thm)], [c_288, c_46])).
% 4.34/1.80  tff(c_310, plain, (![B_102, A_103]: (r1_tarski(B_102, A_103) | ~m1_subset_1(B_102, k1_zfmisc_1(A_103)))), inference(negUnitSimplification, [status(thm)], [c_72, c_303])).
% 4.34/1.80  tff(c_327, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_78, c_310])).
% 4.34/1.80  tff(c_26, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.34/1.80  tff(c_337, plain, (k3_xboole_0('#skF_7', '#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_327, c_26])).
% 4.34/1.80  tff(c_351, plain, (k5_xboole_0('#skF_7', '#skF_7')=k4_xboole_0('#skF_7', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_337, c_342])).
% 4.34/1.80  tff(c_1538, plain, (k4_xboole_0('#skF_7', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1509, c_351])).
% 4.34/1.80  tff(c_30, plain, (![A_16, B_17]: (k5_xboole_0(A_16, k4_xboole_0(B_17, A_16))=k2_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.34/1.80  tff(c_1586, plain, (k5_xboole_0('#skF_6', k1_xboole_0)=k2_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1538, c_30])).
% 4.34/1.80  tff(c_1591, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1586])).
% 4.34/1.80  tff(c_32, plain, (![B_19, A_18]: (k2_tarski(B_19, A_18)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.34/1.80  tff(c_157, plain, (![A_78, B_79]: (k3_tarski(k2_tarski(A_78, B_79))=k2_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.34/1.80  tff(c_194, plain, (![A_84, B_85]: (k3_tarski(k2_tarski(A_84, B_85))=k2_xboole_0(B_85, A_84))), inference(superposition, [status(thm), theory('equality')], [c_32, c_157])).
% 4.34/1.80  tff(c_58, plain, (![A_52, B_53]: (k3_tarski(k2_tarski(A_52, B_53))=k2_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.34/1.80  tff(c_200, plain, (![B_85, A_84]: (k2_xboole_0(B_85, A_84)=k2_xboole_0(A_84, B_85))), inference(superposition, [status(thm), theory('equality')], [c_194, c_58])).
% 4.34/1.80  tff(c_70, plain, (![A_57]: (m1_subset_1(k2_subset_1(A_57), k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.34/1.80  tff(c_80, plain, (![A_57]: (m1_subset_1(A_57, k1_zfmisc_1(A_57)))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_70])).
% 4.34/1.80  tff(c_2411, plain, (![A_245, B_246, C_247]: (k4_subset_1(A_245, B_246, C_247)=k2_xboole_0(B_246, C_247) | ~m1_subset_1(C_247, k1_zfmisc_1(A_245)) | ~m1_subset_1(B_246, k1_zfmisc_1(A_245)))), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.34/1.80  tff(c_2437, plain, (![A_248, B_249]: (k4_subset_1(A_248, B_249, A_248)=k2_xboole_0(B_249, A_248) | ~m1_subset_1(B_249, k1_zfmisc_1(A_248)))), inference(resolution, [status(thm)], [c_80, c_2411])).
% 4.34/1.80  tff(c_2452, plain, (k4_subset_1('#skF_6', '#skF_7', '#skF_6')=k2_xboole_0('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_78, c_2437])).
% 4.34/1.80  tff(c_2464, plain, (k4_subset_1('#skF_6', '#skF_7', '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_1591, c_200, c_2452])).
% 4.34/1.80  tff(c_2466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_79, c_2464])).
% 4.34/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.34/1.80  
% 4.34/1.80  Inference rules
% 4.34/1.80  ----------------------
% 4.34/1.80  #Ref     : 0
% 4.34/1.80  #Sup     : 543
% 4.34/1.80  #Fact    : 0
% 4.34/1.80  #Define  : 0
% 4.34/1.80  #Split   : 8
% 4.34/1.80  #Chain   : 0
% 4.34/1.80  #Close   : 0
% 4.34/1.80  
% 4.34/1.80  Ordering : KBO
% 4.34/1.80  
% 4.34/1.80  Simplification rules
% 4.34/1.80  ----------------------
% 4.34/1.80  #Subsume      : 100
% 4.34/1.80  #Demod        : 197
% 4.34/1.80  #Tautology    : 279
% 4.34/1.80  #SimpNegUnit  : 64
% 4.34/1.80  #BackRed      : 18
% 4.34/1.80  
% 4.34/1.80  #Partial instantiations: 0
% 4.34/1.80  #Strategies tried      : 1
% 4.34/1.80  
% 4.34/1.80  Timing (in seconds)
% 4.34/1.80  ----------------------
% 4.39/1.80  Preprocessing        : 0.35
% 4.39/1.80  Parsing              : 0.18
% 4.39/1.80  CNF conversion       : 0.03
% 4.39/1.80  Main loop            : 0.65
% 4.39/1.80  Inferencing          : 0.23
% 4.39/1.80  Reduction            : 0.21
% 4.39/1.80  Demodulation         : 0.15
% 4.39/1.80  BG Simplification    : 0.03
% 4.39/1.80  Subsumption          : 0.13
% 4.39/1.80  Abstraction          : 0.03
% 4.39/1.80  MUC search           : 0.00
% 4.39/1.80  Cooper               : 0.00
% 4.39/1.80  Total                : 1.04
% 4.39/1.80  Index Insertion      : 0.00
% 4.39/1.80  Index Deletion       : 0.00
% 4.39/1.80  Index Matching       : 0.00
% 4.39/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
