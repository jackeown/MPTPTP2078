%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:41 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   81 (  99 expanded)
%              Number of leaves         :   36 (  48 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 101 expanded)
%              Number of equality atoms :   48 (  62 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_51,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_53,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_59,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_26,plain,(
    ! [A_24,B_25] : k3_tarski(k2_tarski(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_118,plain,(
    ! [A_47,B_48] : k3_tarski(k2_tarski(A_47,B_48)) = k2_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_251,plain,(
    ! [B_60,A_61] : k3_tarski(k2_tarski(B_60,A_61)) = k2_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_118])).

tff(c_263,plain,(
    ! [B_25,A_24] : k2_xboole_0(B_25,A_24) = k2_xboole_0(A_24,B_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_251])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    ! [A_26] : k2_subset_1(A_26) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    ! [A_29] : m1_subset_1(k2_subset_1(A_29),k1_zfmisc_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_44,plain,(
    ! [A_29] : m1_subset_1(A_29,k1_zfmisc_1(A_29)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32])).

tff(c_1054,plain,(
    ! [A_104,B_105,C_106] :
      ( k4_subset_1(A_104,B_105,C_106) = k2_xboole_0(B_105,C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(A_104))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1338,plain,(
    ! [A_116,B_117] :
      ( k4_subset_1(A_116,B_117,A_116) = k2_xboole_0(B_117,A_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(A_116)) ) ),
    inference(resolution,[status(thm)],[c_44,c_1054])).

tff(c_1344,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_1338])).

tff(c_1352,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_1344])).

tff(c_40,plain,(
    k4_subset_1('#skF_1','#skF_2',k2_subset_1('#skF_1')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_43,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_40])).

tff(c_1423,plain,(
    k2_xboole_0('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1352,c_43])).

tff(c_867,plain,(
    ! [A_95,B_96] :
      ( k4_xboole_0(A_95,B_96) = k3_subset_1(A_95,B_96)
      | ~ m1_subset_1(B_96,k1_zfmisc_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_878,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_867])).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_936,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_878,c_14])).

tff(c_584,plain,(
    ! [A_78,B_79] :
      ( k3_subset_1(A_78,k3_subset_1(A_78,B_79)) = B_79
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_589,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_42,c_584])).

tff(c_34,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(k3_subset_1(A_30,B_31),k1_zfmisc_1(A_30))
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1428,plain,(
    ! [A_120,B_121] :
      ( k4_xboole_0(A_120,k3_subset_1(A_120,B_121)) = k3_subset_1(A_120,k3_subset_1(A_120,B_121))
      | ~ m1_subset_1(B_121,k1_zfmisc_1(A_120)) ) ),
    inference(resolution,[status(thm)],[c_34,c_867])).

tff(c_1434,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_1428])).

tff(c_1441,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_936,c_589,c_1434])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_8] : k4_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_80,plain,(
    ! [A_42,B_43] : r1_tarski(k4_xboole_0(A_42,B_43),A_42) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_83,plain,(
    ! [A_8] : r1_tarski(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_80])).

tff(c_142,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = k1_xboole_0
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_149,plain,(
    ! [A_8] : k4_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_83,c_142])).

tff(c_274,plain,(
    ! [A_62,B_63] : k5_xboole_0(A_62,k4_xboole_0(B_63,A_62)) = k2_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_289,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = k2_xboole_0(A_8,A_8) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_274])).

tff(c_295,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_289])).

tff(c_401,plain,(
    ! [A_69,B_70] : k4_xboole_0(A_69,k4_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_592,plain,(
    ! [A_80,B_81] : r1_tarski(k3_xboole_0(A_80,B_81),A_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_10])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_622,plain,(
    ! [A_83,B_84] : k4_xboole_0(k3_xboole_0(A_83,B_84),A_83) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_592,c_6])).

tff(c_16,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_630,plain,(
    ! [A_83,B_84] : k2_xboole_0(A_83,k3_xboole_0(A_83,B_84)) = k5_xboole_0(A_83,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_622,c_16])).

tff(c_658,plain,(
    ! [A_83,B_84] : k2_xboole_0(A_83,k3_xboole_0(A_83,B_84)) = A_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_630])).

tff(c_1462,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1441,c_658])).

tff(c_1475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1423,c_1462])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.44  
% 2.92/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.44  %$ r1_tarski > m1_subset_1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.92/1.44  
% 2.92/1.44  %Foreground sorts:
% 2.92/1.44  
% 2.92/1.44  
% 2.92/1.44  %Background operators:
% 2.92/1.44  
% 2.92/1.44  
% 2.92/1.44  %Foreground operators:
% 2.92/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.92/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.92/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.92/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.92/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.92/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.92/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.92/1.44  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.92/1.44  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.92/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.92/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.92/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.92/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.92/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.44  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.92/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.92/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.92/1.44  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.92/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.92/1.44  
% 3.12/1.45  tff(f_51, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.12/1.45  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.12/1.45  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 3.12/1.45  tff(f_53, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.12/1.45  tff(f_59, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.12/1.45  tff(f_73, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.12/1.45  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.12/1.45  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.12/1.45  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.12/1.45  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.12/1.45  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.12/1.45  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.12/1.45  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.12/1.45  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.12/1.45  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.12/1.45  tff(c_26, plain, (![A_24, B_25]: (k3_tarski(k2_tarski(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.12/1.45  tff(c_18, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.12/1.45  tff(c_118, plain, (![A_47, B_48]: (k3_tarski(k2_tarski(A_47, B_48))=k2_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.12/1.45  tff(c_251, plain, (![B_60, A_61]: (k3_tarski(k2_tarski(B_60, A_61))=k2_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_18, c_118])).
% 3.12/1.45  tff(c_263, plain, (![B_25, A_24]: (k2_xboole_0(B_25, A_24)=k2_xboole_0(A_24, B_25))), inference(superposition, [status(thm), theory('equality')], [c_26, c_251])).
% 3.12/1.45  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.12/1.45  tff(c_28, plain, (![A_26]: (k2_subset_1(A_26)=A_26)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.12/1.45  tff(c_32, plain, (![A_29]: (m1_subset_1(k2_subset_1(A_29), k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.12/1.45  tff(c_44, plain, (![A_29]: (m1_subset_1(A_29, k1_zfmisc_1(A_29)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32])).
% 3.12/1.45  tff(c_1054, plain, (![A_104, B_105, C_106]: (k4_subset_1(A_104, B_105, C_106)=k2_xboole_0(B_105, C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(A_104)) | ~m1_subset_1(B_105, k1_zfmisc_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.12/1.45  tff(c_1338, plain, (![A_116, B_117]: (k4_subset_1(A_116, B_117, A_116)=k2_xboole_0(B_117, A_116) | ~m1_subset_1(B_117, k1_zfmisc_1(A_116)))), inference(resolution, [status(thm)], [c_44, c_1054])).
% 3.12/1.45  tff(c_1344, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_1338])).
% 3.12/1.45  tff(c_1352, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_263, c_1344])).
% 3.12/1.45  tff(c_40, plain, (k4_subset_1('#skF_1', '#skF_2', k2_subset_1('#skF_1'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.12/1.45  tff(c_43, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_40])).
% 3.12/1.45  tff(c_1423, plain, (k2_xboole_0('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1352, c_43])).
% 3.12/1.45  tff(c_867, plain, (![A_95, B_96]: (k4_xboole_0(A_95, B_96)=k3_subset_1(A_95, B_96) | ~m1_subset_1(B_96, k1_zfmisc_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.12/1.45  tff(c_878, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_867])).
% 3.12/1.45  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.12/1.45  tff(c_936, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_878, c_14])).
% 3.12/1.45  tff(c_584, plain, (![A_78, B_79]: (k3_subset_1(A_78, k3_subset_1(A_78, B_79))=B_79 | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.12/1.45  tff(c_589, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_42, c_584])).
% 3.12/1.45  tff(c_34, plain, (![A_30, B_31]: (m1_subset_1(k3_subset_1(A_30, B_31), k1_zfmisc_1(A_30)) | ~m1_subset_1(B_31, k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.12/1.45  tff(c_1428, plain, (![A_120, B_121]: (k4_xboole_0(A_120, k3_subset_1(A_120, B_121))=k3_subset_1(A_120, k3_subset_1(A_120, B_121)) | ~m1_subset_1(B_121, k1_zfmisc_1(A_120)))), inference(resolution, [status(thm)], [c_34, c_867])).
% 3.12/1.45  tff(c_1434, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_42, c_1428])).
% 3.12/1.45  tff(c_1441, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_936, c_589, c_1434])).
% 3.12/1.45  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.12/1.45  tff(c_12, plain, (![A_8]: (k4_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.12/1.45  tff(c_80, plain, (![A_42, B_43]: (r1_tarski(k4_xboole_0(A_42, B_43), A_42))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.12/1.45  tff(c_83, plain, (![A_8]: (r1_tarski(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_12, c_80])).
% 3.12/1.45  tff(c_142, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=k1_xboole_0 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.12/1.45  tff(c_149, plain, (![A_8]: (k4_xboole_0(A_8, A_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_83, c_142])).
% 3.12/1.45  tff(c_274, plain, (![A_62, B_63]: (k5_xboole_0(A_62, k4_xboole_0(B_63, A_62))=k2_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.12/1.45  tff(c_289, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=k2_xboole_0(A_8, A_8))), inference(superposition, [status(thm), theory('equality')], [c_149, c_274])).
% 3.12/1.45  tff(c_295, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_289])).
% 3.12/1.45  tff(c_401, plain, (![A_69, B_70]: (k4_xboole_0(A_69, k4_xboole_0(A_69, B_70))=k3_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.12/1.45  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.12/1.45  tff(c_592, plain, (![A_80, B_81]: (r1_tarski(k3_xboole_0(A_80, B_81), A_80))), inference(superposition, [status(thm), theory('equality')], [c_401, c_10])).
% 3.12/1.45  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.12/1.45  tff(c_622, plain, (![A_83, B_84]: (k4_xboole_0(k3_xboole_0(A_83, B_84), A_83)=k1_xboole_0)), inference(resolution, [status(thm)], [c_592, c_6])).
% 3.12/1.45  tff(c_16, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.12/1.45  tff(c_630, plain, (![A_83, B_84]: (k2_xboole_0(A_83, k3_xboole_0(A_83, B_84))=k5_xboole_0(A_83, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_622, c_16])).
% 3.12/1.45  tff(c_658, plain, (![A_83, B_84]: (k2_xboole_0(A_83, k3_xboole_0(A_83, B_84))=A_83)), inference(demodulation, [status(thm), theory('equality')], [c_295, c_630])).
% 3.12/1.45  tff(c_1462, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1441, c_658])).
% 3.12/1.46  tff(c_1475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1423, c_1462])).
% 3.12/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.46  
% 3.12/1.46  Inference rules
% 3.12/1.46  ----------------------
% 3.12/1.46  #Ref     : 0
% 3.12/1.46  #Sup     : 353
% 3.12/1.46  #Fact    : 0
% 3.12/1.46  #Define  : 0
% 3.12/1.46  #Split   : 0
% 3.12/1.46  #Chain   : 0
% 3.12/1.46  #Close   : 0
% 3.12/1.46  
% 3.12/1.46  Ordering : KBO
% 3.12/1.46  
% 3.12/1.46  Simplification rules
% 3.12/1.46  ----------------------
% 3.12/1.46  #Subsume      : 1
% 3.12/1.46  #Demod        : 246
% 3.12/1.46  #Tautology    : 283
% 3.12/1.46  #SimpNegUnit  : 1
% 3.12/1.46  #BackRed      : 8
% 3.12/1.46  
% 3.12/1.46  #Partial instantiations: 0
% 3.12/1.46  #Strategies tried      : 1
% 3.12/1.46  
% 3.12/1.46  Timing (in seconds)
% 3.12/1.46  ----------------------
% 3.14/1.46  Preprocessing        : 0.30
% 3.14/1.46  Parsing              : 0.16
% 3.14/1.46  CNF conversion       : 0.02
% 3.14/1.46  Main loop            : 0.39
% 3.14/1.46  Inferencing          : 0.14
% 3.14/1.46  Reduction            : 0.15
% 3.14/1.46  Demodulation         : 0.12
% 3.14/1.46  BG Simplification    : 0.02
% 3.14/1.46  Subsumption          : 0.06
% 3.14/1.46  Abstraction          : 0.02
% 3.14/1.46  MUC search           : 0.00
% 3.14/1.46  Cooper               : 0.00
% 3.14/1.46  Total                : 0.73
% 3.14/1.46  Index Insertion      : 0.00
% 3.14/1.46  Index Deletion       : 0.00
% 3.14/1.46  Index Matching       : 0.00
% 3.14/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
