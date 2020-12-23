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
% DateTime   : Thu Dec  3 09:55:37 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 113 expanded)
%              Number of leaves         :   40 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :   83 ( 113 expanded)
%              Number of equality atoms :   49 (  76 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_58,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_78,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_75,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_46,plain,(
    ! [A_30] : k2_subset_1(A_30) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_54,plain,(
    k4_subset_1('#skF_3','#skF_4',k2_subset_1('#skF_3')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_57,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_54])).

tff(c_18,plain,(
    ! [B_15,A_14] : k2_tarski(B_15,A_14) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_171,plain,(
    ! [A_46,B_47] : k3_tarski(k2_tarski(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_216,plain,(
    ! [B_60,A_61] : k3_tarski(k2_tarski(B_60,A_61)) = k2_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_171])).

tff(c_36,plain,(
    ! [A_26,B_27] : k3_tarski(k2_tarski(A_26,B_27)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_222,plain,(
    ! [B_60,A_61] : k2_xboole_0(B_60,A_61) = k2_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_36])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_381,plain,(
    ! [A_73,B_74] : k4_xboole_0(A_73,k4_xboole_0(A_73,B_74)) = k3_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_13] : k4_xboole_0(k1_xboole_0,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_415,plain,(
    ! [B_75] : k3_xboole_0(k1_xboole_0,B_75) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_16])).

tff(c_432,plain,(
    ! [B_2] : k3_xboole_0(B_2,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_415])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_403,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k3_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_381])).

tff(c_517,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_403])).

tff(c_518,plain,(
    ! [A_83] : k4_xboole_0(A_83,A_83) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_403])).

tff(c_14,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_523,plain,(
    ! [A_83] : k4_xboole_0(A_83,k1_xboole_0) = k3_xboole_0(A_83,A_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_14])).

tff(c_551,plain,(
    ! [A_84] : k3_xboole_0(A_84,A_84) = A_84 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_523])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_565,plain,(
    ! [A_84] : k5_xboole_0(A_84,A_84) = k4_xboole_0(A_84,A_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_4])).

tff(c_580,plain,(
    ! [A_84] : k5_xboole_0(A_84,A_84) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_565])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_50,plain,(
    ! [A_32] : ~ v1_xboole_0(k1_zfmisc_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_483,plain,(
    ! [B_77,A_78] :
      ( r2_hidden(B_77,A_78)
      | ~ m1_subset_1(B_77,A_78)
      | v1_xboole_0(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    ! [C_25,A_21] :
      ( r1_tarski(C_25,A_21)
      | ~ r2_hidden(C_25,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_490,plain,(
    ! [B_77,A_21] :
      ( r1_tarski(B_77,A_21)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_21))
      | v1_xboole_0(k1_zfmisc_1(A_21)) ) ),
    inference(resolution,[status(thm)],[c_483,c_24])).

tff(c_631,plain,(
    ! [B_89,A_90] :
      ( r1_tarski(B_89,A_90)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_90)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_490])).

tff(c_648,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_631])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_658,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_648,c_8])).

tff(c_662,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_658,c_4])).

tff(c_665,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_662])).

tff(c_10,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_673,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_665,c_10])).

tff(c_677,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_6,c_673])).

tff(c_48,plain,(
    ! [A_31] : m1_subset_1(k2_subset_1(A_31),k1_zfmisc_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_58,plain,(
    ! [A_31] : m1_subset_1(A_31,k1_zfmisc_1(A_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_48])).

tff(c_1365,plain,(
    ! [A_114,B_115,C_116] :
      ( k4_subset_1(A_114,B_115,C_116) = k2_xboole_0(B_115,C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(A_114))
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1379,plain,(
    ! [A_117,B_118] :
      ( k4_subset_1(A_117,B_118,A_117) = k2_xboole_0(B_118,A_117)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_117)) ) ),
    inference(resolution,[status(thm)],[c_58,c_1365])).

tff(c_1388,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1379])).

tff(c_1394,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_1388])).

tff(c_1396,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_1394])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:28:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.53  
% 3.34/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.53  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.34/1.53  
% 3.34/1.53  %Foreground sorts:
% 3.34/1.53  
% 3.34/1.53  
% 3.34/1.53  %Background operators:
% 3.34/1.53  
% 3.34/1.53  
% 3.34/1.53  %Foreground operators:
% 3.34/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.34/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.34/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.34/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.34/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.34/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.34/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.34/1.53  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.34/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.34/1.53  tff('#skF_3', type, '#skF_3': $i).
% 3.34/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.34/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.53  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.34/1.53  tff('#skF_4', type, '#skF_4': $i).
% 3.34/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.34/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.34/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.34/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.34/1.53  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.34/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.34/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.34/1.53  
% 3.34/1.55  tff(f_73, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.34/1.55  tff(f_89, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 3.34/1.55  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.34/1.55  tff(f_58, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.34/1.55  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.34/1.55  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.34/1.55  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.34/1.55  tff(f_43, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.34/1.55  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.34/1.55  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.34/1.55  tff(f_78, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.34/1.55  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.34/1.55  tff(f_56, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.34/1.55  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.34/1.55  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.34/1.55  tff(f_75, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.34/1.55  tff(f_84, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.34/1.55  tff(c_46, plain, (![A_30]: (k2_subset_1(A_30)=A_30)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.34/1.55  tff(c_54, plain, (k4_subset_1('#skF_3', '#skF_4', k2_subset_1('#skF_3'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.34/1.55  tff(c_57, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_54])).
% 3.34/1.55  tff(c_18, plain, (![B_15, A_14]: (k2_tarski(B_15, A_14)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.34/1.55  tff(c_171, plain, (![A_46, B_47]: (k3_tarski(k2_tarski(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.34/1.55  tff(c_216, plain, (![B_60, A_61]: (k3_tarski(k2_tarski(B_60, A_61))=k2_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_18, c_171])).
% 3.34/1.55  tff(c_36, plain, (![A_26, B_27]: (k3_tarski(k2_tarski(A_26, B_27))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.34/1.55  tff(c_222, plain, (![B_60, A_61]: (k2_xboole_0(B_60, A_61)=k2_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_216, c_36])).
% 3.34/1.55  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.34/1.55  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.34/1.55  tff(c_381, plain, (![A_73, B_74]: (k4_xboole_0(A_73, k4_xboole_0(A_73, B_74))=k3_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.34/1.55  tff(c_16, plain, (![A_13]: (k4_xboole_0(k1_xboole_0, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.34/1.55  tff(c_415, plain, (![B_75]: (k3_xboole_0(k1_xboole_0, B_75)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_381, c_16])).
% 3.34/1.55  tff(c_432, plain, (![B_2]: (k3_xboole_0(B_2, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_415])).
% 3.34/1.55  tff(c_12, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.34/1.55  tff(c_403, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k3_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_381])).
% 3.34/1.55  tff(c_517, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_432, c_403])).
% 3.34/1.55  tff(c_518, plain, (![A_83]: (k4_xboole_0(A_83, A_83)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_432, c_403])).
% 3.34/1.55  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.34/1.55  tff(c_523, plain, (![A_83]: (k4_xboole_0(A_83, k1_xboole_0)=k3_xboole_0(A_83, A_83))), inference(superposition, [status(thm), theory('equality')], [c_518, c_14])).
% 3.34/1.55  tff(c_551, plain, (![A_84]: (k3_xboole_0(A_84, A_84)=A_84)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_523])).
% 3.34/1.55  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.34/1.55  tff(c_565, plain, (![A_84]: (k5_xboole_0(A_84, A_84)=k4_xboole_0(A_84, A_84))), inference(superposition, [status(thm), theory('equality')], [c_551, c_4])).
% 3.34/1.55  tff(c_580, plain, (![A_84]: (k5_xboole_0(A_84, A_84)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_517, c_565])).
% 3.34/1.55  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.34/1.55  tff(c_50, plain, (![A_32]: (~v1_xboole_0(k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.34/1.55  tff(c_483, plain, (![B_77, A_78]: (r2_hidden(B_77, A_78) | ~m1_subset_1(B_77, A_78) | v1_xboole_0(A_78))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.34/1.55  tff(c_24, plain, (![C_25, A_21]: (r1_tarski(C_25, A_21) | ~r2_hidden(C_25, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.34/1.55  tff(c_490, plain, (![B_77, A_21]: (r1_tarski(B_77, A_21) | ~m1_subset_1(B_77, k1_zfmisc_1(A_21)) | v1_xboole_0(k1_zfmisc_1(A_21)))), inference(resolution, [status(thm)], [c_483, c_24])).
% 3.34/1.55  tff(c_631, plain, (![B_89, A_90]: (r1_tarski(B_89, A_90) | ~m1_subset_1(B_89, k1_zfmisc_1(A_90)))), inference(negUnitSimplification, [status(thm)], [c_50, c_490])).
% 3.34/1.55  tff(c_648, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_631])).
% 3.34/1.55  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.34/1.55  tff(c_658, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_648, c_8])).
% 3.34/1.55  tff(c_662, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_658, c_4])).
% 3.34/1.55  tff(c_665, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_580, c_662])).
% 3.34/1.55  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.34/1.55  tff(c_673, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_665, c_10])).
% 3.34/1.55  tff(c_677, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_222, c_6, c_673])).
% 3.34/1.55  tff(c_48, plain, (![A_31]: (m1_subset_1(k2_subset_1(A_31), k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.34/1.55  tff(c_58, plain, (![A_31]: (m1_subset_1(A_31, k1_zfmisc_1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_48])).
% 3.34/1.55  tff(c_1365, plain, (![A_114, B_115, C_116]: (k4_subset_1(A_114, B_115, C_116)=k2_xboole_0(B_115, C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(A_114)) | ~m1_subset_1(B_115, k1_zfmisc_1(A_114)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.34/1.55  tff(c_1379, plain, (![A_117, B_118]: (k4_subset_1(A_117, B_118, A_117)=k2_xboole_0(B_118, A_117) | ~m1_subset_1(B_118, k1_zfmisc_1(A_117)))), inference(resolution, [status(thm)], [c_58, c_1365])).
% 3.34/1.55  tff(c_1388, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')=k2_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_1379])).
% 3.34/1.55  tff(c_1394, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_677, c_1388])).
% 3.34/1.55  tff(c_1396, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_1394])).
% 3.34/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.55  
% 3.34/1.55  Inference rules
% 3.34/1.55  ----------------------
% 3.34/1.55  #Ref     : 0
% 3.34/1.55  #Sup     : 328
% 3.34/1.55  #Fact    : 0
% 3.34/1.55  #Define  : 0
% 3.34/1.55  #Split   : 0
% 3.34/1.55  #Chain   : 0
% 3.34/1.55  #Close   : 0
% 3.34/1.55  
% 3.34/1.55  Ordering : KBO
% 3.34/1.55  
% 3.34/1.55  Simplification rules
% 3.34/1.55  ----------------------
% 3.34/1.55  #Subsume      : 10
% 3.34/1.55  #Demod        : 311
% 3.34/1.55  #Tautology    : 228
% 3.34/1.55  #SimpNegUnit  : 3
% 3.34/1.55  #BackRed      : 0
% 3.34/1.55  
% 3.34/1.55  #Partial instantiations: 0
% 3.34/1.55  #Strategies tried      : 1
% 3.34/1.55  
% 3.34/1.55  Timing (in seconds)
% 3.34/1.55  ----------------------
% 3.34/1.55  Preprocessing        : 0.32
% 3.34/1.55  Parsing              : 0.17
% 3.34/1.55  CNF conversion       : 0.02
% 3.34/1.55  Main loop            : 0.44
% 3.34/1.55  Inferencing          : 0.14
% 3.34/1.55  Reduction            : 0.19
% 3.34/1.55  Demodulation         : 0.16
% 3.34/1.55  BG Simplification    : 0.02
% 3.34/1.55  Subsumption          : 0.06
% 3.34/1.55  Abstraction          : 0.03
% 3.34/1.55  MUC search           : 0.00
% 3.34/1.55  Cooper               : 0.00
% 3.34/1.55  Total                : 0.80
% 3.34/1.55  Index Insertion      : 0.00
% 3.34/1.55  Index Deletion       : 0.00
% 3.34/1.55  Index Matching       : 0.00
% 3.34/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
