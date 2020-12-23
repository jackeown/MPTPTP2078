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
% DateTime   : Thu Dec  3 09:55:39 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 107 expanded)
%              Number of leaves         :   37 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :   84 ( 112 expanded)
%              Number of equality atoms :   46 (  70 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_71,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_56,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_76,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_73,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_44,plain,(
    ! [A_25] : k2_subset_1(A_25) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_52,plain,(
    k4_subset_1('#skF_3','#skF_4',k2_subset_1('#skF_3')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_55,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_52])).

tff(c_10,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_153,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_187,plain,(
    ! [B_56,A_57] : k3_tarski(k2_tarski(B_56,A_57)) = k2_xboole_0(A_57,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_153])).

tff(c_34,plain,(
    ! [A_21,B_22] : k3_tarski(k2_tarski(A_21,B_22)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_217,plain,(
    ! [B_60,A_61] : k2_xboole_0(B_60,A_61) = k2_xboole_0(A_61,B_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_34])).

tff(c_270,plain,(
    ! [A_62] : k2_xboole_0(k1_xboole_0,A_62) = A_62 ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_10])).

tff(c_14,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_282,plain,(
    ! [A_62] : k4_xboole_0(k1_xboole_0,A_62) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_14])).

tff(c_450,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k4_xboole_0(B_76,A_75)) = k2_xboole_0(A_75,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_465,plain,(
    ! [A_62] : k5_xboole_0(A_62,k1_xboole_0) = k2_xboole_0(A_62,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_450])).

tff(c_475,plain,(
    ! [A_62] : k5_xboole_0(A_62,k1_xboole_0) = A_62 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_465])).

tff(c_193,plain,(
    ! [B_56,A_57] : k2_xboole_0(B_56,A_57) = k2_xboole_0(A_57,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_34])).

tff(c_79,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k2_xboole_0(A_36,B_37)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_86,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_79])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_168,plain,(
    ! [A_51,B_52] :
      ( k3_xboole_0(A_51,B_52) = A_51
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_172,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_168])).

tff(c_422,plain,(
    ! [A_72,B_73] : k5_xboole_0(A_72,k3_xboole_0(A_72,B_73)) = k4_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_434,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_422])).

tff(c_437,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_434])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_48,plain,(
    ! [A_27] : ~ v1_xboole_0(k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_382,plain,(
    ! [B_68,A_69] :
      ( r2_hidden(B_68,A_69)
      | ~ m1_subset_1(B_68,A_69)
      | v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    ! [C_20,A_16] :
      ( r1_tarski(C_20,A_16)
      | ~ r2_hidden(C_20,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_389,plain,(
    ! [B_68,A_16] :
      ( r1_tarski(B_68,A_16)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_16))
      | v1_xboole_0(k1_zfmisc_1(A_16)) ) ),
    inference(resolution,[status(thm)],[c_382,c_22])).

tff(c_395,plain,(
    ! [B_70,A_71] :
      ( r1_tarski(B_70,A_71)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_389])).

tff(c_409,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_395])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_416,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_409,c_12])).

tff(c_431,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_422])).

tff(c_445,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_431])).

tff(c_459,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_450])).

tff(c_474,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_459])).

tff(c_533,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_474])).

tff(c_46,plain,(
    ! [A_26] : m1_subset_1(k2_subset_1(A_26),k1_zfmisc_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_56,plain,(
    ! [A_26] : m1_subset_1(A_26,k1_zfmisc_1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46])).

tff(c_1029,plain,(
    ! [A_99,B_100,C_101] :
      ( k4_subset_1(A_99,B_100,C_101) = k2_xboole_0(B_100,C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(A_99))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1248,plain,(
    ! [A_106,B_107] :
      ( k4_subset_1(A_106,B_107,A_106) = k2_xboole_0(B_107,A_106)
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_106)) ) ),
    inference(resolution,[status(thm)],[c_56,c_1029])).

tff(c_1257,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1248])).

tff(c_1263,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_533,c_1257])).

tff(c_1265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_1263])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:02:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.43  
% 2.78/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.43  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.78/1.43  
% 2.78/1.43  %Foreground sorts:
% 2.78/1.43  
% 2.78/1.43  
% 2.78/1.43  %Background operators:
% 2.78/1.43  
% 2.78/1.43  
% 2.78/1.43  %Foreground operators:
% 2.78/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.78/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.78/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.78/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.78/1.43  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.78/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.78/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.78/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.78/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.78/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.78/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.78/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.78/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.78/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.78/1.43  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.78/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.78/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.78/1.43  
% 2.78/1.44  tff(f_71, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.78/1.44  tff(f_87, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 2.78/1.44  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.78/1.44  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.78/1.44  tff(f_56, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.78/1.44  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.78/1.44  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.78/1.44  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.78/1.44  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.78/1.44  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.78/1.44  tff(f_76, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.78/1.44  tff(f_69, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.78/1.44  tff(f_54, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.78/1.44  tff(f_73, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.78/1.44  tff(f_82, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.78/1.44  tff(c_44, plain, (![A_25]: (k2_subset_1(A_25)=A_25)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.78/1.44  tff(c_52, plain, (k4_subset_1('#skF_3', '#skF_4', k2_subset_1('#skF_3'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.78/1.44  tff(c_55, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_52])).
% 2.78/1.44  tff(c_10, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.78/1.44  tff(c_18, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.78/1.44  tff(c_153, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.78/1.44  tff(c_187, plain, (![B_56, A_57]: (k3_tarski(k2_tarski(B_56, A_57))=k2_xboole_0(A_57, B_56))), inference(superposition, [status(thm), theory('equality')], [c_18, c_153])).
% 2.78/1.44  tff(c_34, plain, (![A_21, B_22]: (k3_tarski(k2_tarski(A_21, B_22))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.78/1.44  tff(c_217, plain, (![B_60, A_61]: (k2_xboole_0(B_60, A_61)=k2_xboole_0(A_61, B_60))), inference(superposition, [status(thm), theory('equality')], [c_187, c_34])).
% 2.78/1.44  tff(c_270, plain, (![A_62]: (k2_xboole_0(k1_xboole_0, A_62)=A_62)), inference(superposition, [status(thm), theory('equality')], [c_217, c_10])).
% 2.78/1.44  tff(c_14, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k2_xboole_0(A_8, B_9))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.78/1.44  tff(c_282, plain, (![A_62]: (k4_xboole_0(k1_xboole_0, A_62)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_270, c_14])).
% 2.78/1.44  tff(c_450, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k4_xboole_0(B_76, A_75))=k2_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.78/1.44  tff(c_465, plain, (![A_62]: (k5_xboole_0(A_62, k1_xboole_0)=k2_xboole_0(A_62, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_282, c_450])).
% 2.78/1.44  tff(c_475, plain, (![A_62]: (k5_xboole_0(A_62, k1_xboole_0)=A_62)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_465])).
% 2.78/1.44  tff(c_193, plain, (![B_56, A_57]: (k2_xboole_0(B_56, A_57)=k2_xboole_0(A_57, B_56))), inference(superposition, [status(thm), theory('equality')], [c_187, c_34])).
% 2.78/1.44  tff(c_79, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k2_xboole_0(A_36, B_37))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.78/1.44  tff(c_86, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_79])).
% 2.78/1.44  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.78/1.44  tff(c_168, plain, (![A_51, B_52]: (k3_xboole_0(A_51, B_52)=A_51 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.78/1.44  tff(c_172, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_168])).
% 2.78/1.44  tff(c_422, plain, (![A_72, B_73]: (k5_xboole_0(A_72, k3_xboole_0(A_72, B_73))=k4_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.78/1.44  tff(c_434, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_172, c_422])).
% 2.78/1.44  tff(c_437, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_86, c_434])).
% 2.78/1.44  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.78/1.44  tff(c_48, plain, (![A_27]: (~v1_xboole_0(k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.78/1.44  tff(c_382, plain, (![B_68, A_69]: (r2_hidden(B_68, A_69) | ~m1_subset_1(B_68, A_69) | v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.78/1.44  tff(c_22, plain, (![C_20, A_16]: (r1_tarski(C_20, A_16) | ~r2_hidden(C_20, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.78/1.44  tff(c_389, plain, (![B_68, A_16]: (r1_tarski(B_68, A_16) | ~m1_subset_1(B_68, k1_zfmisc_1(A_16)) | v1_xboole_0(k1_zfmisc_1(A_16)))), inference(resolution, [status(thm)], [c_382, c_22])).
% 2.78/1.44  tff(c_395, plain, (![B_70, A_71]: (r1_tarski(B_70, A_71) | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)))), inference(negUnitSimplification, [status(thm)], [c_48, c_389])).
% 2.78/1.44  tff(c_409, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_395])).
% 2.78/1.44  tff(c_12, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.78/1.44  tff(c_416, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_409, c_12])).
% 2.78/1.44  tff(c_431, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_416, c_422])).
% 2.78/1.44  tff(c_445, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_437, c_431])).
% 2.78/1.44  tff(c_459, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_445, c_450])).
% 2.78/1.44  tff(c_474, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_459])).
% 2.78/1.44  tff(c_533, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_475, c_474])).
% 2.78/1.44  tff(c_46, plain, (![A_26]: (m1_subset_1(k2_subset_1(A_26), k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.78/1.44  tff(c_56, plain, (![A_26]: (m1_subset_1(A_26, k1_zfmisc_1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46])).
% 2.78/1.44  tff(c_1029, plain, (![A_99, B_100, C_101]: (k4_subset_1(A_99, B_100, C_101)=k2_xboole_0(B_100, C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(A_99)) | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.78/1.44  tff(c_1248, plain, (![A_106, B_107]: (k4_subset_1(A_106, B_107, A_106)=k2_xboole_0(B_107, A_106) | ~m1_subset_1(B_107, k1_zfmisc_1(A_106)))), inference(resolution, [status(thm)], [c_56, c_1029])).
% 2.78/1.44  tff(c_1257, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')=k2_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_1248])).
% 2.78/1.44  tff(c_1263, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_533, c_1257])).
% 2.78/1.44  tff(c_1265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_1263])).
% 2.78/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/1.44  
% 2.78/1.44  Inference rules
% 2.78/1.44  ----------------------
% 2.78/1.44  #Ref     : 0
% 2.78/1.44  #Sup     : 290
% 2.78/1.44  #Fact    : 0
% 2.78/1.44  #Define  : 0
% 2.78/1.44  #Split   : 1
% 2.78/1.44  #Chain   : 0
% 2.78/1.44  #Close   : 0
% 2.78/1.44  
% 2.78/1.44  Ordering : KBO
% 2.78/1.44  
% 2.78/1.44  Simplification rules
% 2.78/1.44  ----------------------
% 2.78/1.44  #Subsume      : 10
% 2.78/1.44  #Demod        : 278
% 2.78/1.44  #Tautology    : 229
% 2.78/1.44  #SimpNegUnit  : 3
% 2.78/1.44  #BackRed      : 0
% 2.78/1.44  
% 2.78/1.44  #Partial instantiations: 0
% 2.78/1.44  #Strategies tried      : 1
% 2.78/1.44  
% 2.78/1.44  Timing (in seconds)
% 2.78/1.44  ----------------------
% 2.78/1.45  Preprocessing        : 0.31
% 2.78/1.45  Parsing              : 0.16
% 2.78/1.45  CNF conversion       : 0.02
% 2.78/1.45  Main loop            : 0.38
% 2.78/1.45  Inferencing          : 0.13
% 2.78/1.45  Reduction            : 0.15
% 2.78/1.45  Demodulation         : 0.13
% 2.78/1.45  BG Simplification    : 0.02
% 2.78/1.45  Subsumption          : 0.06
% 2.78/1.45  Abstraction          : 0.02
% 2.78/1.45  MUC search           : 0.00
% 2.78/1.45  Cooper               : 0.00
% 2.78/1.45  Total                : 0.71
% 2.78/1.45  Index Insertion      : 0.00
% 2.78/1.45  Index Deletion       : 0.00
% 2.78/1.45  Index Matching       : 0.00
% 2.78/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
