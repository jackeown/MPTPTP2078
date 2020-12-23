%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:19 EST 2020

% Result     : Theorem 4.37s
% Output     : CNFRefutation 4.37s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 110 expanded)
%              Number of leaves         :   33 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :   90 ( 152 expanded)
%              Number of equality atoms :   44 (  65 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_72,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_53,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_55,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_61,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_584,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = k3_subset_1(A_61,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_593,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_584])).

tff(c_32,plain,(
    ! [A_27] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    ! [A_18] : k1_subset_1(A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_19] : k2_subset_1(A_19) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [A_22] : k3_subset_1(A_22,k1_subset_1(A_22)) = k2_subset_1(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_41,plain,(
    ! [A_22] : k3_subset_1(A_22,k1_subset_1(A_22)) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_42,plain,(
    ! [A_22] : k3_subset_1(A_22,k1_xboole_0) = A_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_41])).

tff(c_12,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_732,plain,(
    ! [C_67,A_68,B_69] :
      ( r1_tarski(C_67,k3_subset_1(A_68,B_69))
      | ~ r1_tarski(B_69,k3_subset_1(A_68,C_67))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(A_68))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_739,plain,(
    ! [C_67,A_68] :
      ( r1_tarski(C_67,k3_subset_1(A_68,k1_xboole_0))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(A_68))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_68)) ) ),
    inference(resolution,[status(thm)],[c_12,c_732])).

tff(c_825,plain,(
    ! [C_74,A_75] :
      ( r1_tarski(C_74,A_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(A_75)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_42,c_739])).

tff(c_834,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_825])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_839,plain,(
    k3_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_834,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_852,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_839,c_2])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_877,plain,(
    k5_xboole_0('#skF_1','#skF_3') = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_852,c_8])).

tff(c_884,plain,(
    k5_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_877])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_xboole_0(k3_xboole_0(A_5,B_6),k5_xboole_0(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_849,plain,(
    r1_xboole_0('#skF_3',k5_xboole_0('#skF_3','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_839,c_6])).

tff(c_865,plain,(
    r1_xboole_0('#skF_3',k5_xboole_0('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_849])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = A_15
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_895,plain,(
    k4_xboole_0('#skF_3',k5_xboole_0('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_865,c_16])).

tff(c_930,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_884,c_895])).

tff(c_38,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(A_15,B_16)
      | k4_xboole_0(A_15,B_16) != A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_420,plain,(
    ! [A_54,C_55,B_56] :
      ( r1_xboole_0(A_54,C_55)
      | ~ r1_xboole_0(B_56,C_55)
      | ~ r1_tarski(A_54,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1497,plain,(
    ! [A_100,B_101,A_102] :
      ( r1_xboole_0(A_100,B_101)
      | ~ r1_tarski(A_100,A_102)
      | k4_xboole_0(A_102,B_101) != A_102 ) ),
    inference(resolution,[status(thm)],[c_18,c_420])).

tff(c_1511,plain,(
    ! [B_103] :
      ( r1_xboole_0('#skF_2',B_103)
      | k4_xboole_0('#skF_3',B_103) != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_38,c_1497])).

tff(c_1527,plain,(
    ! [B_105] :
      ( k4_xboole_0('#skF_2',B_105) = '#skF_2'
      | k4_xboole_0('#skF_3',B_105) != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_1511,c_16])).

tff(c_20,plain,(
    ! [A_17] : k5_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_160,plain,(
    ! [A_41,B_42] :
      ( k3_xboole_0(A_41,B_42) = A_41
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_170,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_160])).

tff(c_347,plain,(
    ! [A_51,B_52] : k5_xboole_0(A_51,k3_xboole_0(A_51,B_52)) = k4_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_369,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) = k5_xboole_0('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_347])).

tff(c_384,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_369])).

tff(c_1553,plain,
    ( k1_xboole_0 = '#skF_2'
    | k4_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_3')) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1527,c_384])).

tff(c_1588,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_930,c_1553])).

tff(c_1590,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1588])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:39:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.37/2.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.37/2.15  
% 4.37/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.37/2.16  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.37/2.16  
% 4.37/2.16  %Foreground sorts:
% 4.37/2.16  
% 4.37/2.16  
% 4.37/2.16  %Background operators:
% 4.37/2.16  
% 4.37/2.16  
% 4.37/2.16  %Foreground operators:
% 4.37/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.37/2.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.37/2.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.37/2.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.37/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.37/2.16  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.37/2.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.37/2.16  tff('#skF_2', type, '#skF_2': $i).
% 4.37/2.16  tff('#skF_3', type, '#skF_3': $i).
% 4.37/2.16  tff('#skF_1', type, '#skF_1': $i).
% 4.37/2.16  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.37/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.37/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.37/2.16  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 4.37/2.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.37/2.16  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.37/2.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.37/2.16  
% 4.37/2.18  tff(f_81, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 4.37/2.18  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.37/2.18  tff(f_72, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.37/2.18  tff(f_53, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 4.37/2.18  tff(f_55, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.37/2.18  tff(f_61, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 4.37/2.18  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.37/2.18  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 4.37/2.18  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.37/2.18  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.37/2.18  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.37/2.18  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 4.37/2.18  tff(f_31, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 4.37/2.18  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.37/2.18  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 4.37/2.18  tff(f_51, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.37/2.18  tff(c_34, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.37/2.18  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.37/2.18  tff(c_584, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=k3_subset_1(A_61, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.37/2.18  tff(c_593, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_584])).
% 4.37/2.18  tff(c_32, plain, (![A_27]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.37/2.18  tff(c_22, plain, (![A_18]: (k1_subset_1(A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.37/2.18  tff(c_24, plain, (![A_19]: (k2_subset_1(A_19)=A_19)), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.37/2.18  tff(c_28, plain, (![A_22]: (k3_subset_1(A_22, k1_subset_1(A_22))=k2_subset_1(A_22))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.37/2.18  tff(c_41, plain, (![A_22]: (k3_subset_1(A_22, k1_subset_1(A_22))=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 4.37/2.18  tff(c_42, plain, (![A_22]: (k3_subset_1(A_22, k1_xboole_0)=A_22)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_41])).
% 4.37/2.18  tff(c_12, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.37/2.18  tff(c_732, plain, (![C_67, A_68, B_69]: (r1_tarski(C_67, k3_subset_1(A_68, B_69)) | ~r1_tarski(B_69, k3_subset_1(A_68, C_67)) | ~m1_subset_1(C_67, k1_zfmisc_1(A_68)) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.37/2.18  tff(c_739, plain, (![C_67, A_68]: (r1_tarski(C_67, k3_subset_1(A_68, k1_xboole_0)) | ~m1_subset_1(C_67, k1_zfmisc_1(A_68)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_68)))), inference(resolution, [status(thm)], [c_12, c_732])).
% 4.37/2.18  tff(c_825, plain, (![C_74, A_75]: (r1_tarski(C_74, A_75) | ~m1_subset_1(C_74, k1_zfmisc_1(A_75)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_42, c_739])).
% 4.37/2.18  tff(c_834, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_825])).
% 4.37/2.18  tff(c_10, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.37/2.18  tff(c_839, plain, (k3_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_834, c_10])).
% 4.37/2.18  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.37/2.18  tff(c_852, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_839, c_2])).
% 4.37/2.18  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.37/2.18  tff(c_877, plain, (k5_xboole_0('#skF_1', '#skF_3')=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_852, c_8])).
% 4.37/2.18  tff(c_884, plain, (k5_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_593, c_877])).
% 4.37/2.18  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.37/2.18  tff(c_6, plain, (![A_5, B_6]: (r1_xboole_0(k3_xboole_0(A_5, B_6), k5_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.37/2.18  tff(c_849, plain, (r1_xboole_0('#skF_3', k5_xboole_0('#skF_3', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_839, c_6])).
% 4.37/2.18  tff(c_865, plain, (r1_xboole_0('#skF_3', k5_xboole_0('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_849])).
% 4.37/2.18  tff(c_16, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=A_15 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.37/2.18  tff(c_895, plain, (k4_xboole_0('#skF_3', k5_xboole_0('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_865, c_16])).
% 4.37/2.18  tff(c_930, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_884, c_895])).
% 4.37/2.18  tff(c_38, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.37/2.18  tff(c_18, plain, (![A_15, B_16]: (r1_xboole_0(A_15, B_16) | k4_xboole_0(A_15, B_16)!=A_15)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.37/2.18  tff(c_420, plain, (![A_54, C_55, B_56]: (r1_xboole_0(A_54, C_55) | ~r1_xboole_0(B_56, C_55) | ~r1_tarski(A_54, B_56))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.37/2.18  tff(c_1497, plain, (![A_100, B_101, A_102]: (r1_xboole_0(A_100, B_101) | ~r1_tarski(A_100, A_102) | k4_xboole_0(A_102, B_101)!=A_102)), inference(resolution, [status(thm)], [c_18, c_420])).
% 4.37/2.18  tff(c_1511, plain, (![B_103]: (r1_xboole_0('#skF_2', B_103) | k4_xboole_0('#skF_3', B_103)!='#skF_3')), inference(resolution, [status(thm)], [c_38, c_1497])).
% 4.37/2.18  tff(c_1527, plain, (![B_105]: (k4_xboole_0('#skF_2', B_105)='#skF_2' | k4_xboole_0('#skF_3', B_105)!='#skF_3')), inference(resolution, [status(thm)], [c_1511, c_16])).
% 4.37/2.18  tff(c_20, plain, (![A_17]: (k5_xboole_0(A_17, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.37/2.18  tff(c_36, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.37/2.18  tff(c_160, plain, (![A_41, B_42]: (k3_xboole_0(A_41, B_42)=A_41 | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.37/2.18  tff(c_170, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))='#skF_2'), inference(resolution, [status(thm)], [c_36, c_160])).
% 4.37/2.18  tff(c_347, plain, (![A_51, B_52]: (k5_xboole_0(A_51, k3_xboole_0(A_51, B_52))=k4_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.37/2.18  tff(c_369, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))=k5_xboole_0('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_170, c_347])).
% 4.37/2.18  tff(c_384, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_369])).
% 4.37/2.18  tff(c_1553, plain, (k1_xboole_0='#skF_2' | k4_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_3'))!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1527, c_384])).
% 4.37/2.18  tff(c_1588, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_930, c_1553])).
% 4.37/2.18  tff(c_1590, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1588])).
% 4.37/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.37/2.18  
% 4.37/2.18  Inference rules
% 4.37/2.18  ----------------------
% 4.37/2.18  #Ref     : 0
% 4.37/2.18  #Sup     : 389
% 4.37/2.18  #Fact    : 0
% 4.37/2.18  #Define  : 0
% 4.37/2.18  #Split   : 4
% 4.37/2.18  #Chain   : 0
% 4.37/2.18  #Close   : 0
% 4.37/2.18  
% 4.37/2.18  Ordering : KBO
% 4.37/2.18  
% 4.37/2.18  Simplification rules
% 4.37/2.18  ----------------------
% 4.37/2.18  #Subsume      : 16
% 4.37/2.18  #Demod        : 323
% 4.37/2.18  #Tautology    : 266
% 4.37/2.18  #SimpNegUnit  : 1
% 4.37/2.18  #BackRed      : 10
% 4.37/2.18  
% 4.37/2.18  #Partial instantiations: 0
% 4.37/2.18  #Strategies tried      : 1
% 4.37/2.18  
% 4.37/2.18  Timing (in seconds)
% 4.37/2.18  ----------------------
% 4.37/2.19  Preprocessing        : 0.49
% 4.37/2.19  Parsing              : 0.26
% 4.37/2.19  CNF conversion       : 0.03
% 4.37/2.19  Main loop            : 0.81
% 4.37/2.19  Inferencing          : 0.26
% 4.37/2.19  Reduction            : 0.32
% 4.37/2.19  Demodulation         : 0.26
% 4.37/2.19  BG Simplification    : 0.03
% 4.37/2.19  Subsumption          : 0.13
% 4.37/2.19  Abstraction          : 0.03
% 4.37/2.19  MUC search           : 0.00
% 4.37/2.19  Cooper               : 0.00
% 4.37/2.19  Total                : 1.36
% 4.37/2.19  Index Insertion      : 0.00
% 4.37/2.19  Index Deletion       : 0.00
% 4.37/2.19  Index Matching       : 0.00
% 4.37/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
