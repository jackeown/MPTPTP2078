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
% DateTime   : Thu Dec  3 10:09:40 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 115 expanded)
%              Number of leaves         :   22 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :   99 ( 294 expanded)
%              Number of equality atoms :   85 ( 255 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ~ ! [D] :
                ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
               => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                  & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                  & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_12,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_mcart_1('#skF_4')
    | k2_mcart_1(k1_mcart_1('#skF_4')) != k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')
    | k1_mcart_1(k1_mcart_1('#skF_4')) != k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_84,plain,(
    k1_mcart_1(k1_mcart_1('#skF_4')) != k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_14,plain,(
    m1_subset_1('#skF_4',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_135,plain,(
    ! [A_39,B_40,C_41,D_42] :
      ( k3_mcart_1(k5_mcart_1(A_39,B_40,C_41,D_42),k6_mcart_1(A_39,B_40,C_41,D_42),k7_mcart_1(A_39,B_40,C_41,D_42)) = D_42
      | ~ m1_subset_1(D_42,k3_zfmisc_1(A_39,B_40,C_41))
      | k1_xboole_0 = C_41
      | k1_xboole_0 = B_40
      | k1_xboole_0 = A_39 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_54,plain,(
    ! [A_22,B_23,C_24] : k4_tarski(k4_tarski(A_22,B_23),C_24) = k3_mcart_1(A_22,B_23,C_24) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_12,B_13] : k2_mcart_1(k4_tarski(A_12,B_13)) = B_13 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_66,plain,(
    ! [A_22,B_23,C_24] : k2_mcart_1(k3_mcart_1(A_22,B_23,C_24)) = C_24 ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_10])).

tff(c_151,plain,(
    ! [A_43,B_44,C_45,D_46] :
      ( k7_mcart_1(A_43,B_44,C_45,D_46) = k2_mcart_1(D_46)
      | ~ m1_subset_1(D_46,k3_zfmisc_1(A_43,B_44,C_45))
      | k1_xboole_0 = C_45
      | k1_xboole_0 = B_44
      | k1_xboole_0 = A_43 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_66])).

tff(c_157,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_mcart_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_14,c_151])).

tff(c_160,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_mcart_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_18,c_16,c_157])).

tff(c_6,plain,(
    ! [A_7,B_8,C_9,D_11] :
      ( k3_mcart_1(k5_mcart_1(A_7,B_8,C_9,D_11),k6_mcart_1(A_7,B_8,C_9,D_11),k7_mcart_1(A_7,B_8,C_9,D_11)) = D_11
      | ~ m1_subset_1(D_11,k3_zfmisc_1(A_7,B_8,C_9))
      | k1_xboole_0 = C_9
      | k1_xboole_0 = B_8
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_164,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_mcart_1('#skF_4')) = '#skF_4'
    | ~ m1_subset_1('#skF_4',k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_6])).

tff(c_168,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_mcart_1('#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_164])).

tff(c_169,plain,(
    k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_mcart_1('#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_18,c_16,c_168])).

tff(c_8,plain,(
    ! [A_12,B_13] : k1_mcart_1(k4_tarski(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_63,plain,(
    ! [A_22,B_23,C_24] : k1_mcart_1(k3_mcart_1(A_22,B_23,C_24)) = k4_tarski(A_22,B_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_8])).

tff(c_174,plain,(
    k4_tarski(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k1_mcart_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_63])).

tff(c_191,plain,(
    k1_mcart_1(k1_mcart_1('#skF_4')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_8])).

tff(c_198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_191])).

tff(c_199,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_4')) != k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')
    | k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_mcart_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_248,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') != k2_mcart_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_199])).

tff(c_257,plain,(
    ! [A_58,B_59,C_60,D_61] :
      ( k3_mcart_1(k5_mcart_1(A_58,B_59,C_60,D_61),k6_mcart_1(A_58,B_59,C_60,D_61),k7_mcart_1(A_58,B_59,C_60,D_61)) = D_61
      | ~ m1_subset_1(D_61,k3_zfmisc_1(A_58,B_59,C_60))
      | k1_xboole_0 = C_60
      | k1_xboole_0 = B_59
      | k1_xboole_0 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_272,plain,(
    ! [A_62,B_63,C_64,D_65] :
      ( k7_mcart_1(A_62,B_63,C_64,D_65) = k2_mcart_1(D_65)
      | ~ m1_subset_1(D_65,k3_zfmisc_1(A_62,B_63,C_64))
      | k1_xboole_0 = C_64
      | k1_xboole_0 = B_63
      | k1_xboole_0 = A_62 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_66])).

tff(c_278,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_mcart_1('#skF_4')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_14,c_272])).

tff(c_282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_18,c_16,c_248,c_278])).

tff(c_283,plain,(
    k2_mcart_1(k1_mcart_1('#skF_4')) != k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_199])).

tff(c_284,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') = k2_mcart_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_199])).

tff(c_297,plain,(
    ! [A_66,B_67,C_68,D_69] :
      ( k3_mcart_1(k5_mcart_1(A_66,B_67,C_68,D_69),k6_mcart_1(A_66,B_67,C_68,D_69),k7_mcart_1(A_66,B_67,C_68,D_69)) = D_69
      | ~ m1_subset_1(D_69,k3_zfmisc_1(A_66,B_67,C_68))
      | k1_xboole_0 = C_68
      | k1_xboole_0 = B_67
      | k1_xboole_0 = A_66 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_312,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_mcart_1('#skF_4')) = '#skF_4'
    | ~ m1_subset_1('#skF_4',k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_297])).

tff(c_316,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_mcart_1('#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_312])).

tff(c_317,plain,(
    k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k2_mcart_1('#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_18,c_16,c_316])).

tff(c_321,plain,(
    k4_tarski(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4')) = k1_mcart_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_63])).

tff(c_341,plain,(
    k2_mcart_1(k1_mcart_1('#skF_4')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_10])).

tff(c_346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_283,c_341])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:09:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.31  
% 2.16/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.31  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.16/1.31  
% 2.16/1.31  %Foreground sorts:
% 2.16/1.31  
% 2.16/1.31  
% 2.16/1.31  %Background operators:
% 2.16/1.31  
% 2.16/1.31  
% 2.16/1.31  %Foreground operators:
% 2.16/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.16/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.31  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.16/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.31  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 2.16/1.31  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.16/1.31  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 2.16/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.31  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.16/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.16/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.31  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 2.16/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.31  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.16/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.31  
% 2.16/1.32  tff(f_70, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 2.16/1.32  tff(f_45, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 2.16/1.32  tff(f_27, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.16/1.32  tff(f_49, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.16/1.32  tff(c_20, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.16/1.32  tff(c_18, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.16/1.32  tff(c_16, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.16/1.32  tff(c_12, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_mcart_1('#skF_4') | k2_mcart_1(k1_mcart_1('#skF_4'))!=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4') | k1_mcart_1(k1_mcart_1('#skF_4'))!=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.16/1.32  tff(c_84, plain, (k1_mcart_1(k1_mcart_1('#skF_4'))!=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_12])).
% 2.16/1.32  tff(c_14, plain, (m1_subset_1('#skF_4', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.16/1.32  tff(c_135, plain, (![A_39, B_40, C_41, D_42]: (k3_mcart_1(k5_mcart_1(A_39, B_40, C_41, D_42), k6_mcart_1(A_39, B_40, C_41, D_42), k7_mcart_1(A_39, B_40, C_41, D_42))=D_42 | ~m1_subset_1(D_42, k3_zfmisc_1(A_39, B_40, C_41)) | k1_xboole_0=C_41 | k1_xboole_0=B_40 | k1_xboole_0=A_39)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.16/1.32  tff(c_54, plain, (![A_22, B_23, C_24]: (k4_tarski(k4_tarski(A_22, B_23), C_24)=k3_mcart_1(A_22, B_23, C_24))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.16/1.32  tff(c_10, plain, (![A_12, B_13]: (k2_mcart_1(k4_tarski(A_12, B_13))=B_13)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.16/1.32  tff(c_66, plain, (![A_22, B_23, C_24]: (k2_mcart_1(k3_mcart_1(A_22, B_23, C_24))=C_24)), inference(superposition, [status(thm), theory('equality')], [c_54, c_10])).
% 2.16/1.32  tff(c_151, plain, (![A_43, B_44, C_45, D_46]: (k7_mcart_1(A_43, B_44, C_45, D_46)=k2_mcart_1(D_46) | ~m1_subset_1(D_46, k3_zfmisc_1(A_43, B_44, C_45)) | k1_xboole_0=C_45 | k1_xboole_0=B_44 | k1_xboole_0=A_43)), inference(superposition, [status(thm), theory('equality')], [c_135, c_66])).
% 2.16/1.32  tff(c_157, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_mcart_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_14, c_151])).
% 2.16/1.32  tff(c_160, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_mcart_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_20, c_18, c_16, c_157])).
% 2.16/1.32  tff(c_6, plain, (![A_7, B_8, C_9, D_11]: (k3_mcart_1(k5_mcart_1(A_7, B_8, C_9, D_11), k6_mcart_1(A_7, B_8, C_9, D_11), k7_mcart_1(A_7, B_8, C_9, D_11))=D_11 | ~m1_subset_1(D_11, k3_zfmisc_1(A_7, B_8, C_9)) | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.16/1.32  tff(c_164, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_mcart_1('#skF_4'))='#skF_4' | ~m1_subset_1('#skF_4', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_160, c_6])).
% 2.16/1.32  tff(c_168, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_mcart_1('#skF_4'))='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_164])).
% 2.16/1.32  tff(c_169, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_mcart_1('#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_20, c_18, c_16, c_168])).
% 2.16/1.32  tff(c_8, plain, (![A_12, B_13]: (k1_mcart_1(k4_tarski(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.16/1.32  tff(c_63, plain, (![A_22, B_23, C_24]: (k1_mcart_1(k3_mcart_1(A_22, B_23, C_24))=k4_tarski(A_22, B_23))), inference(superposition, [status(thm), theory('equality')], [c_54, c_8])).
% 2.16/1.32  tff(c_174, plain, (k4_tarski(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k1_mcart_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_169, c_63])).
% 2.16/1.32  tff(c_191, plain, (k1_mcart_1(k1_mcart_1('#skF_4'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_174, c_8])).
% 2.16/1.32  tff(c_198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_191])).
% 2.16/1.32  tff(c_199, plain, (k2_mcart_1(k1_mcart_1('#skF_4'))!=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4') | k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_mcart_1('#skF_4')), inference(splitRight, [status(thm)], [c_12])).
% 2.16/1.32  tff(c_248, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')!=k2_mcart_1('#skF_4')), inference(splitLeft, [status(thm)], [c_199])).
% 2.16/1.32  tff(c_257, plain, (![A_58, B_59, C_60, D_61]: (k3_mcart_1(k5_mcart_1(A_58, B_59, C_60, D_61), k6_mcart_1(A_58, B_59, C_60, D_61), k7_mcart_1(A_58, B_59, C_60, D_61))=D_61 | ~m1_subset_1(D_61, k3_zfmisc_1(A_58, B_59, C_60)) | k1_xboole_0=C_60 | k1_xboole_0=B_59 | k1_xboole_0=A_58)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.16/1.32  tff(c_272, plain, (![A_62, B_63, C_64, D_65]: (k7_mcart_1(A_62, B_63, C_64, D_65)=k2_mcart_1(D_65) | ~m1_subset_1(D_65, k3_zfmisc_1(A_62, B_63, C_64)) | k1_xboole_0=C_64 | k1_xboole_0=B_63 | k1_xboole_0=A_62)), inference(superposition, [status(thm), theory('equality')], [c_257, c_66])).
% 2.16/1.32  tff(c_278, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_mcart_1('#skF_4') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_14, c_272])).
% 2.16/1.32  tff(c_282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_18, c_16, c_248, c_278])).
% 2.16/1.32  tff(c_283, plain, (k2_mcart_1(k1_mcart_1('#skF_4'))!=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_199])).
% 2.16/1.32  tff(c_284, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')=k2_mcart_1('#skF_4')), inference(splitRight, [status(thm)], [c_199])).
% 2.16/1.32  tff(c_297, plain, (![A_66, B_67, C_68, D_69]: (k3_mcart_1(k5_mcart_1(A_66, B_67, C_68, D_69), k6_mcart_1(A_66, B_67, C_68, D_69), k7_mcart_1(A_66, B_67, C_68, D_69))=D_69 | ~m1_subset_1(D_69, k3_zfmisc_1(A_66, B_67, C_68)) | k1_xboole_0=C_68 | k1_xboole_0=B_67 | k1_xboole_0=A_66)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.16/1.32  tff(c_312, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_mcart_1('#skF_4'))='#skF_4' | ~m1_subset_1('#skF_4', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_284, c_297])).
% 2.16/1.32  tff(c_316, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_mcart_1('#skF_4'))='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_312])).
% 2.16/1.32  tff(c_317, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k2_mcart_1('#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_20, c_18, c_16, c_316])).
% 2.16/1.32  tff(c_321, plain, (k4_tarski(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4'))=k1_mcart_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_317, c_63])).
% 2.16/1.32  tff(c_341, plain, (k2_mcart_1(k1_mcart_1('#skF_4'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_321, c_10])).
% 2.16/1.32  tff(c_346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_283, c_341])).
% 2.16/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.32  
% 2.16/1.32  Inference rules
% 2.16/1.32  ----------------------
% 2.16/1.32  #Ref     : 0
% 2.16/1.32  #Sup     : 80
% 2.16/1.32  #Fact    : 0
% 2.16/1.32  #Define  : 0
% 2.16/1.32  #Split   : 2
% 2.16/1.32  #Chain   : 0
% 2.16/1.32  #Close   : 0
% 2.16/1.32  
% 2.16/1.32  Ordering : KBO
% 2.16/1.32  
% 2.16/1.32  Simplification rules
% 2.16/1.32  ----------------------
% 2.16/1.32  #Subsume      : 0
% 2.16/1.32  #Demod        : 23
% 2.16/1.32  #Tautology    : 57
% 2.16/1.32  #SimpNegUnit  : 6
% 2.16/1.32  #BackRed      : 0
% 2.16/1.32  
% 2.16/1.32  #Partial instantiations: 0
% 2.16/1.32  #Strategies tried      : 1
% 2.16/1.32  
% 2.16/1.32  Timing (in seconds)
% 2.16/1.32  ----------------------
% 2.16/1.32  Preprocessing        : 0.30
% 2.16/1.32  Parsing              : 0.16
% 2.16/1.32  CNF conversion       : 0.02
% 2.16/1.32  Main loop            : 0.22
% 2.16/1.32  Inferencing          : 0.09
% 2.16/1.33  Reduction            : 0.07
% 2.16/1.33  Demodulation         : 0.05
% 2.16/1.33  BG Simplification    : 0.01
% 2.16/1.33  Subsumption          : 0.02
% 2.16/1.33  Abstraction          : 0.01
% 2.16/1.33  MUC search           : 0.00
% 2.16/1.33  Cooper               : 0.00
% 2.16/1.33  Total                : 0.55
% 2.16/1.33  Index Insertion      : 0.00
% 2.16/1.33  Index Deletion       : 0.00
% 2.16/1.33  Index Matching       : 0.00
% 2.16/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
