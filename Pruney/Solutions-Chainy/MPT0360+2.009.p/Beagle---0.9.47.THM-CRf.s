%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:19 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   69 (  82 expanded)
%              Number of leaves         :   33 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :   66 (  90 expanded)
%              Number of equality atoms :   35 (  48 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_58,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_222,plain,(
    ! [A_57,B_58] :
      ( k3_xboole_0(A_57,B_58) = A_57
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_229,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_58,c_222])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1138,plain,(
    ! [A_114,B_115] :
      ( k4_xboole_0(A_114,B_115) = k3_subset_1(A_114,B_115)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1151,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_1138])).

tff(c_20,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_959,plain,(
    ! [A_109,B_110] : k5_xboole_0(A_109,k3_xboole_0(A_109,B_110)) = k4_xboole_0(A_109,B_110) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1013,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = k4_xboole_0(A_13,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_959])).

tff(c_1025,plain,(
    ! [A_111] : k4_xboole_0(A_111,k1_xboole_0) = A_111 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1013])).

tff(c_18,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1058,plain,(
    ! [A_111] : k4_xboole_0(A_111,A_111) = k3_xboole_0(A_111,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1025,c_18])).

tff(c_1086,plain,(
    ! [A_111] : k4_xboole_0(A_111,A_111) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1058])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1010,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_959])).

tff(c_1508,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1086,c_1010])).

tff(c_60,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_230,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_222])).

tff(c_998,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_959])).

tff(c_1509,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1508,c_998])).

tff(c_30,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1559,plain,(
    k5_xboole_0('#skF_5',k1_xboole_0) = k2_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1509,c_30])).

tff(c_1575,plain,(
    k2_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1559])).

tff(c_28,plain,(
    ! [A_20,B_21] : r1_xboole_0(k4_xboole_0(A_20,B_21),B_21) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_565,plain,(
    ! [A_81,C_82,B_83] :
      ( r1_xboole_0(A_81,C_82)
      | ~ r1_xboole_0(A_81,k2_xboole_0(B_83,C_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_645,plain,(
    ! [A_84,B_85,C_86] : r1_xboole_0(k4_xboole_0(A_84,k2_xboole_0(B_85,C_86)),C_86) ),
    inference(resolution,[status(thm)],[c_28,c_565])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_657,plain,(
    ! [C_86,A_84,B_85] : r1_xboole_0(C_86,k4_xboole_0(A_84,k2_xboole_0(B_85,C_86))) ),
    inference(resolution,[status(thm)],[c_645,c_10])).

tff(c_1606,plain,(
    ! [A_124] : r1_xboole_0('#skF_4',k4_xboole_0(A_124,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1575,c_657])).

tff(c_1615,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1151,c_1606])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1674,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1615,c_4])).

tff(c_1678,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_229,c_1674])).

tff(c_1680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1678])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:33:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.64  
% 3.40/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.65  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.40/1.65  
% 3.40/1.65  %Foreground sorts:
% 3.40/1.65  
% 3.40/1.65  
% 3.40/1.65  %Background operators:
% 3.40/1.65  
% 3.40/1.65  
% 3.40/1.65  %Foreground operators:
% 3.40/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.40/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.40/1.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.40/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.65  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.40/1.65  tff('#skF_5', type, '#skF_5': $i).
% 3.40/1.65  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.40/1.65  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.40/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.65  tff('#skF_4', type, '#skF_4': $i).
% 3.40/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.65  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.40/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.40/1.65  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.40/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.40/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.40/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.40/1.65  
% 3.40/1.66  tff(f_105, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 3.40/1.66  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.40/1.66  tff(f_93, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.40/1.66  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.40/1.66  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.40/1.66  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.40/1.66  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.40/1.66  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.40/1.66  tff(f_69, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.40/1.66  tff(f_67, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.40/1.66  tff(f_65, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.40/1.66  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.40/1.66  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.40/1.66  tff(c_56, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.40/1.66  tff(c_58, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.40/1.66  tff(c_222, plain, (![A_57, B_58]: (k3_xboole_0(A_57, B_58)=A_57 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.40/1.66  tff(c_229, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))='#skF_4'), inference(resolution, [status(thm)], [c_58, c_222])).
% 3.40/1.66  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.40/1.66  tff(c_1138, plain, (![A_114, B_115]: (k4_xboole_0(A_114, B_115)=k3_subset_1(A_114, B_115) | ~m1_subset_1(B_115, k1_zfmisc_1(A_114)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.40/1.66  tff(c_1151, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_62, c_1138])).
% 3.40/1.66  tff(c_20, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.40/1.66  tff(c_16, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.40/1.66  tff(c_959, plain, (![A_109, B_110]: (k5_xboole_0(A_109, k3_xboole_0(A_109, B_110))=k4_xboole_0(A_109, B_110))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.40/1.66  tff(c_1013, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=k4_xboole_0(A_13, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_959])).
% 3.40/1.66  tff(c_1025, plain, (![A_111]: (k4_xboole_0(A_111, k1_xboole_0)=A_111)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1013])).
% 3.40/1.66  tff(c_18, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.40/1.66  tff(c_1058, plain, (![A_111]: (k4_xboole_0(A_111, A_111)=k3_xboole_0(A_111, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1025, c_18])).
% 3.40/1.66  tff(c_1086, plain, (![A_111]: (k4_xboole_0(A_111, A_111)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_1058])).
% 3.40/1.66  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.40/1.66  tff(c_1010, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_959])).
% 3.40/1.66  tff(c_1508, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1086, c_1010])).
% 3.40/1.66  tff(c_60, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.40/1.66  tff(c_230, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_60, c_222])).
% 3.40/1.66  tff(c_998, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_230, c_959])).
% 3.40/1.66  tff(c_1509, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1508, c_998])).
% 3.40/1.66  tff(c_30, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.40/1.66  tff(c_1559, plain, (k5_xboole_0('#skF_5', k1_xboole_0)=k2_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1509, c_30])).
% 3.40/1.66  tff(c_1575, plain, (k2_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1559])).
% 3.40/1.66  tff(c_28, plain, (![A_20, B_21]: (r1_xboole_0(k4_xboole_0(A_20, B_21), B_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.40/1.66  tff(c_565, plain, (![A_81, C_82, B_83]: (r1_xboole_0(A_81, C_82) | ~r1_xboole_0(A_81, k2_xboole_0(B_83, C_82)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.40/1.66  tff(c_645, plain, (![A_84, B_85, C_86]: (r1_xboole_0(k4_xboole_0(A_84, k2_xboole_0(B_85, C_86)), C_86))), inference(resolution, [status(thm)], [c_28, c_565])).
% 3.40/1.66  tff(c_10, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.40/1.66  tff(c_657, plain, (![C_86, A_84, B_85]: (r1_xboole_0(C_86, k4_xboole_0(A_84, k2_xboole_0(B_85, C_86))))), inference(resolution, [status(thm)], [c_645, c_10])).
% 3.40/1.66  tff(c_1606, plain, (![A_124]: (r1_xboole_0('#skF_4', k4_xboole_0(A_124, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1575, c_657])).
% 3.40/1.66  tff(c_1615, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1151, c_1606])).
% 3.40/1.66  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.40/1.66  tff(c_1674, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1615, c_4])).
% 3.40/1.66  tff(c_1678, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_229, c_1674])).
% 3.40/1.66  tff(c_1680, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1678])).
% 3.40/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.66  
% 3.40/1.66  Inference rules
% 3.40/1.66  ----------------------
% 3.40/1.66  #Ref     : 0
% 3.40/1.66  #Sup     : 409
% 3.40/1.66  #Fact    : 0
% 3.40/1.66  #Define  : 0
% 3.40/1.66  #Split   : 0
% 3.40/1.66  #Chain   : 0
% 3.40/1.66  #Close   : 0
% 3.40/1.66  
% 3.40/1.66  Ordering : KBO
% 3.40/1.66  
% 3.40/1.66  Simplification rules
% 3.40/1.66  ----------------------
% 3.40/1.66  #Subsume      : 5
% 3.40/1.66  #Demod        : 259
% 3.40/1.66  #Tautology    : 277
% 3.40/1.66  #SimpNegUnit  : 3
% 3.40/1.66  #BackRed      : 5
% 3.40/1.66  
% 3.40/1.66  #Partial instantiations: 0
% 3.40/1.66  #Strategies tried      : 1
% 3.40/1.66  
% 3.40/1.66  Timing (in seconds)
% 3.40/1.66  ----------------------
% 3.40/1.66  Preprocessing        : 0.35
% 3.40/1.66  Parsing              : 0.18
% 3.40/1.66  CNF conversion       : 0.03
% 3.40/1.66  Main loop            : 0.51
% 3.40/1.66  Inferencing          : 0.17
% 3.40/1.66  Reduction            : 0.20
% 3.40/1.66  Demodulation         : 0.15
% 3.40/1.66  BG Simplification    : 0.02
% 3.40/1.66  Subsumption          : 0.08
% 3.40/1.66  Abstraction          : 0.02
% 3.40/1.66  MUC search           : 0.00
% 3.40/1.66  Cooper               : 0.00
% 3.40/1.66  Total                : 0.89
% 3.40/1.66  Index Insertion      : 0.00
% 3.40/1.66  Index Deletion       : 0.00
% 3.40/1.66  Index Matching       : 0.00
% 3.40/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
