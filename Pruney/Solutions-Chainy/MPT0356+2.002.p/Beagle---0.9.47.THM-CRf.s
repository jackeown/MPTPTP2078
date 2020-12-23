%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:55 EST 2020

% Result     : Theorem 5.66s
% Output     : CNFRefutation 5.66s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 192 expanded)
%              Number of leaves         :   34 (  78 expanded)
%              Depth                    :   12
%              Number of atoms          :  122 ( 313 expanded)
%              Number of equality atoms :   39 (  87 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,k3_subset_1(A,C))
             => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_86,axiom,(
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

tff(f_66,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_47,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_54,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_48,plain,(
    ! [A_30] : ~ v1_xboole_0(k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_455,plain,(
    ! [B_76,A_77] :
      ( r2_hidden(B_76,A_77)
      | ~ m1_subset_1(B_76,A_77)
      | v1_xboole_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_26,plain,(
    ! [C_25,A_21] :
      ( r1_tarski(C_25,A_21)
      | ~ r2_hidden(C_25,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_462,plain,(
    ! [B_76,A_21] :
      ( r1_tarski(B_76,A_21)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_21))
      | v1_xboole_0(k1_zfmisc_1(A_21)) ) ),
    inference(resolution,[status(thm)],[c_455,c_26])).

tff(c_1141,plain,(
    ! [B_115,A_116] :
      ( r1_tarski(B_115,A_116)
      | ~ m1_subset_1(B_115,k1_zfmisc_1(A_116)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_462])).

tff(c_1157,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1141])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_174,plain,(
    ! [A_51,B_52,C_53] :
      ( r1_tarski(A_51,B_52)
      | ~ r1_tarski(A_51,k4_xboole_0(B_52,C_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_186,plain,(
    ! [B_52,C_53] : r1_tarski(k4_xboole_0(B_52,C_53),B_52) ),
    inference(resolution,[status(thm)],[c_8,c_174])).

tff(c_18,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_94,plain,(
    ! [A_37,B_38] :
      ( k2_xboole_0(A_37,B_38) = B_38
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_106,plain,(
    ! [A_12] : k2_xboole_0(k1_xboole_0,A_12) = A_12 ),
    inference(resolution,[status(thm)],[c_18,c_94])).

tff(c_638,plain,(
    ! [A_89,B_90,C_91] :
      ( r1_tarski(A_89,k2_xboole_0(B_90,C_91))
      | ~ r1_tarski(k4_xboole_0(A_89,B_90),C_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_733,plain,(
    ! [A_96,B_97] : r1_tarski(A_96,k2_xboole_0(B_97,k4_xboole_0(A_96,B_97))) ),
    inference(resolution,[status(thm)],[c_8,c_638])).

tff(c_763,plain,(
    ! [A_98] : r1_tarski(A_98,k4_xboole_0(A_98,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_733])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_772,plain,(
    ! [A_98] :
      ( k4_xboole_0(A_98,k1_xboole_0) = A_98
      | ~ r1_tarski(k4_xboole_0(A_98,k1_xboole_0),A_98) ) ),
    inference(resolution,[status(thm)],[c_763,c_4])).

tff(c_787,plain,(
    ! [A_98] : k4_xboole_0(A_98,k1_xboole_0) = A_98 ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_772])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_202,plain,(
    ! [B_56,A_57] :
      ( B_56 = A_57
      | ~ r1_tarski(B_56,A_57)
      | ~ r1_tarski(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_218,plain,(
    ! [A_58] :
      ( k1_xboole_0 = A_58
      | ~ r1_tarski(A_58,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_202])).

tff(c_231,plain,(
    ! [C_53] : k4_xboole_0(k1_xboole_0,C_53) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_186,c_218])).

tff(c_236,plain,(
    ! [C_59] : k4_xboole_0(k1_xboole_0,C_59) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_186,c_218])).

tff(c_22,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_247,plain,(
    ! [C_59] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,C_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_236,c_22])).

tff(c_262,plain,(
    ! [C_60] : k3_xboole_0(k1_xboole_0,C_60) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_247])).

tff(c_280,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_262])).

tff(c_528,plain,(
    ! [A_84,B_85] : k5_xboole_0(A_84,k3_xboole_0(A_84,B_85)) = k4_xboole_0(A_84,B_85) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_537,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = k4_xboole_0(A_1,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_528])).

tff(c_827,plain,(
    ! [A_1] : k5_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_787,c_537])).

tff(c_829,plain,(
    ! [A_103] : k4_xboole_0(A_103,k1_xboole_0) = A_103 ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_772])).

tff(c_863,plain,(
    ! [A_103] : k4_xboole_0(A_103,A_103) = k3_xboole_0(A_103,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_829,c_22])).

tff(c_881,plain,(
    ! [A_103] : k4_xboole_0(A_103,A_103) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_863])).

tff(c_52,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_572,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(A_87,B_88) = k3_subset_1(A_87,B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_584,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_572])).

tff(c_12,plain,(
    ! [A_7,C_9,B_8] :
      ( r1_xboole_0(A_7,C_9)
      | ~ r1_tarski(A_7,k4_xboole_0(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3416,plain,(
    ! [A_204] :
      ( r1_xboole_0(A_204,'#skF_5')
      | ~ r1_tarski(A_204,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_584,c_12])).

tff(c_3496,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_3416])).

tff(c_792,plain,(
    ! [A_99,B_100,C_101] :
      ( r1_tarski(A_99,k4_xboole_0(B_100,C_101))
      | ~ r1_xboole_0(A_99,C_101)
      | ~ r1_tarski(A_99,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6009,plain,(
    ! [B_257,C_258,A_259] :
      ( k4_xboole_0(B_257,C_258) = A_259
      | ~ r1_tarski(k4_xboole_0(B_257,C_258),A_259)
      | ~ r1_xboole_0(A_259,C_258)
      | ~ r1_tarski(A_259,B_257) ) ),
    inference(resolution,[status(thm)],[c_792,c_4])).

tff(c_6078,plain,(
    ! [B_52,C_53] :
      ( k4_xboole_0(B_52,C_53) = B_52
      | ~ r1_xboole_0(B_52,C_53)
      | ~ r1_tarski(B_52,B_52) ) ),
    inference(resolution,[status(thm)],[c_186,c_6009])).

tff(c_6117,plain,(
    ! [B_260,C_261] :
      ( k4_xboole_0(B_260,C_261) = B_260
      | ~ r1_xboole_0(B_260,C_261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6078])).

tff(c_6181,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3496,c_6117])).

tff(c_6282,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6181,c_22])).

tff(c_6300,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_881,c_6282])).

tff(c_543,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_528])).

tff(c_6341,plain,(
    k5_xboole_0('#skF_5',k1_xboole_0) = k4_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6300,c_543])).

tff(c_6394,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_827,c_6341])).

tff(c_285,plain,(
    ! [A_61,C_62,B_63] :
      ( r1_xboole_0(A_61,C_62)
      | ~ r1_tarski(A_61,k4_xboole_0(B_63,C_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_305,plain,(
    ! [B_63,C_62] : r1_xboole_0(k4_xboole_0(B_63,C_62),C_62) ),
    inference(resolution,[status(thm)],[c_8,c_285])).

tff(c_6521,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6394,c_305])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_585,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_572])).

tff(c_6740,plain,(
    ! [A_274] :
      ( r1_tarski(A_274,k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_xboole_0(A_274,'#skF_4')
      | ~ r1_tarski(A_274,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_792])).

tff(c_50,plain,(
    ~ r1_tarski('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6777,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_4')
    | ~ r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_6740,c_50])).

tff(c_6795,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1157,c_6521,c_6777])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:03:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.66/2.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.66/2.21  
% 5.66/2.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.66/2.22  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.66/2.22  
% 5.66/2.22  %Foreground sorts:
% 5.66/2.22  
% 5.66/2.22  
% 5.66/2.22  %Background operators:
% 5.66/2.22  
% 5.66/2.22  
% 5.66/2.22  %Foreground operators:
% 5.66/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.66/2.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.66/2.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.66/2.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.66/2.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.66/2.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.66/2.22  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.66/2.22  tff('#skF_5', type, '#skF_5': $i).
% 5.66/2.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.66/2.22  tff('#skF_3', type, '#skF_3': $i).
% 5.66/2.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.66/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.66/2.22  tff('#skF_4', type, '#skF_4': $i).
% 5.66/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.66/2.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.66/2.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.66/2.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.66/2.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.66/2.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.66/2.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.66/2.22  
% 5.66/2.23  tff(f_96, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 5.66/2.23  tff(f_86, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 5.66/2.23  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.66/2.23  tff(f_66, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.66/2.23  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.66/2.23  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 5.66/2.23  tff(f_47, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.66/2.23  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.66/2.23  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 5.66/2.23  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.66/2.23  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.66/2.23  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.66/2.23  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.66/2.23  tff(f_59, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 5.66/2.23  tff(c_54, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.66/2.23  tff(c_48, plain, (![A_30]: (~v1_xboole_0(k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.66/2.23  tff(c_455, plain, (![B_76, A_77]: (r2_hidden(B_76, A_77) | ~m1_subset_1(B_76, A_77) | v1_xboole_0(A_77))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.66/2.23  tff(c_26, plain, (![C_25, A_21]: (r1_tarski(C_25, A_21) | ~r2_hidden(C_25, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.66/2.23  tff(c_462, plain, (![B_76, A_21]: (r1_tarski(B_76, A_21) | ~m1_subset_1(B_76, k1_zfmisc_1(A_21)) | v1_xboole_0(k1_zfmisc_1(A_21)))), inference(resolution, [status(thm)], [c_455, c_26])).
% 5.66/2.23  tff(c_1141, plain, (![B_115, A_116]: (r1_tarski(B_115, A_116) | ~m1_subset_1(B_115, k1_zfmisc_1(A_116)))), inference(negUnitSimplification, [status(thm)], [c_48, c_462])).
% 5.66/2.23  tff(c_1157, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_1141])).
% 5.66/2.23  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.66/2.23  tff(c_174, plain, (![A_51, B_52, C_53]: (r1_tarski(A_51, B_52) | ~r1_tarski(A_51, k4_xboole_0(B_52, C_53)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.66/2.23  tff(c_186, plain, (![B_52, C_53]: (r1_tarski(k4_xboole_0(B_52, C_53), B_52))), inference(resolution, [status(thm)], [c_8, c_174])).
% 5.66/2.23  tff(c_18, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.66/2.23  tff(c_94, plain, (![A_37, B_38]: (k2_xboole_0(A_37, B_38)=B_38 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.66/2.23  tff(c_106, plain, (![A_12]: (k2_xboole_0(k1_xboole_0, A_12)=A_12)), inference(resolution, [status(thm)], [c_18, c_94])).
% 5.66/2.23  tff(c_638, plain, (![A_89, B_90, C_91]: (r1_tarski(A_89, k2_xboole_0(B_90, C_91)) | ~r1_tarski(k4_xboole_0(A_89, B_90), C_91))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.66/2.23  tff(c_733, plain, (![A_96, B_97]: (r1_tarski(A_96, k2_xboole_0(B_97, k4_xboole_0(A_96, B_97))))), inference(resolution, [status(thm)], [c_8, c_638])).
% 5.66/2.23  tff(c_763, plain, (![A_98]: (r1_tarski(A_98, k4_xboole_0(A_98, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_106, c_733])).
% 5.66/2.23  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.66/2.23  tff(c_772, plain, (![A_98]: (k4_xboole_0(A_98, k1_xboole_0)=A_98 | ~r1_tarski(k4_xboole_0(A_98, k1_xboole_0), A_98))), inference(resolution, [status(thm)], [c_763, c_4])).
% 5.66/2.23  tff(c_787, plain, (![A_98]: (k4_xboole_0(A_98, k1_xboole_0)=A_98)), inference(demodulation, [status(thm), theory('equality')], [c_186, c_772])).
% 5.66/2.23  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.66/2.23  tff(c_202, plain, (![B_56, A_57]: (B_56=A_57 | ~r1_tarski(B_56, A_57) | ~r1_tarski(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.66/2.23  tff(c_218, plain, (![A_58]: (k1_xboole_0=A_58 | ~r1_tarski(A_58, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_202])).
% 5.66/2.23  tff(c_231, plain, (![C_53]: (k4_xboole_0(k1_xboole_0, C_53)=k1_xboole_0)), inference(resolution, [status(thm)], [c_186, c_218])).
% 5.66/2.23  tff(c_236, plain, (![C_59]: (k4_xboole_0(k1_xboole_0, C_59)=k1_xboole_0)), inference(resolution, [status(thm)], [c_186, c_218])).
% 5.66/2.23  tff(c_22, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.66/2.23  tff(c_247, plain, (![C_59]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k3_xboole_0(k1_xboole_0, C_59))), inference(superposition, [status(thm), theory('equality')], [c_236, c_22])).
% 5.66/2.23  tff(c_262, plain, (![C_60]: (k3_xboole_0(k1_xboole_0, C_60)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_231, c_247])).
% 5.66/2.23  tff(c_280, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_262])).
% 5.66/2.23  tff(c_528, plain, (![A_84, B_85]: (k5_xboole_0(A_84, k3_xboole_0(A_84, B_85))=k4_xboole_0(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.66/2.23  tff(c_537, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=k4_xboole_0(A_1, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_280, c_528])).
% 5.66/2.23  tff(c_827, plain, (![A_1]: (k5_xboole_0(A_1, k1_xboole_0)=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_787, c_537])).
% 5.66/2.23  tff(c_829, plain, (![A_103]: (k4_xboole_0(A_103, k1_xboole_0)=A_103)), inference(demodulation, [status(thm), theory('equality')], [c_186, c_772])).
% 5.66/2.23  tff(c_863, plain, (![A_103]: (k4_xboole_0(A_103, A_103)=k3_xboole_0(A_103, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_829, c_22])).
% 5.66/2.23  tff(c_881, plain, (![A_103]: (k4_xboole_0(A_103, A_103)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_280, c_863])).
% 5.66/2.23  tff(c_52, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.66/2.23  tff(c_572, plain, (![A_87, B_88]: (k4_xboole_0(A_87, B_88)=k3_subset_1(A_87, B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 5.66/2.23  tff(c_584, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_54, c_572])).
% 5.66/2.23  tff(c_12, plain, (![A_7, C_9, B_8]: (r1_xboole_0(A_7, C_9) | ~r1_tarski(A_7, k4_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.66/2.23  tff(c_3416, plain, (![A_204]: (r1_xboole_0(A_204, '#skF_5') | ~r1_tarski(A_204, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_584, c_12])).
% 5.66/2.23  tff(c_3496, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_3416])).
% 5.66/2.23  tff(c_792, plain, (![A_99, B_100, C_101]: (r1_tarski(A_99, k4_xboole_0(B_100, C_101)) | ~r1_xboole_0(A_99, C_101) | ~r1_tarski(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.66/2.23  tff(c_6009, plain, (![B_257, C_258, A_259]: (k4_xboole_0(B_257, C_258)=A_259 | ~r1_tarski(k4_xboole_0(B_257, C_258), A_259) | ~r1_xboole_0(A_259, C_258) | ~r1_tarski(A_259, B_257))), inference(resolution, [status(thm)], [c_792, c_4])).
% 5.66/2.23  tff(c_6078, plain, (![B_52, C_53]: (k4_xboole_0(B_52, C_53)=B_52 | ~r1_xboole_0(B_52, C_53) | ~r1_tarski(B_52, B_52))), inference(resolution, [status(thm)], [c_186, c_6009])).
% 5.66/2.23  tff(c_6117, plain, (![B_260, C_261]: (k4_xboole_0(B_260, C_261)=B_260 | ~r1_xboole_0(B_260, C_261))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_6078])).
% 5.66/2.23  tff(c_6181, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_3496, c_6117])).
% 5.66/2.23  tff(c_6282, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6181, c_22])).
% 5.66/2.23  tff(c_6300, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_881, c_6282])).
% 5.66/2.23  tff(c_543, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_528])).
% 5.66/2.23  tff(c_6341, plain, (k5_xboole_0('#skF_5', k1_xboole_0)=k4_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6300, c_543])).
% 5.66/2.23  tff(c_6394, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_827, c_6341])).
% 5.66/2.23  tff(c_285, plain, (![A_61, C_62, B_63]: (r1_xboole_0(A_61, C_62) | ~r1_tarski(A_61, k4_xboole_0(B_63, C_62)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.66/2.23  tff(c_305, plain, (![B_63, C_62]: (r1_xboole_0(k4_xboole_0(B_63, C_62), C_62))), inference(resolution, [status(thm)], [c_8, c_285])).
% 5.66/2.23  tff(c_6521, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6394, c_305])).
% 5.66/2.23  tff(c_56, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.66/2.23  tff(c_585, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_56, c_572])).
% 5.66/2.23  tff(c_6740, plain, (![A_274]: (r1_tarski(A_274, k3_subset_1('#skF_3', '#skF_4')) | ~r1_xboole_0(A_274, '#skF_4') | ~r1_tarski(A_274, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_585, c_792])).
% 5.66/2.23  tff(c_50, plain, (~r1_tarski('#skF_5', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 5.66/2.23  tff(c_6777, plain, (~r1_xboole_0('#skF_5', '#skF_4') | ~r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_6740, c_50])).
% 5.66/2.23  tff(c_6795, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1157, c_6521, c_6777])).
% 5.66/2.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.66/2.23  
% 5.66/2.23  Inference rules
% 5.66/2.23  ----------------------
% 5.66/2.23  #Ref     : 0
% 5.66/2.23  #Sup     : 1563
% 5.66/2.23  #Fact    : 0
% 5.66/2.23  #Define  : 0
% 5.66/2.23  #Split   : 3
% 5.66/2.23  #Chain   : 0
% 5.66/2.23  #Close   : 0
% 5.66/2.23  
% 5.66/2.23  Ordering : KBO
% 5.66/2.23  
% 5.66/2.23  Simplification rules
% 5.66/2.23  ----------------------
% 5.66/2.23  #Subsume      : 35
% 5.66/2.23  #Demod        : 1074
% 5.66/2.23  #Tautology    : 1075
% 5.66/2.23  #SimpNegUnit  : 5
% 5.66/2.23  #BackRed      : 2
% 5.66/2.23  
% 5.66/2.23  #Partial instantiations: 0
% 5.66/2.23  #Strategies tried      : 1
% 5.66/2.23  
% 5.66/2.23  Timing (in seconds)
% 5.66/2.23  ----------------------
% 5.66/2.24  Preprocessing        : 0.32
% 5.66/2.24  Parsing              : 0.17
% 5.66/2.24  CNF conversion       : 0.02
% 5.66/2.24  Main loop            : 1.03
% 5.66/2.24  Inferencing          : 0.31
% 5.66/2.24  Reduction            : 0.44
% 5.66/2.24  Demodulation         : 0.35
% 5.66/2.24  BG Simplification    : 0.03
% 5.66/2.24  Subsumption          : 0.18
% 5.66/2.24  Abstraction          : 0.04
% 5.66/2.24  MUC search           : 0.00
% 5.66/2.24  Cooper               : 0.00
% 5.66/2.24  Total                : 1.39
% 5.66/2.24  Index Insertion      : 0.00
% 5.66/2.24  Index Deletion       : 0.00
% 5.66/2.24  Index Matching       : 0.00
% 5.66/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
