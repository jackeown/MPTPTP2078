%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:32 EST 2020

% Result     : Theorem 12.89s
% Output     : CNFRefutation 12.89s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 144 expanded)
%              Number of leaves         :   47 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :   92 ( 183 expanded)
%              Number of equality atoms :   48 (  78 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_85,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_89,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_96,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_58,plain,(
    ! [A_56] : k2_subset_1(A_56) = A_56 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_68,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_71,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_68])).

tff(c_16,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1380,plain,(
    ! [A_132,B_133] :
      ( k4_xboole_0(A_132,B_133) = k3_subset_1(A_132,B_133)
      | ~ m1_subset_1(B_133,k1_zfmisc_1(A_132)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1393,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_1380])).

tff(c_64,plain,(
    ! [A_61] : ~ v1_xboole_0(k1_zfmisc_1(A_61)) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_642,plain,(
    ! [B_109,A_110] :
      ( r2_hidden(B_109,A_110)
      | ~ m1_subset_1(B_109,A_110)
      | v1_xboole_0(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_36,plain,(
    ! [C_51,A_47] :
      ( r1_tarski(C_51,A_47)
      | ~ r2_hidden(C_51,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_649,plain,(
    ! [B_109,A_47] :
      ( r1_tarski(B_109,A_47)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_47))
      | v1_xboole_0(k1_zfmisc_1(A_47)) ) ),
    inference(resolution,[status(thm)],[c_642,c_36])).

tff(c_1713,plain,(
    ! [B_152,A_153] :
      ( r1_tarski(B_152,A_153)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(A_153)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_649])).

tff(c_1730,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_1713])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1734,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1730,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_514,plain,(
    ! [A_102,B_103] : k5_xboole_0(A_102,k3_xboole_0(A_102,B_103)) = k4_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2651,plain,(
    ! [A_198,B_199] : k5_xboole_0(A_198,k3_xboole_0(B_199,A_198)) = k4_xboole_0(A_198,B_199) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_514])).

tff(c_2726,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1734,c_2651])).

tff(c_2773,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1393,c_2726])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_108,plain,(
    ! [B_69,A_70] : k5_xboole_0(B_69,A_70) = k5_xboole_0(A_70,B_69) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_124,plain,(
    ! [A_70] : k5_xboole_0(k1_xboole_0,A_70) = A_70 ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_16])).

tff(c_20,plain,(
    ! [A_17] : k5_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_883,plain,(
    ! [A_119,B_120,C_121] : k5_xboole_0(k5_xboole_0(A_119,B_120),C_121) = k5_xboole_0(A_119,k5_xboole_0(B_120,C_121)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_963,plain,(
    ! [A_17,C_121] : k5_xboole_0(A_17,k5_xboole_0(A_17,C_121)) = k5_xboole_0(k1_xboole_0,C_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_883])).

tff(c_977,plain,(
    ! [A_122,C_123] : k5_xboole_0(A_122,k5_xboole_0(A_122,C_123)) = C_123 ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_963])).

tff(c_1029,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_977])).

tff(c_2927,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2773,c_1029])).

tff(c_2949,plain,(
    k5_xboole_0('#skF_4','#skF_3') = k3_subset_1('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2773])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_xboole_0(k3_xboole_0(A_7,B_8),k5_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1747,plain,(
    r1_xboole_0('#skF_4',k5_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1734,c_10])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1774,plain,(
    k3_xboole_0('#skF_4',k5_xboole_0('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1747,c_6])).

tff(c_2988,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2949,c_1774])).

tff(c_22,plain,(
    ! [A_18,B_19] : k5_xboole_0(k5_xboole_0(A_18,B_19),k3_xboole_0(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3375,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')),k1_xboole_0) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2988,c_22])).

tff(c_3387,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2927,c_3375])).

tff(c_62,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1(k3_subset_1(A_59,B_60),k1_zfmisc_1(A_59))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1950,plain,(
    ! [A_167,B_168,C_169] :
      ( k4_subset_1(A_167,B_168,C_169) = k2_xboole_0(B_168,C_169)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(A_167))
      | ~ m1_subset_1(B_168,k1_zfmisc_1(A_167)) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_30467,plain,(
    ! [A_385,B_386,B_387] :
      ( k4_subset_1(A_385,B_386,k3_subset_1(A_385,B_387)) = k2_xboole_0(B_386,k3_subset_1(A_385,B_387))
      | ~ m1_subset_1(B_386,k1_zfmisc_1(A_385))
      | ~ m1_subset_1(B_387,k1_zfmisc_1(A_385)) ) ),
    inference(resolution,[status(thm)],[c_62,c_1950])).

tff(c_30770,plain,(
    ! [B_389] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_389)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_389))
      | ~ m1_subset_1(B_389,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_70,c_30467])).

tff(c_30789,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_70,c_30770])).

tff(c_30797,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3387,c_30789])).

tff(c_30799,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_30797])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:26:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.89/6.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.89/6.67  
% 12.89/6.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.89/6.68  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 12.89/6.68  
% 12.89/6.68  %Foreground sorts:
% 12.89/6.68  
% 12.89/6.68  
% 12.89/6.68  %Background operators:
% 12.89/6.68  
% 12.89/6.68  
% 12.89/6.68  %Foreground operators:
% 12.89/6.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.89/6.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.89/6.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.89/6.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.89/6.68  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.89/6.68  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.89/6.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.89/6.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.89/6.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.89/6.68  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 12.89/6.68  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 12.89/6.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.89/6.68  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.89/6.68  tff('#skF_3', type, '#skF_3': $i).
% 12.89/6.68  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.89/6.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.89/6.68  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 12.89/6.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.89/6.68  tff(k3_tarski, type, k3_tarski: $i > $i).
% 12.89/6.68  tff('#skF_4', type, '#skF_4': $i).
% 12.89/6.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.89/6.68  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 12.89/6.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.89/6.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.89/6.68  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 12.89/6.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.89/6.68  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 12.89/6.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 12.89/6.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.89/6.68  
% 12.89/6.69  tff(f_85, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 12.89/6.69  tff(f_107, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 12.89/6.69  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 12.89/6.69  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 12.89/6.69  tff(f_96, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 12.89/6.69  tff(f_83, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 12.89/6.69  tff(f_68, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 12.89/6.69  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 12.89/6.69  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.89/6.69  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.89/6.69  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 12.89/6.69  tff(f_47, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 12.89/6.69  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 12.89/6.69  tff(f_35, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 12.89/6.69  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 12.89/6.69  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 12.89/6.69  tff(f_93, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 12.89/6.69  tff(f_102, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 12.89/6.69  tff(c_58, plain, (![A_56]: (k2_subset_1(A_56)=A_56)), inference(cnfTransformation, [status(thm)], [f_85])).
% 12.89/6.69  tff(c_68, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_107])).
% 12.89/6.69  tff(c_71, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_68])).
% 12.89/6.69  tff(c_16, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_43])).
% 12.89/6.69  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 12.89/6.69  tff(c_1380, plain, (![A_132, B_133]: (k4_xboole_0(A_132, B_133)=k3_subset_1(A_132, B_133) | ~m1_subset_1(B_133, k1_zfmisc_1(A_132)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 12.89/6.69  tff(c_1393, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_70, c_1380])).
% 12.89/6.69  tff(c_64, plain, (![A_61]: (~v1_xboole_0(k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 12.89/6.69  tff(c_642, plain, (![B_109, A_110]: (r2_hidden(B_109, A_110) | ~m1_subset_1(B_109, A_110) | v1_xboole_0(A_110))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.89/6.69  tff(c_36, plain, (![C_51, A_47]: (r1_tarski(C_51, A_47) | ~r2_hidden(C_51, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.89/6.69  tff(c_649, plain, (![B_109, A_47]: (r1_tarski(B_109, A_47) | ~m1_subset_1(B_109, k1_zfmisc_1(A_47)) | v1_xboole_0(k1_zfmisc_1(A_47)))), inference(resolution, [status(thm)], [c_642, c_36])).
% 12.89/6.69  tff(c_1713, plain, (![B_152, A_153]: (r1_tarski(B_152, A_153) | ~m1_subset_1(B_152, k1_zfmisc_1(A_153)))), inference(negUnitSimplification, [status(thm)], [c_64, c_649])).
% 12.89/6.69  tff(c_1730, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_1713])).
% 12.89/6.69  tff(c_14, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.89/6.69  tff(c_1734, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_1730, c_14])).
% 12.89/6.69  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.89/6.69  tff(c_514, plain, (![A_102, B_103]: (k5_xboole_0(A_102, k3_xboole_0(A_102, B_103))=k4_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.89/6.69  tff(c_2651, plain, (![A_198, B_199]: (k5_xboole_0(A_198, k3_xboole_0(B_199, A_198))=k4_xboole_0(A_198, B_199))), inference(superposition, [status(thm), theory('equality')], [c_2, c_514])).
% 12.89/6.69  tff(c_2726, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1734, c_2651])).
% 12.89/6.69  tff(c_2773, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1393, c_2726])).
% 12.89/6.69  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.89/6.69  tff(c_108, plain, (![B_69, A_70]: (k5_xboole_0(B_69, A_70)=k5_xboole_0(A_70, B_69))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.89/6.69  tff(c_124, plain, (![A_70]: (k5_xboole_0(k1_xboole_0, A_70)=A_70)), inference(superposition, [status(thm), theory('equality')], [c_108, c_16])).
% 12.89/6.69  tff(c_20, plain, (![A_17]: (k5_xboole_0(A_17, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.89/6.69  tff(c_883, plain, (![A_119, B_120, C_121]: (k5_xboole_0(k5_xboole_0(A_119, B_120), C_121)=k5_xboole_0(A_119, k5_xboole_0(B_120, C_121)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.89/6.69  tff(c_963, plain, (![A_17, C_121]: (k5_xboole_0(A_17, k5_xboole_0(A_17, C_121))=k5_xboole_0(k1_xboole_0, C_121))), inference(superposition, [status(thm), theory('equality')], [c_20, c_883])).
% 12.89/6.69  tff(c_977, plain, (![A_122, C_123]: (k5_xboole_0(A_122, k5_xboole_0(A_122, C_123))=C_123)), inference(demodulation, [status(thm), theory('equality')], [c_124, c_963])).
% 12.89/6.69  tff(c_1029, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_977])).
% 12.89/6.69  tff(c_2927, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2773, c_1029])).
% 12.89/6.69  tff(c_2949, plain, (k5_xboole_0('#skF_4', '#skF_3')=k3_subset_1('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4, c_2773])).
% 12.89/6.69  tff(c_10, plain, (![A_7, B_8]: (r1_xboole_0(k3_xboole_0(A_7, B_8), k5_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.89/6.69  tff(c_1747, plain, (r1_xboole_0('#skF_4', k5_xboole_0('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1734, c_10])).
% 12.89/6.69  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.89/6.69  tff(c_1774, plain, (k3_xboole_0('#skF_4', k5_xboole_0('#skF_4', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1747, c_6])).
% 12.89/6.69  tff(c_2988, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2949, c_1774])).
% 12.89/6.69  tff(c_22, plain, (![A_18, B_19]: (k5_xboole_0(k5_xboole_0(A_18, B_19), k3_xboole_0(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.89/6.69  tff(c_3375, plain, (k5_xboole_0(k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4')), k1_xboole_0)=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2988, c_22])).
% 12.89/6.69  tff(c_3387, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2927, c_3375])).
% 12.89/6.69  tff(c_62, plain, (![A_59, B_60]: (m1_subset_1(k3_subset_1(A_59, B_60), k1_zfmisc_1(A_59)) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 12.89/6.69  tff(c_1950, plain, (![A_167, B_168, C_169]: (k4_subset_1(A_167, B_168, C_169)=k2_xboole_0(B_168, C_169) | ~m1_subset_1(C_169, k1_zfmisc_1(A_167)) | ~m1_subset_1(B_168, k1_zfmisc_1(A_167)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 12.89/6.69  tff(c_30467, plain, (![A_385, B_386, B_387]: (k4_subset_1(A_385, B_386, k3_subset_1(A_385, B_387))=k2_xboole_0(B_386, k3_subset_1(A_385, B_387)) | ~m1_subset_1(B_386, k1_zfmisc_1(A_385)) | ~m1_subset_1(B_387, k1_zfmisc_1(A_385)))), inference(resolution, [status(thm)], [c_62, c_1950])).
% 12.89/6.69  tff(c_30770, plain, (![B_389]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_389))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_389)) | ~m1_subset_1(B_389, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_70, c_30467])).
% 12.89/6.69  tff(c_30789, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_70, c_30770])).
% 12.89/6.69  tff(c_30797, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3387, c_30789])).
% 12.89/6.69  tff(c_30799, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_30797])).
% 12.89/6.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.89/6.69  
% 12.89/6.69  Inference rules
% 12.89/6.69  ----------------------
% 12.89/6.69  #Ref     : 0
% 12.89/6.69  #Sup     : 7814
% 12.89/6.69  #Fact    : 0
% 12.89/6.69  #Define  : 0
% 12.89/6.69  #Split   : 0
% 12.89/6.69  #Chain   : 0
% 12.89/6.69  #Close   : 0
% 12.89/6.69  
% 12.89/6.69  Ordering : KBO
% 12.89/6.69  
% 12.89/6.69  Simplification rules
% 12.89/6.69  ----------------------
% 12.89/6.69  #Subsume      : 277
% 12.89/6.69  #Demod        : 11116
% 12.89/6.69  #Tautology    : 3640
% 12.89/6.69  #SimpNegUnit  : 14
% 12.89/6.69  #BackRed      : 19
% 12.89/6.69  
% 12.89/6.69  #Partial instantiations: 0
% 12.89/6.69  #Strategies tried      : 1
% 12.89/6.69  
% 12.89/6.69  Timing (in seconds)
% 12.89/6.69  ----------------------
% 12.89/6.69  Preprocessing        : 0.38
% 12.89/6.70  Parsing              : 0.20
% 12.89/6.70  CNF conversion       : 0.03
% 12.89/6.70  Main loop            : 5.50
% 12.89/6.70  Inferencing          : 0.77
% 12.89/6.70  Reduction            : 3.55
% 12.89/6.70  Demodulation         : 3.26
% 12.89/6.70  BG Simplification    : 0.12
% 12.89/6.70  Subsumption          : 0.82
% 12.89/6.70  Abstraction          : 0.18
% 12.89/6.70  MUC search           : 0.00
% 12.89/6.70  Cooper               : 0.00
% 12.89/6.70  Total                : 5.91
% 12.89/6.70  Index Insertion      : 0.00
% 12.89/6.70  Index Deletion       : 0.00
% 12.89/6.70  Index Matching       : 0.00
% 12.89/6.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
