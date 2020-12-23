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
% DateTime   : Thu Dec  3 09:55:32 EST 2020

% Result     : Theorem 9.64s
% Output     : CNFRefutation 9.71s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 113 expanded)
%              Number of leaves         :   45 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :   93 ( 125 expanded)
%              Number of equality atoms :   50 (  67 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_81,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

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

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

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
    ! [A_43] : k2_subset_1(A_43) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_64,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_67,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_64])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_666,plain,(
    ! [A_107,B_108] :
      ( k4_xboole_0(A_107,B_108) = k3_subset_1(A_107,B_108)
      | ~ m1_subset_1(B_108,k1_zfmisc_1(A_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_675,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_666])).

tff(c_60,plain,(
    ! [A_48] : ~ v1_xboole_0(k1_zfmisc_1(A_48)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_476,plain,(
    ! [B_97,A_98] :
      ( r2_hidden(B_97,A_98)
      | ~ m1_subset_1(B_97,A_98)
      | v1_xboole_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_32,plain,(
    ! [C_38,A_34] :
      ( r1_tarski(C_38,A_34)
      | ~ r2_hidden(C_38,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_483,plain,(
    ! [B_97,A_34] :
      ( r1_tarski(B_97,A_34)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_34))
      | v1_xboole_0(k1_zfmisc_1(A_34)) ) ),
    inference(resolution,[status(thm)],[c_476,c_32])).

tff(c_1853,plain,(
    ! [B_148,A_149] :
      ( r1_tarski(B_148,A_149)
      | ~ m1_subset_1(B_148,k1_zfmisc_1(A_149)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_483])).

tff(c_1866,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_1853])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1870,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1866,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_311,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k3_xboole_0(A_85,B_86)) = k4_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2180,plain,(
    ! [A_158,B_159] : k5_xboole_0(A_158,k3_xboole_0(B_159,A_158)) = k4_xboole_0(A_158,B_159) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_311])).

tff(c_2222,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1870,c_2180])).

tff(c_2279,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_2222])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_138,plain,(
    ! [B_60,A_61] : k5_xboole_0(B_60,A_61) = k5_xboole_0(A_61,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_154,plain,(
    ! [A_61] : k5_xboole_0(k1_xboole_0,A_61) = A_61 ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_14])).

tff(c_20,plain,(
    ! [A_17] : k5_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_875,plain,(
    ! [A_117,B_118,C_119] : k5_xboole_0(k5_xboole_0(A_117,B_118),C_119) = k5_xboole_0(A_117,k5_xboole_0(B_118,C_119)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_950,plain,(
    ! [A_17,C_119] : k5_xboole_0(A_17,k5_xboole_0(A_17,C_119)) = k5_xboole_0(k1_xboole_0,C_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_875])).

tff(c_964,plain,(
    ! [A_120,C_121] : k5_xboole_0(A_120,k5_xboole_0(A_120,C_121)) = C_121 ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_950])).

tff(c_1010,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_964])).

tff(c_2398,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2279,c_1010])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_xboole_0(k4_xboole_0(A_12,B_13),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_253,plain,(
    ! [A_75,B_76] :
      ( k3_xboole_0(A_75,B_76) = k1_xboole_0
      | ~ r1_xboole_0(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_261,plain,(
    ! [A_12,B_13] : k3_xboole_0(k4_xboole_0(A_12,B_13),B_13) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_253])).

tff(c_327,plain,(
    ! [A_12,B_13] : k5_xboole_0(k4_xboole_0(A_12,B_13),k1_xboole_0) = k4_xboole_0(k4_xboole_0(A_12,B_13),B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_311])).

tff(c_2675,plain,(
    ! [A_165,B_166] : k4_xboole_0(k4_xboole_0(A_165,B_166),B_166) = k4_xboole_0(A_165,B_166) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_327])).

tff(c_2739,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_675,c_2675])).

tff(c_2770,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_675,c_2739])).

tff(c_22,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2890,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2770,c_22])).

tff(c_2906,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2398,c_2890])).

tff(c_58,plain,(
    ! [A_46,B_47] :
      ( m1_subset_1(k3_subset_1(A_46,B_47),k1_zfmisc_1(A_46))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2085,plain,(
    ! [A_152,B_153,C_154] :
      ( k4_subset_1(A_152,B_153,C_154) = k2_xboole_0(B_153,C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(A_152))
      | ~ m1_subset_1(B_153,k1_zfmisc_1(A_152)) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_15037,plain,(
    ! [A_290,B_291,B_292] :
      ( k4_subset_1(A_290,B_291,k3_subset_1(A_290,B_292)) = k2_xboole_0(B_291,k3_subset_1(A_290,B_292))
      | ~ m1_subset_1(B_291,k1_zfmisc_1(A_290))
      | ~ m1_subset_1(B_292,k1_zfmisc_1(A_290)) ) ),
    inference(resolution,[status(thm)],[c_58,c_2085])).

tff(c_15215,plain,(
    ! [B_294] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_294)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_294))
      | ~ m1_subset_1(B_294,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_66,c_15037])).

tff(c_15234,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_66,c_15215])).

tff(c_15242,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2906,c_15234])).

tff(c_15244,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_15242])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.64/3.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.64/3.59  
% 9.64/3.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.64/3.60  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 9.64/3.60  
% 9.64/3.60  %Foreground sorts:
% 9.64/3.60  
% 9.64/3.60  
% 9.64/3.60  %Background operators:
% 9.64/3.60  
% 9.64/3.60  
% 9.64/3.60  %Foreground operators:
% 9.64/3.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.64/3.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.64/3.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.64/3.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.64/3.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.64/3.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.64/3.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.64/3.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.64/3.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.64/3.60  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.64/3.60  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 9.64/3.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.64/3.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.64/3.60  tff('#skF_3', type, '#skF_3': $i).
% 9.64/3.60  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.64/3.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.64/3.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.64/3.60  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.64/3.60  tff('#skF_4', type, '#skF_4': $i).
% 9.64/3.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.64/3.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.64/3.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.64/3.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.64/3.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.64/3.60  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 9.64/3.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.64/3.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.64/3.60  
% 9.71/3.61  tff(f_81, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 9.71/3.61  tff(f_103, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 9.71/3.61  tff(f_85, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 9.71/3.61  tff(f_92, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 9.71/3.61  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 9.71/3.61  tff(f_64, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 9.71/3.61  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.71/3.61  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.71/3.61  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 9.71/3.61  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 9.71/3.61  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 9.71/3.61  tff(f_47, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 9.71/3.61  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 9.71/3.61  tff(f_43, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 9.71/3.61  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 9.71/3.61  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 9.71/3.61  tff(f_89, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 9.71/3.61  tff(f_98, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 9.71/3.61  tff(c_54, plain, (![A_43]: (k2_subset_1(A_43)=A_43)), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.71/3.61  tff(c_64, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.71/3.61  tff(c_67, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_64])).
% 9.71/3.61  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 9.71/3.61  tff(c_666, plain, (![A_107, B_108]: (k4_xboole_0(A_107, B_108)=k3_subset_1(A_107, B_108) | ~m1_subset_1(B_108, k1_zfmisc_1(A_107)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.71/3.61  tff(c_675, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_66, c_666])).
% 9.71/3.61  tff(c_60, plain, (![A_48]: (~v1_xboole_0(k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 9.71/3.61  tff(c_476, plain, (![B_97, A_98]: (r2_hidden(B_97, A_98) | ~m1_subset_1(B_97, A_98) | v1_xboole_0(A_98))), inference(cnfTransformation, [status(thm)], [f_79])).
% 9.71/3.61  tff(c_32, plain, (![C_38, A_34]: (r1_tarski(C_38, A_34) | ~r2_hidden(C_38, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.71/3.61  tff(c_483, plain, (![B_97, A_34]: (r1_tarski(B_97, A_34) | ~m1_subset_1(B_97, k1_zfmisc_1(A_34)) | v1_xboole_0(k1_zfmisc_1(A_34)))), inference(resolution, [status(thm)], [c_476, c_32])).
% 9.71/3.61  tff(c_1853, plain, (![B_148, A_149]: (r1_tarski(B_148, A_149) | ~m1_subset_1(B_148, k1_zfmisc_1(A_149)))), inference(negUnitSimplification, [status(thm)], [c_60, c_483])).
% 9.71/3.61  tff(c_1866, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_66, c_1853])).
% 9.71/3.61  tff(c_12, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.71/3.61  tff(c_1870, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_1866, c_12])).
% 9.71/3.61  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.71/3.61  tff(c_311, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k3_xboole_0(A_85, B_86))=k4_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.71/3.61  tff(c_2180, plain, (![A_158, B_159]: (k5_xboole_0(A_158, k3_xboole_0(B_159, A_158))=k4_xboole_0(A_158, B_159))), inference(superposition, [status(thm), theory('equality')], [c_2, c_311])).
% 9.71/3.61  tff(c_2222, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1870, c_2180])).
% 9.71/3.61  tff(c_2279, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_675, c_2222])).
% 9.71/3.61  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.71/3.61  tff(c_138, plain, (![B_60, A_61]: (k5_xboole_0(B_60, A_61)=k5_xboole_0(A_61, B_60))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.71/3.61  tff(c_14, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.71/3.61  tff(c_154, plain, (![A_61]: (k5_xboole_0(k1_xboole_0, A_61)=A_61)), inference(superposition, [status(thm), theory('equality')], [c_138, c_14])).
% 9.71/3.61  tff(c_20, plain, (![A_17]: (k5_xboole_0(A_17, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.71/3.61  tff(c_875, plain, (![A_117, B_118, C_119]: (k5_xboole_0(k5_xboole_0(A_117, B_118), C_119)=k5_xboole_0(A_117, k5_xboole_0(B_118, C_119)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.71/3.61  tff(c_950, plain, (![A_17, C_119]: (k5_xboole_0(A_17, k5_xboole_0(A_17, C_119))=k5_xboole_0(k1_xboole_0, C_119))), inference(superposition, [status(thm), theory('equality')], [c_20, c_875])).
% 9.71/3.61  tff(c_964, plain, (![A_120, C_121]: (k5_xboole_0(A_120, k5_xboole_0(A_120, C_121))=C_121)), inference(demodulation, [status(thm), theory('equality')], [c_154, c_950])).
% 9.71/3.61  tff(c_1010, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_964])).
% 9.71/3.61  tff(c_2398, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2279, c_1010])).
% 9.71/3.61  tff(c_16, plain, (![A_12, B_13]: (r1_xboole_0(k4_xboole_0(A_12, B_13), B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.71/3.61  tff(c_253, plain, (![A_75, B_76]: (k3_xboole_0(A_75, B_76)=k1_xboole_0 | ~r1_xboole_0(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.71/3.61  tff(c_261, plain, (![A_12, B_13]: (k3_xboole_0(k4_xboole_0(A_12, B_13), B_13)=k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_253])).
% 9.71/3.61  tff(c_327, plain, (![A_12, B_13]: (k5_xboole_0(k4_xboole_0(A_12, B_13), k1_xboole_0)=k4_xboole_0(k4_xboole_0(A_12, B_13), B_13))), inference(superposition, [status(thm), theory('equality')], [c_261, c_311])).
% 9.71/3.61  tff(c_2675, plain, (![A_165, B_166]: (k4_xboole_0(k4_xboole_0(A_165, B_166), B_166)=k4_xboole_0(A_165, B_166))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_327])).
% 9.71/3.61  tff(c_2739, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_675, c_2675])).
% 9.71/3.61  tff(c_2770, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_675, c_2739])).
% 9.71/3.61  tff(c_22, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.71/3.61  tff(c_2890, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2770, c_22])).
% 9.71/3.61  tff(c_2906, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2398, c_2890])).
% 9.71/3.61  tff(c_58, plain, (![A_46, B_47]: (m1_subset_1(k3_subset_1(A_46, B_47), k1_zfmisc_1(A_46)) | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 9.71/3.61  tff(c_2085, plain, (![A_152, B_153, C_154]: (k4_subset_1(A_152, B_153, C_154)=k2_xboole_0(B_153, C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(A_152)) | ~m1_subset_1(B_153, k1_zfmisc_1(A_152)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.71/3.61  tff(c_15037, plain, (![A_290, B_291, B_292]: (k4_subset_1(A_290, B_291, k3_subset_1(A_290, B_292))=k2_xboole_0(B_291, k3_subset_1(A_290, B_292)) | ~m1_subset_1(B_291, k1_zfmisc_1(A_290)) | ~m1_subset_1(B_292, k1_zfmisc_1(A_290)))), inference(resolution, [status(thm)], [c_58, c_2085])).
% 9.71/3.61  tff(c_15215, plain, (![B_294]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_294))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_294)) | ~m1_subset_1(B_294, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_66, c_15037])).
% 9.71/3.61  tff(c_15234, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_66, c_15215])).
% 9.71/3.61  tff(c_15242, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2906, c_15234])).
% 9.71/3.61  tff(c_15244, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_15242])).
% 9.71/3.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.71/3.61  
% 9.71/3.61  Inference rules
% 9.71/3.61  ----------------------
% 9.71/3.61  #Ref     : 0
% 9.71/3.61  #Sup     : 3734
% 9.71/3.61  #Fact    : 0
% 9.71/3.61  #Define  : 0
% 9.71/3.61  #Split   : 0
% 9.71/3.61  #Chain   : 0
% 9.71/3.61  #Close   : 0
% 9.71/3.61  
% 9.71/3.61  Ordering : KBO
% 9.71/3.61  
% 9.71/3.61  Simplification rules
% 9.71/3.61  ----------------------
% 9.71/3.61  #Subsume      : 147
% 9.71/3.61  #Demod        : 4504
% 9.71/3.61  #Tautology    : 2334
% 9.71/3.61  #SimpNegUnit  : 14
% 9.71/3.61  #BackRed      : 10
% 9.71/3.61  
% 9.71/3.61  #Partial instantiations: 0
% 9.71/3.61  #Strategies tried      : 1
% 9.71/3.61  
% 9.71/3.61  Timing (in seconds)
% 9.71/3.61  ----------------------
% 9.71/3.62  Preprocessing        : 0.36
% 9.71/3.62  Parsing              : 0.19
% 9.71/3.62  CNF conversion       : 0.02
% 9.71/3.62  Main loop            : 2.43
% 9.71/3.62  Inferencing          : 0.56
% 9.71/3.62  Reduction            : 1.32
% 9.76/3.62  Demodulation         : 1.16
% 9.76/3.62  BG Simplification    : 0.07
% 9.76/3.62  Subsumption          : 0.36
% 9.76/3.62  Abstraction          : 0.10
% 9.76/3.62  MUC search           : 0.00
% 9.76/3.62  Cooper               : 0.00
% 9.76/3.62  Total                : 2.82
% 9.76/3.62  Index Insertion      : 0.00
% 9.76/3.62  Index Deletion       : 0.00
% 9.76/3.62  Index Matching       : 0.00
% 9.76/3.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
