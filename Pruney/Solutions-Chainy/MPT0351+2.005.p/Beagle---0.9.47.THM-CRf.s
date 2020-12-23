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
% DateTime   : Thu Dec  3 09:55:37 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 253 expanded)
%              Number of leaves         :   38 ( 100 expanded)
%              Depth                    :   17
%              Number of atoms          :   90 ( 389 expanded)
%              Number of equality atoms :   52 ( 126 expanded)
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

tff(f_67,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_80,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_72,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_50,axiom,(
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

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_52,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_69,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_40,plain,(
    ! [A_25] : k2_subset_1(A_25) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_50,plain,(
    k4_subset_1('#skF_3','#skF_4',k2_subset_1('#skF_3')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_53,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_50])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_31] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_44,plain,(
    ! [A_27] : ~ v1_xboole_0(k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_298,plain,(
    ! [B_60,A_61] :
      ( r2_hidden(B_60,A_61)
      | ~ m1_subset_1(B_60,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    ! [C_20,A_16] :
      ( r1_tarski(C_20,A_16)
      | ~ r2_hidden(C_20,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_302,plain,(
    ! [B_60,A_16] :
      ( r1_tarski(B_60,A_16)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_16))
      | v1_xboole_0(k1_zfmisc_1(A_16)) ) ),
    inference(resolution,[status(thm)],[c_298,c_18])).

tff(c_319,plain,(
    ! [B_64,A_65] :
      ( r1_tarski(B_64,A_65)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_65)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_302])).

tff(c_342,plain,(
    ! [A_67] : r1_tarski(k1_xboole_0,A_67) ),
    inference(resolution,[status(thm)],[c_48,c_319])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_346,plain,(
    ! [A_67] : k3_xboole_0(k1_xboole_0,A_67) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_342,c_8])).

tff(c_439,plain,(
    ! [A_71,B_72] : k5_xboole_0(A_71,k3_xboole_0(A_71,B_72)) = k4_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_501,plain,(
    ! [A_76] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_439])).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_514,plain,(
    ! [B_9] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,B_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_10])).

tff(c_530,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_514])).

tff(c_457,plain,(
    ! [A_67] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_439])).

tff(c_546,plain,(
    ! [A_77] : k4_xboole_0(k1_xboole_0,A_77) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_530,c_457])).

tff(c_12,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_558,plain,(
    ! [A_77] : k5_xboole_0(A_77,k1_xboole_0) = k2_xboole_0(A_77,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_546,c_12])).

tff(c_568,plain,(
    ! [A_77] : k5_xboole_0(A_77,k1_xboole_0) = A_77 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_558])).

tff(c_351,plain,(
    ! [A_68] : k3_xboole_0(k1_xboole_0,A_68) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_342,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_356,plain,(
    ! [A_68] : k3_xboole_0(A_68,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_2])).

tff(c_448,plain,(
    ! [A_68] : k5_xboole_0(A_68,k1_xboole_0) = k4_xboole_0(A_68,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_439])).

tff(c_619,plain,(
    ! [A_81] : k4_xboole_0(A_81,k1_xboole_0) = A_81 ),
    inference(demodulation,[status(thm),theory(equality)],[c_568,c_448])).

tff(c_629,plain,(
    ! [A_81] : k4_xboole_0(A_81,A_81) = k3_xboole_0(A_81,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_619,c_10])).

tff(c_642,plain,(
    ! [A_81] : k4_xboole_0(A_81,A_81) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_629])).

tff(c_14,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_144,plain,(
    ! [A_45,B_46] : k3_tarski(k2_tarski(A_45,B_46)) = k2_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_191,plain,(
    ! [B_55,A_56] : k3_tarski(k2_tarski(B_55,A_56)) = k2_xboole_0(A_56,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_144])).

tff(c_30,plain,(
    ! [A_21,B_22] : k3_tarski(k2_tarski(A_21,B_22)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_197,plain,(
    ! [B_55,A_56] : k2_xboole_0(B_55,A_56) = k2_xboole_0(A_56,B_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_30])).

tff(c_42,plain,(
    ! [A_26] : m1_subset_1(k2_subset_1(A_26),k1_zfmisc_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_54,plain,(
    ! [A_26] : m1_subset_1(A_26,k1_zfmisc_1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42])).

tff(c_337,plain,(
    ! [A_66] : r1_tarski(A_66,A_66) ),
    inference(resolution,[status(thm)],[c_54,c_319])).

tff(c_341,plain,(
    ! [A_66] : k3_xboole_0(A_66,A_66) = A_66 ),
    inference(resolution,[status(thm)],[c_337,c_8])).

tff(c_454,plain,(
    ! [A_66] : k5_xboole_0(A_66,A_66) = k4_xboole_0(A_66,A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_439])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_336,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_319])).

tff(c_350,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_336,c_8])).

tff(c_451,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_439])).

tff(c_491,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k4_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_451])).

tff(c_610,plain,(
    k5_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_4')) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_12])).

tff(c_614,plain,(
    k5_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_610])).

tff(c_797,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_568,c_642,c_614])).

tff(c_1404,plain,(
    ! [A_110,B_111,C_112] :
      ( k4_subset_1(A_110,B_111,C_112) = k2_xboole_0(B_111,C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(A_110))
      | ~ m1_subset_1(B_111,k1_zfmisc_1(A_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1526,plain,(
    ! [A_120,B_121] :
      ( k4_subset_1(A_120,B_121,A_120) = k2_xboole_0(B_121,A_120)
      | ~ m1_subset_1(B_121,k1_zfmisc_1(A_120)) ) ),
    inference(resolution,[status(thm)],[c_54,c_1404])).

tff(c_1537,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1526])).

tff(c_1545,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_797,c_1537])).

tff(c_1547,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1545])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:26:08 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.26/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.60  
% 3.26/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.60  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.26/1.60  
% 3.26/1.60  %Foreground sorts:
% 3.26/1.60  
% 3.26/1.60  
% 3.26/1.60  %Background operators:
% 3.26/1.60  
% 3.26/1.60  
% 3.26/1.60  %Foreground operators:
% 3.26/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.26/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.26/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.26/1.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.26/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.26/1.60  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.26/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.26/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.26/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.26/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.60  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.26/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.26/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.26/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.26/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.26/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.26/1.60  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.26/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.26/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.26/1.60  
% 3.26/1.62  tff(f_67, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.26/1.62  tff(f_85, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 3.26/1.62  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.26/1.62  tff(f_80, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.26/1.62  tff(f_72, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.26/1.62  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.26/1.62  tff(f_50, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.26/1.62  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.26/1.62  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.26/1.62  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.26/1.62  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.26/1.62  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.26/1.62  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.26/1.62  tff(f_52, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.26/1.62  tff(f_69, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.26/1.62  tff(f_78, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.26/1.62  tff(c_40, plain, (![A_25]: (k2_subset_1(A_25)=A_25)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.26/1.62  tff(c_50, plain, (k4_subset_1('#skF_3', '#skF_4', k2_subset_1('#skF_3'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.26/1.62  tff(c_53, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_50])).
% 3.26/1.62  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.26/1.62  tff(c_48, plain, (![A_31]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.26/1.62  tff(c_44, plain, (![A_27]: (~v1_xboole_0(k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.26/1.62  tff(c_298, plain, (![B_60, A_61]: (r2_hidden(B_60, A_61) | ~m1_subset_1(B_60, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.26/1.62  tff(c_18, plain, (![C_20, A_16]: (r1_tarski(C_20, A_16) | ~r2_hidden(C_20, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.26/1.62  tff(c_302, plain, (![B_60, A_16]: (r1_tarski(B_60, A_16) | ~m1_subset_1(B_60, k1_zfmisc_1(A_16)) | v1_xboole_0(k1_zfmisc_1(A_16)))), inference(resolution, [status(thm)], [c_298, c_18])).
% 3.26/1.62  tff(c_319, plain, (![B_64, A_65]: (r1_tarski(B_64, A_65) | ~m1_subset_1(B_64, k1_zfmisc_1(A_65)))), inference(negUnitSimplification, [status(thm)], [c_44, c_302])).
% 3.26/1.62  tff(c_342, plain, (![A_67]: (r1_tarski(k1_xboole_0, A_67))), inference(resolution, [status(thm)], [c_48, c_319])).
% 3.26/1.62  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.26/1.62  tff(c_346, plain, (![A_67]: (k3_xboole_0(k1_xboole_0, A_67)=k1_xboole_0)), inference(resolution, [status(thm)], [c_342, c_8])).
% 3.26/1.62  tff(c_439, plain, (![A_71, B_72]: (k5_xboole_0(A_71, k3_xboole_0(A_71, B_72))=k4_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.26/1.62  tff(c_501, plain, (![A_76]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_76))), inference(superposition, [status(thm), theory('equality')], [c_346, c_439])).
% 3.26/1.62  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.26/1.62  tff(c_514, plain, (![B_9]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k3_xboole_0(k1_xboole_0, B_9))), inference(superposition, [status(thm), theory('equality')], [c_501, c_10])).
% 3.26/1.62  tff(c_530, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_346, c_514])).
% 3.26/1.62  tff(c_457, plain, (![A_67]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_67))), inference(superposition, [status(thm), theory('equality')], [c_346, c_439])).
% 3.26/1.62  tff(c_546, plain, (![A_77]: (k4_xboole_0(k1_xboole_0, A_77)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_530, c_457])).
% 3.26/1.62  tff(c_12, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.26/1.62  tff(c_558, plain, (![A_77]: (k5_xboole_0(A_77, k1_xboole_0)=k2_xboole_0(A_77, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_546, c_12])).
% 3.26/1.62  tff(c_568, plain, (![A_77]: (k5_xboole_0(A_77, k1_xboole_0)=A_77)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_558])).
% 3.26/1.62  tff(c_351, plain, (![A_68]: (k3_xboole_0(k1_xboole_0, A_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_342, c_8])).
% 3.26/1.62  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.26/1.62  tff(c_356, plain, (![A_68]: (k3_xboole_0(A_68, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_351, c_2])).
% 3.26/1.62  tff(c_448, plain, (![A_68]: (k5_xboole_0(A_68, k1_xboole_0)=k4_xboole_0(A_68, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_356, c_439])).
% 3.26/1.62  tff(c_619, plain, (![A_81]: (k4_xboole_0(A_81, k1_xboole_0)=A_81)), inference(demodulation, [status(thm), theory('equality')], [c_568, c_448])).
% 3.26/1.62  tff(c_629, plain, (![A_81]: (k4_xboole_0(A_81, A_81)=k3_xboole_0(A_81, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_619, c_10])).
% 3.26/1.62  tff(c_642, plain, (![A_81]: (k4_xboole_0(A_81, A_81)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_356, c_629])).
% 3.26/1.62  tff(c_14, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.26/1.62  tff(c_144, plain, (![A_45, B_46]: (k3_tarski(k2_tarski(A_45, B_46))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.26/1.62  tff(c_191, plain, (![B_55, A_56]: (k3_tarski(k2_tarski(B_55, A_56))=k2_xboole_0(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_14, c_144])).
% 3.26/1.62  tff(c_30, plain, (![A_21, B_22]: (k3_tarski(k2_tarski(A_21, B_22))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.26/1.62  tff(c_197, plain, (![B_55, A_56]: (k2_xboole_0(B_55, A_56)=k2_xboole_0(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_191, c_30])).
% 3.26/1.62  tff(c_42, plain, (![A_26]: (m1_subset_1(k2_subset_1(A_26), k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.26/1.62  tff(c_54, plain, (![A_26]: (m1_subset_1(A_26, k1_zfmisc_1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42])).
% 3.26/1.62  tff(c_337, plain, (![A_66]: (r1_tarski(A_66, A_66))), inference(resolution, [status(thm)], [c_54, c_319])).
% 3.26/1.62  tff(c_341, plain, (![A_66]: (k3_xboole_0(A_66, A_66)=A_66)), inference(resolution, [status(thm)], [c_337, c_8])).
% 3.26/1.62  tff(c_454, plain, (![A_66]: (k5_xboole_0(A_66, A_66)=k4_xboole_0(A_66, A_66))), inference(superposition, [status(thm), theory('equality')], [c_341, c_439])).
% 3.26/1.62  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.26/1.62  tff(c_336, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_319])).
% 3.26/1.62  tff(c_350, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_336, c_8])).
% 3.26/1.62  tff(c_451, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_350, c_439])).
% 3.26/1.62  tff(c_491, plain, (k4_xboole_0('#skF_4', '#skF_3')=k4_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_454, c_451])).
% 3.26/1.62  tff(c_610, plain, (k5_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_4'))=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_491, c_12])).
% 3.26/1.62  tff(c_614, plain, (k5_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_197, c_610])).
% 3.26/1.62  tff(c_797, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_568, c_642, c_614])).
% 3.26/1.62  tff(c_1404, plain, (![A_110, B_111, C_112]: (k4_subset_1(A_110, B_111, C_112)=k2_xboole_0(B_111, C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(A_110)) | ~m1_subset_1(B_111, k1_zfmisc_1(A_110)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.26/1.62  tff(c_1526, plain, (![A_120, B_121]: (k4_subset_1(A_120, B_121, A_120)=k2_xboole_0(B_121, A_120) | ~m1_subset_1(B_121, k1_zfmisc_1(A_120)))), inference(resolution, [status(thm)], [c_54, c_1404])).
% 3.26/1.62  tff(c_1537, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')=k2_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_1526])).
% 3.26/1.62  tff(c_1545, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_797, c_1537])).
% 3.26/1.62  tff(c_1547, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_1545])).
% 3.26/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.62  
% 3.26/1.62  Inference rules
% 3.26/1.62  ----------------------
% 3.26/1.62  #Ref     : 0
% 3.26/1.62  #Sup     : 362
% 3.26/1.62  #Fact    : 0
% 3.26/1.62  #Define  : 0
% 3.26/1.62  #Split   : 0
% 3.26/1.62  #Chain   : 0
% 3.26/1.62  #Close   : 0
% 3.26/1.62  
% 3.26/1.62  Ordering : KBO
% 3.26/1.62  
% 3.26/1.62  Simplification rules
% 3.26/1.62  ----------------------
% 3.26/1.62  #Subsume      : 13
% 3.26/1.62  #Demod        : 320
% 3.26/1.62  #Tautology    : 257
% 3.26/1.62  #SimpNegUnit  : 3
% 3.26/1.62  #BackRed      : 4
% 3.26/1.62  
% 3.26/1.62  #Partial instantiations: 0
% 3.26/1.62  #Strategies tried      : 1
% 3.26/1.62  
% 3.26/1.62  Timing (in seconds)
% 3.26/1.62  ----------------------
% 3.26/1.62  Preprocessing        : 0.33
% 3.26/1.62  Parsing              : 0.17
% 3.26/1.62  CNF conversion       : 0.02
% 3.26/1.62  Main loop            : 0.52
% 3.26/1.62  Inferencing          : 0.18
% 3.26/1.62  Reduction            : 0.21
% 3.26/1.62  Demodulation         : 0.17
% 3.26/1.62  BG Simplification    : 0.02
% 3.26/1.62  Subsumption          : 0.07
% 3.26/1.62  Abstraction          : 0.03
% 3.26/1.62  MUC search           : 0.00
% 3.26/1.62  Cooper               : 0.00
% 3.26/1.62  Total                : 0.88
% 3.26/1.62  Index Insertion      : 0.00
% 3.26/1.62  Index Deletion       : 0.00
% 3.26/1.62  Index Matching       : 0.00
% 3.26/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
