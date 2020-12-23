%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:37 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 139 expanded)
%              Number of leaves         :   38 (  62 expanded)
%              Depth                    :   13
%              Number of atoms          :   83 ( 185 expanded)
%              Number of equality atoms :   45 (  72 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_80,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_72,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_52,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_69,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_40,plain,(
    ! [A_25] : k2_subset_1(A_25) = A_25 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_50,plain,(
    k4_subset_1('#skF_3','#skF_4',k2_subset_1('#skF_3')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_53,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_50])).

tff(c_8,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_48,plain,(
    ! [A_31] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_44,plain,(
    ! [A_27] : ~ v1_xboole_0(k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_341,plain,(
    ! [B_69,A_70] :
      ( r2_hidden(B_69,A_70)
      | ~ m1_subset_1(B_69,A_70)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    ! [C_20,A_16] :
      ( r1_tarski(C_20,A_16)
      | ~ r2_hidden(C_20,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_348,plain,(
    ! [B_69,A_16] :
      ( r1_tarski(B_69,A_16)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_16))
      | v1_xboole_0(k1_zfmisc_1(A_16)) ) ),
    inference(resolution,[status(thm)],[c_341,c_18])).

tff(c_384,plain,(
    ! [B_73,A_74] :
      ( r1_tarski(B_73,A_74)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_348])).

tff(c_411,plain,(
    ! [A_76] : r1_tarski(k1_xboole_0,A_76) ),
    inference(resolution,[status(thm)],[c_48,c_384])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_444,plain,(
    ! [A_80] : k3_xboole_0(k1_xboole_0,A_80) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_411,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_491,plain,(
    ! [A_81] : k3_xboole_0(A_81,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_503,plain,(
    ! [A_81] : k5_xboole_0(A_81,k1_xboole_0) = k4_xboole_0(A_81,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_4])).

tff(c_530,plain,(
    ! [A_81] : k5_xboole_0(A_81,k1_xboole_0) = A_81 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_503])).

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

tff(c_456,plain,(
    ! [A_80] : k3_xboole_0(A_80,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_2])).

tff(c_247,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k4_xboole_0(A_59,B_60)) = k3_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_262,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_247])).

tff(c_42,plain,(
    ! [A_26] : m1_subset_1(k2_subset_1(A_26),k1_zfmisc_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_54,plain,(
    ! [A_26] : m1_subset_1(A_26,k1_zfmisc_1(A_26)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42])).

tff(c_406,plain,(
    ! [A_75] : r1_tarski(A_75,A_75) ),
    inference(resolution,[status(thm)],[c_54,c_384])).

tff(c_431,plain,(
    ! [A_79] : k3_xboole_0(A_79,A_79) = A_79 ),
    inference(resolution,[status(thm)],[c_406,c_6])).

tff(c_437,plain,(
    ! [A_79] : k5_xboole_0(A_79,A_79) = k4_xboole_0(A_79,A_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_4])).

tff(c_442,plain,(
    ! [A_79] : k5_xboole_0(A_79,A_79) = k3_xboole_0(A_79,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_437])).

tff(c_627,plain,(
    ! [A_79] : k5_xboole_0(A_79,A_79) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_442])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_405,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_384])).

tff(c_419,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_405,c_6])).

tff(c_482,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_4])).

tff(c_628,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_627,c_482])).

tff(c_12,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_659,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_12])).

tff(c_665,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_530,c_197,c_659])).

tff(c_900,plain,(
    ! [A_98,B_99,C_100] :
      ( k4_subset_1(A_98,B_99,C_100) = k2_xboole_0(B_99,C_100)
      | ~ m1_subset_1(C_100,k1_zfmisc_1(A_98))
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_98)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1200,plain,(
    ! [A_113,B_114] :
      ( k4_subset_1(A_113,B_114,A_113) = k2_xboole_0(B_114,A_113)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(A_113)) ) ),
    inference(resolution,[status(thm)],[c_54,c_900])).

tff(c_1211,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_1200])).

tff(c_1219,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_665,c_1211])).

tff(c_1221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_1219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:32:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.41  
% 2.95/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.41  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.95/1.41  
% 2.95/1.41  %Foreground sorts:
% 2.95/1.41  
% 2.95/1.41  
% 2.95/1.41  %Background operators:
% 2.95/1.41  
% 2.95/1.41  
% 2.95/1.41  %Foreground operators:
% 2.95/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.95/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.95/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.95/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.95/1.41  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.95/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.95/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.95/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.41  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.95/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.95/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.95/1.41  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.95/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.95/1.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.95/1.41  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.95/1.41  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.95/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.95/1.41  
% 2.95/1.42  tff(f_67, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.95/1.42  tff(f_85, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 2.95/1.42  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.95/1.42  tff(f_80, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.95/1.42  tff(f_72, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.95/1.42  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.95/1.42  tff(f_50, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.95/1.42  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.95/1.42  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.95/1.42  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.95/1.42  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.95/1.42  tff(f_52, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.95/1.42  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.95/1.42  tff(f_69, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.95/1.42  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.95/1.42  tff(f_78, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.95/1.42  tff(c_40, plain, (![A_25]: (k2_subset_1(A_25)=A_25)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.95/1.42  tff(c_50, plain, (k4_subset_1('#skF_3', '#skF_4', k2_subset_1('#skF_3'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.95/1.42  tff(c_53, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_50])).
% 2.95/1.42  tff(c_8, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.95/1.42  tff(c_48, plain, (![A_31]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.95/1.42  tff(c_44, plain, (![A_27]: (~v1_xboole_0(k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.95/1.42  tff(c_341, plain, (![B_69, A_70]: (r2_hidden(B_69, A_70) | ~m1_subset_1(B_69, A_70) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.95/1.42  tff(c_18, plain, (![C_20, A_16]: (r1_tarski(C_20, A_16) | ~r2_hidden(C_20, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.95/1.42  tff(c_348, plain, (![B_69, A_16]: (r1_tarski(B_69, A_16) | ~m1_subset_1(B_69, k1_zfmisc_1(A_16)) | v1_xboole_0(k1_zfmisc_1(A_16)))), inference(resolution, [status(thm)], [c_341, c_18])).
% 2.95/1.42  tff(c_384, plain, (![B_73, A_74]: (r1_tarski(B_73, A_74) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)))), inference(negUnitSimplification, [status(thm)], [c_44, c_348])).
% 2.95/1.42  tff(c_411, plain, (![A_76]: (r1_tarski(k1_xboole_0, A_76))), inference(resolution, [status(thm)], [c_48, c_384])).
% 2.95/1.42  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.95/1.42  tff(c_444, plain, (![A_80]: (k3_xboole_0(k1_xboole_0, A_80)=k1_xboole_0)), inference(resolution, [status(thm)], [c_411, c_6])).
% 2.95/1.42  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.95/1.42  tff(c_491, plain, (![A_81]: (k3_xboole_0(A_81, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_444, c_2])).
% 2.95/1.42  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.95/1.42  tff(c_503, plain, (![A_81]: (k5_xboole_0(A_81, k1_xboole_0)=k4_xboole_0(A_81, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_491, c_4])).
% 2.95/1.42  tff(c_530, plain, (![A_81]: (k5_xboole_0(A_81, k1_xboole_0)=A_81)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_503])).
% 2.95/1.42  tff(c_14, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.95/1.42  tff(c_144, plain, (![A_45, B_46]: (k3_tarski(k2_tarski(A_45, B_46))=k2_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.95/1.42  tff(c_191, plain, (![B_55, A_56]: (k3_tarski(k2_tarski(B_55, A_56))=k2_xboole_0(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_14, c_144])).
% 2.95/1.42  tff(c_30, plain, (![A_21, B_22]: (k3_tarski(k2_tarski(A_21, B_22))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.95/1.42  tff(c_197, plain, (![B_55, A_56]: (k2_xboole_0(B_55, A_56)=k2_xboole_0(A_56, B_55))), inference(superposition, [status(thm), theory('equality')], [c_191, c_30])).
% 2.95/1.42  tff(c_456, plain, (![A_80]: (k3_xboole_0(A_80, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_444, c_2])).
% 2.95/1.42  tff(c_247, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k4_xboole_0(A_59, B_60))=k3_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.95/1.42  tff(c_262, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_247])).
% 2.95/1.42  tff(c_42, plain, (![A_26]: (m1_subset_1(k2_subset_1(A_26), k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.95/1.42  tff(c_54, plain, (![A_26]: (m1_subset_1(A_26, k1_zfmisc_1(A_26)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42])).
% 2.95/1.42  tff(c_406, plain, (![A_75]: (r1_tarski(A_75, A_75))), inference(resolution, [status(thm)], [c_54, c_384])).
% 2.95/1.42  tff(c_431, plain, (![A_79]: (k3_xboole_0(A_79, A_79)=A_79)), inference(resolution, [status(thm)], [c_406, c_6])).
% 2.95/1.42  tff(c_437, plain, (![A_79]: (k5_xboole_0(A_79, A_79)=k4_xboole_0(A_79, A_79))), inference(superposition, [status(thm), theory('equality')], [c_431, c_4])).
% 2.95/1.42  tff(c_442, plain, (![A_79]: (k5_xboole_0(A_79, A_79)=k3_xboole_0(A_79, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_437])).
% 2.95/1.42  tff(c_627, plain, (![A_79]: (k5_xboole_0(A_79, A_79)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_456, c_442])).
% 2.95/1.42  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.95/1.42  tff(c_405, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_384])).
% 2.95/1.42  tff(c_419, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_405, c_6])).
% 2.95/1.42  tff(c_482, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_419, c_4])).
% 2.95/1.42  tff(c_628, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_627, c_482])).
% 2.95/1.42  tff(c_12, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.95/1.42  tff(c_659, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_628, c_12])).
% 2.95/1.42  tff(c_665, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_530, c_197, c_659])).
% 2.95/1.42  tff(c_900, plain, (![A_98, B_99, C_100]: (k4_subset_1(A_98, B_99, C_100)=k2_xboole_0(B_99, C_100) | ~m1_subset_1(C_100, k1_zfmisc_1(A_98)) | ~m1_subset_1(B_99, k1_zfmisc_1(A_98)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.95/1.42  tff(c_1200, plain, (![A_113, B_114]: (k4_subset_1(A_113, B_114, A_113)=k2_xboole_0(B_114, A_113) | ~m1_subset_1(B_114, k1_zfmisc_1(A_113)))), inference(resolution, [status(thm)], [c_54, c_900])).
% 2.95/1.42  tff(c_1211, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')=k2_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_1200])).
% 2.95/1.42  tff(c_1219, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_665, c_1211])).
% 2.95/1.42  tff(c_1221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_1219])).
% 2.95/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.42  
% 2.95/1.42  Inference rules
% 2.95/1.42  ----------------------
% 2.95/1.42  #Ref     : 0
% 2.95/1.42  #Sup     : 279
% 2.95/1.42  #Fact    : 0
% 2.95/1.42  #Define  : 0
% 2.95/1.42  #Split   : 0
% 2.95/1.42  #Chain   : 0
% 2.95/1.42  #Close   : 0
% 2.95/1.42  
% 2.95/1.42  Ordering : KBO
% 2.95/1.42  
% 2.95/1.42  Simplification rules
% 2.95/1.42  ----------------------
% 2.95/1.42  #Subsume      : 10
% 2.95/1.42  #Demod        : 161
% 2.95/1.42  #Tautology    : 209
% 2.95/1.42  #SimpNegUnit  : 3
% 2.95/1.42  #BackRed      : 3
% 2.95/1.42  
% 2.95/1.42  #Partial instantiations: 0
% 2.95/1.42  #Strategies tried      : 1
% 2.95/1.42  
% 2.95/1.42  Timing (in seconds)
% 2.95/1.42  ----------------------
% 2.95/1.43  Preprocessing        : 0.31
% 2.95/1.43  Parsing              : 0.16
% 2.95/1.43  CNF conversion       : 0.02
% 2.95/1.43  Main loop            : 0.36
% 2.95/1.43  Inferencing          : 0.13
% 2.95/1.43  Reduction            : 0.13
% 2.95/1.43  Demodulation         : 0.10
% 2.95/1.43  BG Simplification    : 0.02
% 2.95/1.43  Subsumption          : 0.05
% 2.95/1.43  Abstraction          : 0.02
% 2.95/1.43  MUC search           : 0.00
% 2.95/1.43  Cooper               : 0.00
% 2.95/1.43  Total                : 0.70
% 2.95/1.43  Index Insertion      : 0.00
% 2.95/1.43  Index Deletion       : 0.00
% 2.95/1.43  Index Matching       : 0.00
% 2.95/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
