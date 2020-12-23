%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:27 EST 2020

% Result     : Theorem 4.70s
% Output     : CNFRefutation 4.70s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 144 expanded)
%              Number of leaves         :   38 (  65 expanded)
%              Depth                    :   11
%              Number of atoms          :   90 ( 197 expanded)
%              Number of equality atoms :   42 (  80 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_69,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_54,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_76,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_42,plain,(
    ! [A_29] : k2_subset_1(A_29) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_50,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_53,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_50])).

tff(c_14,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_199,plain,(
    ! [A_58,B_59] : k3_tarski(k2_tarski(A_58,B_59)) = k2_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_219,plain,(
    ! [B_62,A_63] : k3_tarski(k2_tarski(B_62,A_63)) = k2_xboole_0(A_63,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_199])).

tff(c_32,plain,(
    ! [A_25,B_26] : k3_tarski(k2_tarski(A_25,B_26)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_225,plain,(
    ! [B_62,A_63] : k2_xboole_0(B_62,A_63) = k2_xboole_0(A_63,B_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_32])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_46,plain,(
    ! [A_32] : ~ v1_xboole_0(k1_zfmisc_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_303,plain,(
    ! [B_72,A_73] :
      ( r2_hidden(B_72,A_73)
      | ~ m1_subset_1(B_72,A_73)
      | v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    ! [C_24,A_20] :
      ( r1_tarski(C_24,A_20)
      | ~ r2_hidden(C_24,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_310,plain,(
    ! [B_72,A_20] :
      ( r1_tarski(B_72,A_20)
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_20))
      | v1_xboole_0(k1_zfmisc_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_303,c_20])).

tff(c_324,plain,(
    ! [B_77,A_78] :
      ( r1_tarski(B_77,A_78)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_78)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_310])).

tff(c_337,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_324])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_341,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_337,c_8])).

tff(c_107,plain,(
    ! [B_44,A_45] : k3_xboole_0(B_44,A_45) = k3_xboole_0(A_45,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_122,plain,(
    ! [A_45,B_44] : k2_xboole_0(A_45,k3_xboole_0(B_44,A_45)) = A_45 ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_6])).

tff(c_348,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_122])).

tff(c_368,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_348])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_382,plain,(
    ! [A_79,B_80] :
      ( k4_xboole_0(A_79,B_80) = k3_subset_1(A_79,B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_395,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_382])).

tff(c_288,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_440,plain,(
    ! [B_81,A_82] : k5_xboole_0(B_81,k3_xboole_0(A_82,B_81)) = k4_xboole_0(B_81,A_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_288])).

tff(c_456,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_440])).

tff(c_470,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_456])).

tff(c_530,plain,(
    ! [A_87,B_88] : k2_xboole_0(k5_xboole_0(A_87,B_88),k3_xboole_0(A_87,B_88)) = k2_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_548,plain,(
    k2_xboole_0(k3_subset_1('#skF_3','#skF_4'),k3_xboole_0('#skF_3','#skF_4')) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_470,c_530])).

tff(c_579,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_225,c_341,c_225,c_2,c_548])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_tarski(k4_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_399,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_395,c_10])).

tff(c_22,plain,(
    ! [C_24,A_20] :
      ( r2_hidden(C_24,k1_zfmisc_1(A_20))
      | ~ r1_tarski(C_24,A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_275,plain,(
    ! [B_66,A_67] :
      ( m1_subset_1(B_66,A_67)
      | ~ r2_hidden(B_66,A_67)
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_278,plain,(
    ! [C_24,A_20] :
      ( m1_subset_1(C_24,k1_zfmisc_1(A_20))
      | v1_xboole_0(k1_zfmisc_1(A_20))
      | ~ r1_tarski(C_24,A_20) ) ),
    inference(resolution,[status(thm)],[c_22,c_275])).

tff(c_281,plain,(
    ! [C_24,A_20] :
      ( m1_subset_1(C_24,k1_zfmisc_1(A_20))
      | ~ r1_tarski(C_24,A_20) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_278])).

tff(c_1114,plain,(
    ! [A_117,B_118,C_119] :
      ( k4_subset_1(A_117,B_118,C_119) = k2_xboole_0(B_118,C_119)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(A_117))
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_117)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2447,plain,(
    ! [A_175,B_176,C_177] :
      ( k4_subset_1(A_175,B_176,C_177) = k2_xboole_0(B_176,C_177)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(A_175))
      | ~ r1_tarski(C_177,A_175) ) ),
    inference(resolution,[status(thm)],[c_281,c_1114])).

tff(c_2464,plain,(
    ! [C_178] :
      ( k4_subset_1('#skF_3','#skF_4',C_178) = k2_xboole_0('#skF_4',C_178)
      | ~ r1_tarski(C_178,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_52,c_2447])).

tff(c_2500,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_399,c_2464])).

tff(c_2517,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_2500])).

tff(c_2519,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_2517])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.70/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.70/1.92  
% 4.70/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.70/1.93  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.70/1.93  
% 4.70/1.93  %Foreground sorts:
% 4.70/1.93  
% 4.70/1.93  
% 4.70/1.93  %Background operators:
% 4.70/1.93  
% 4.70/1.93  
% 4.70/1.93  %Foreground operators:
% 4.70/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.70/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.70/1.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.70/1.93  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.70/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.70/1.93  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.70/1.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.70/1.93  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.70/1.93  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.70/1.93  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.70/1.93  tff('#skF_3', type, '#skF_3': $i).
% 4.70/1.93  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.70/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.70/1.93  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.70/1.93  tff('#skF_4', type, '#skF_4': $i).
% 4.70/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.70/1.93  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.70/1.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.70/1.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.70/1.93  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.70/1.93  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.70/1.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.70/1.93  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.70/1.93  
% 4.70/1.94  tff(f_69, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.70/1.94  tff(f_87, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 4.70/1.94  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.70/1.94  tff(f_54, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.70/1.94  tff(f_76, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.70/1.94  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.70/1.94  tff(f_52, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.70/1.94  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.70/1.94  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.70/1.94  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 4.70/1.94  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.70/1.94  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.70/1.94  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 4.70/1.94  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.70/1.94  tff(f_82, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.70/1.94  tff(c_42, plain, (![A_29]: (k2_subset_1(A_29)=A_29)), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.70/1.94  tff(c_50, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.70/1.94  tff(c_53, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_50])).
% 4.70/1.94  tff(c_14, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.70/1.94  tff(c_199, plain, (![A_58, B_59]: (k3_tarski(k2_tarski(A_58, B_59))=k2_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.70/1.94  tff(c_219, plain, (![B_62, A_63]: (k3_tarski(k2_tarski(B_62, A_63))=k2_xboole_0(A_63, B_62))), inference(superposition, [status(thm), theory('equality')], [c_14, c_199])).
% 4.70/1.94  tff(c_32, plain, (![A_25, B_26]: (k3_tarski(k2_tarski(A_25, B_26))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.70/1.94  tff(c_225, plain, (![B_62, A_63]: (k2_xboole_0(B_62, A_63)=k2_xboole_0(A_63, B_62))), inference(superposition, [status(thm), theory('equality')], [c_219, c_32])).
% 4.70/1.94  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.70/1.94  tff(c_46, plain, (![A_32]: (~v1_xboole_0(k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.70/1.94  tff(c_303, plain, (![B_72, A_73]: (r2_hidden(B_72, A_73) | ~m1_subset_1(B_72, A_73) | v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.70/1.94  tff(c_20, plain, (![C_24, A_20]: (r1_tarski(C_24, A_20) | ~r2_hidden(C_24, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.70/1.94  tff(c_310, plain, (![B_72, A_20]: (r1_tarski(B_72, A_20) | ~m1_subset_1(B_72, k1_zfmisc_1(A_20)) | v1_xboole_0(k1_zfmisc_1(A_20)))), inference(resolution, [status(thm)], [c_303, c_20])).
% 4.70/1.94  tff(c_324, plain, (![B_77, A_78]: (r1_tarski(B_77, A_78) | ~m1_subset_1(B_77, k1_zfmisc_1(A_78)))), inference(negUnitSimplification, [status(thm)], [c_46, c_310])).
% 4.70/1.94  tff(c_337, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_324])).
% 4.70/1.94  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.70/1.94  tff(c_341, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_337, c_8])).
% 4.70/1.94  tff(c_107, plain, (![B_44, A_45]: (k3_xboole_0(B_44, A_45)=k3_xboole_0(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.70/1.94  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.70/1.94  tff(c_122, plain, (![A_45, B_44]: (k2_xboole_0(A_45, k3_xboole_0(B_44, A_45))=A_45)), inference(superposition, [status(thm), theory('equality')], [c_107, c_6])).
% 4.70/1.94  tff(c_348, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_341, c_122])).
% 4.70/1.94  tff(c_368, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_225, c_348])).
% 4.70/1.94  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.70/1.94  tff(c_382, plain, (![A_79, B_80]: (k4_xboole_0(A_79, B_80)=k3_subset_1(A_79, B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(A_79)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.70/1.94  tff(c_395, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_382])).
% 4.70/1.94  tff(c_288, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.70/1.94  tff(c_440, plain, (![B_81, A_82]: (k5_xboole_0(B_81, k3_xboole_0(A_82, B_81))=k4_xboole_0(B_81, A_82))), inference(superposition, [status(thm), theory('equality')], [c_2, c_288])).
% 4.70/1.94  tff(c_456, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_341, c_440])).
% 4.70/1.94  tff(c_470, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_395, c_456])).
% 4.70/1.94  tff(c_530, plain, (![A_87, B_88]: (k2_xboole_0(k5_xboole_0(A_87, B_88), k3_xboole_0(A_87, B_88))=k2_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.70/1.94  tff(c_548, plain, (k2_xboole_0(k3_subset_1('#skF_3', '#skF_4'), k3_xboole_0('#skF_3', '#skF_4'))=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_470, c_530])).
% 4.70/1.94  tff(c_579, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_368, c_225, c_341, c_225, c_2, c_548])).
% 4.70/1.94  tff(c_10, plain, (![A_9, B_10]: (r1_tarski(k4_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.70/1.94  tff(c_399, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_395, c_10])).
% 4.70/1.94  tff(c_22, plain, (![C_24, A_20]: (r2_hidden(C_24, k1_zfmisc_1(A_20)) | ~r1_tarski(C_24, A_20))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.70/1.94  tff(c_275, plain, (![B_66, A_67]: (m1_subset_1(B_66, A_67) | ~r2_hidden(B_66, A_67) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.70/1.94  tff(c_278, plain, (![C_24, A_20]: (m1_subset_1(C_24, k1_zfmisc_1(A_20)) | v1_xboole_0(k1_zfmisc_1(A_20)) | ~r1_tarski(C_24, A_20))), inference(resolution, [status(thm)], [c_22, c_275])).
% 4.70/1.94  tff(c_281, plain, (![C_24, A_20]: (m1_subset_1(C_24, k1_zfmisc_1(A_20)) | ~r1_tarski(C_24, A_20))), inference(negUnitSimplification, [status(thm)], [c_46, c_278])).
% 4.70/1.94  tff(c_1114, plain, (![A_117, B_118, C_119]: (k4_subset_1(A_117, B_118, C_119)=k2_xboole_0(B_118, C_119) | ~m1_subset_1(C_119, k1_zfmisc_1(A_117)) | ~m1_subset_1(B_118, k1_zfmisc_1(A_117)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.70/1.94  tff(c_2447, plain, (![A_175, B_176, C_177]: (k4_subset_1(A_175, B_176, C_177)=k2_xboole_0(B_176, C_177) | ~m1_subset_1(B_176, k1_zfmisc_1(A_175)) | ~r1_tarski(C_177, A_175))), inference(resolution, [status(thm)], [c_281, c_1114])).
% 4.70/1.94  tff(c_2464, plain, (![C_178]: (k4_subset_1('#skF_3', '#skF_4', C_178)=k2_xboole_0('#skF_4', C_178) | ~r1_tarski(C_178, '#skF_3'))), inference(resolution, [status(thm)], [c_52, c_2447])).
% 4.70/1.94  tff(c_2500, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_399, c_2464])).
% 4.70/1.94  tff(c_2517, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_579, c_2500])).
% 4.70/1.94  tff(c_2519, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_2517])).
% 4.70/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.70/1.94  
% 4.70/1.94  Inference rules
% 4.70/1.94  ----------------------
% 4.70/1.94  #Ref     : 0
% 4.70/1.94  #Sup     : 616
% 4.70/1.95  #Fact    : 0
% 4.70/1.95  #Define  : 0
% 4.70/1.95  #Split   : 0
% 4.70/1.95  #Chain   : 0
% 4.70/1.95  #Close   : 0
% 4.70/1.95  
% 4.70/1.95  Ordering : KBO
% 4.70/1.95  
% 4.70/1.95  Simplification rules
% 4.70/1.95  ----------------------
% 4.70/1.95  #Subsume      : 13
% 4.70/1.95  #Demod        : 563
% 4.70/1.95  #Tautology    : 355
% 4.70/1.95  #SimpNegUnit  : 11
% 4.70/1.95  #BackRed      : 3
% 4.70/1.95  
% 4.70/1.95  #Partial instantiations: 0
% 4.70/1.95  #Strategies tried      : 1
% 4.70/1.95  
% 4.70/1.95  Timing (in seconds)
% 4.70/1.95  ----------------------
% 4.70/1.95  Preprocessing        : 0.34
% 4.70/1.95  Parsing              : 0.19
% 4.70/1.95  CNF conversion       : 0.02
% 4.70/1.95  Main loop            : 0.76
% 4.70/1.95  Inferencing          : 0.26
% 4.70/1.95  Reduction            : 0.31
% 4.70/1.95  Demodulation         : 0.25
% 4.70/1.95  BG Simplification    : 0.03
% 4.70/1.95  Subsumption          : 0.11
% 4.70/1.95  Abstraction          : 0.04
% 4.70/1.95  MUC search           : 0.00
% 4.70/1.95  Cooper               : 0.00
% 4.70/1.95  Total                : 1.14
% 4.70/1.95  Index Insertion      : 0.00
% 4.70/1.95  Index Deletion       : 0.00
% 4.70/1.95  Index Matching       : 0.00
% 4.70/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
