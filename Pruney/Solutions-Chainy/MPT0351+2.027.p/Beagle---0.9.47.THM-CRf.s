%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:40 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 101 expanded)
%              Number of leaves         :   37 (  50 expanded)
%              Depth                    :   12
%              Number of atoms          :   72 ( 116 expanded)
%              Number of equality atoms :   37 (  53 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_52,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_69,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

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
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_40,plain,(
    ! [A_26] : k2_subset_1(A_26) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_48,plain,(
    k4_subset_1('#skF_3','#skF_4',k2_subset_1('#skF_3')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_51,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_40,c_48])).

tff(c_12,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_147,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_168,plain,(
    ! [A_55,B_56] : k3_tarski(k2_tarski(A_55,B_56)) = k2_xboole_0(B_56,A_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_147])).

tff(c_30,plain,(
    ! [A_22,B_23] : k3_tarski(k2_tarski(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_174,plain,(
    ! [B_56,A_55] : k2_xboole_0(B_56,A_55) = k2_xboole_0(A_55,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_30])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_73,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k2_xboole_0(A_36,B_37)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_80,plain,(
    ! [A_3] : k4_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_73])).

tff(c_42,plain,(
    ! [A_27] : m1_subset_1(k2_subset_1(A_27),k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_52,plain,(
    ! [A_27] : m1_subset_1(A_27,k1_zfmisc_1(A_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42])).

tff(c_44,plain,(
    ! [A_28] : ~ v1_xboole_0(k1_zfmisc_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_284,plain,(
    ! [B_60,A_61] :
      ( r2_hidden(B_60,A_61)
      | ~ m1_subset_1(B_60,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    ! [C_21,A_17] :
      ( r1_tarski(C_21,A_17)
      | ~ r2_hidden(C_21,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_288,plain,(
    ! [B_60,A_17] :
      ( r1_tarski(B_60,A_17)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_284,c_18])).

tff(c_480,plain,(
    ! [B_71,A_72] :
      ( r1_tarski(B_71,A_72)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_288])).

tff(c_494,plain,(
    ! [A_73] : r1_tarski(A_73,A_73) ),
    inference(resolution,[status(thm)],[c_52,c_480])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( k3_xboole_0(A_4,B_5) = A_4
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_514,plain,(
    ! [A_76] : k3_xboole_0(A_76,A_76) = A_76 ),
    inference(resolution,[status(thm)],[c_494,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_520,plain,(
    ! [A_76] : k5_xboole_0(A_76,A_76) = k4_xboole_0(A_76,A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_2])).

tff(c_525,plain,(
    ! [A_76] : k5_xboole_0(A_76,A_76) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_520])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_493,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_480])).

tff(c_502,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_493,c_6])).

tff(c_530,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_502,c_2])).

tff(c_541,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_525,c_530])).

tff(c_8,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_545,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_8])).

tff(c_548,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_4,c_545])).

tff(c_1352,plain,(
    ! [A_105,B_106,C_107] :
      ( k4_subset_1(A_105,B_106,C_107) = k2_xboole_0(B_106,C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(A_105))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1908,plain,(
    ! [A_116,B_117] :
      ( k4_subset_1(A_116,B_117,A_116) = k2_xboole_0(B_117,A_116)
      | ~ m1_subset_1(B_117,k1_zfmisc_1(A_116)) ) ),
    inference(resolution,[status(thm)],[c_52,c_1352])).

tff(c_1917,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1908])).

tff(c_1923,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_1917])).

tff(c_1925,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_1923])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:00:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.52  
% 3.31/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.52  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.31/1.52  
% 3.31/1.52  %Foreground sorts:
% 3.31/1.52  
% 3.31/1.52  
% 3.31/1.52  %Background operators:
% 3.31/1.52  
% 3.31/1.52  
% 3.31/1.52  %Foreground operators:
% 3.31/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.31/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.31/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.31/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.31/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.31/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.31/1.52  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.31/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.31/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.52  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.31/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.31/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.31/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.31/1.52  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.31/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.31/1.52  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.31/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.31/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.52  
% 3.31/1.53  tff(f_67, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.31/1.53  tff(f_83, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 3.31/1.53  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.31/1.53  tff(f_52, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.31/1.53  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.31/1.53  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.31/1.53  tff(f_69, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.31/1.53  tff(f_72, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.31/1.53  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.31/1.53  tff(f_50, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.31/1.53  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.31/1.53  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.31/1.53  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.31/1.53  tff(f_78, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.31/1.53  tff(c_40, plain, (![A_26]: (k2_subset_1(A_26)=A_26)), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.31/1.53  tff(c_48, plain, (k4_subset_1('#skF_3', '#skF_4', k2_subset_1('#skF_3'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.31/1.53  tff(c_51, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_40, c_48])).
% 3.31/1.53  tff(c_12, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.31/1.53  tff(c_147, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.31/1.53  tff(c_168, plain, (![A_55, B_56]: (k3_tarski(k2_tarski(A_55, B_56))=k2_xboole_0(B_56, A_55))), inference(superposition, [status(thm), theory('equality')], [c_12, c_147])).
% 3.31/1.53  tff(c_30, plain, (![A_22, B_23]: (k3_tarski(k2_tarski(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.31/1.53  tff(c_174, plain, (![B_56, A_55]: (k2_xboole_0(B_56, A_55)=k2_xboole_0(A_55, B_56))), inference(superposition, [status(thm), theory('equality')], [c_168, c_30])).
% 3.31/1.53  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.31/1.53  tff(c_73, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k2_xboole_0(A_36, B_37))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.31/1.53  tff(c_80, plain, (![A_3]: (k4_xboole_0(A_3, A_3)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_73])).
% 3.31/1.53  tff(c_42, plain, (![A_27]: (m1_subset_1(k2_subset_1(A_27), k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.31/1.53  tff(c_52, plain, (![A_27]: (m1_subset_1(A_27, k1_zfmisc_1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42])).
% 3.31/1.53  tff(c_44, plain, (![A_28]: (~v1_xboole_0(k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.31/1.53  tff(c_284, plain, (![B_60, A_61]: (r2_hidden(B_60, A_61) | ~m1_subset_1(B_60, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.31/1.53  tff(c_18, plain, (![C_21, A_17]: (r1_tarski(C_21, A_17) | ~r2_hidden(C_21, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.31/1.53  tff(c_288, plain, (![B_60, A_17]: (r1_tarski(B_60, A_17) | ~m1_subset_1(B_60, k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)))), inference(resolution, [status(thm)], [c_284, c_18])).
% 3.31/1.53  tff(c_480, plain, (![B_71, A_72]: (r1_tarski(B_71, A_72) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)))), inference(negUnitSimplification, [status(thm)], [c_44, c_288])).
% 3.31/1.53  tff(c_494, plain, (![A_73]: (r1_tarski(A_73, A_73))), inference(resolution, [status(thm)], [c_52, c_480])).
% 3.31/1.53  tff(c_6, plain, (![A_4, B_5]: (k3_xboole_0(A_4, B_5)=A_4 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.31/1.53  tff(c_514, plain, (![A_76]: (k3_xboole_0(A_76, A_76)=A_76)), inference(resolution, [status(thm)], [c_494, c_6])).
% 3.31/1.53  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.31/1.53  tff(c_520, plain, (![A_76]: (k5_xboole_0(A_76, A_76)=k4_xboole_0(A_76, A_76))), inference(superposition, [status(thm), theory('equality')], [c_514, c_2])).
% 3.31/1.53  tff(c_525, plain, (![A_76]: (k5_xboole_0(A_76, A_76)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_520])).
% 3.31/1.53  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.31/1.53  tff(c_493, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_480])).
% 3.31/1.53  tff(c_502, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_493, c_6])).
% 3.31/1.53  tff(c_530, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_502, c_2])).
% 3.31/1.53  tff(c_541, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_525, c_530])).
% 3.31/1.53  tff(c_8, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.31/1.53  tff(c_545, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_541, c_8])).
% 3.31/1.53  tff(c_548, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_174, c_4, c_545])).
% 3.31/1.53  tff(c_1352, plain, (![A_105, B_106, C_107]: (k4_subset_1(A_105, B_106, C_107)=k2_xboole_0(B_106, C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(A_105)) | ~m1_subset_1(B_106, k1_zfmisc_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.31/1.53  tff(c_1908, plain, (![A_116, B_117]: (k4_subset_1(A_116, B_117, A_116)=k2_xboole_0(B_117, A_116) | ~m1_subset_1(B_117, k1_zfmisc_1(A_116)))), inference(resolution, [status(thm)], [c_52, c_1352])).
% 3.31/1.53  tff(c_1917, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')=k2_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_1908])).
% 3.31/1.53  tff(c_1923, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_548, c_1917])).
% 3.31/1.53  tff(c_1925, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_1923])).
% 3.31/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.53  
% 3.31/1.53  Inference rules
% 3.31/1.53  ----------------------
% 3.31/1.53  #Ref     : 0
% 3.31/1.53  #Sup     : 460
% 3.31/1.53  #Fact    : 0
% 3.31/1.53  #Define  : 0
% 3.31/1.53  #Split   : 0
% 3.31/1.53  #Chain   : 0
% 3.31/1.53  #Close   : 0
% 3.31/1.53  
% 3.31/1.53  Ordering : KBO
% 3.31/1.53  
% 3.31/1.53  Simplification rules
% 3.31/1.53  ----------------------
% 3.31/1.53  #Subsume      : 22
% 3.31/1.53  #Demod        : 480
% 3.31/1.53  #Tautology    : 355
% 3.31/1.53  #SimpNegUnit  : 3
% 3.31/1.53  #BackRed      : 0
% 3.31/1.53  
% 3.31/1.53  #Partial instantiations: 0
% 3.31/1.53  #Strategies tried      : 1
% 3.31/1.53  
% 3.31/1.53  Timing (in seconds)
% 3.31/1.53  ----------------------
% 3.31/1.53  Preprocessing        : 0.31
% 3.31/1.53  Parsing              : 0.16
% 3.31/1.53  CNF conversion       : 0.02
% 3.31/1.53  Main loop            : 0.45
% 3.31/1.53  Inferencing          : 0.14
% 3.31/1.53  Reduction            : 0.20
% 3.31/1.53  Demodulation         : 0.16
% 3.31/1.53  BG Simplification    : 0.02
% 3.31/1.53  Subsumption          : 0.06
% 3.31/1.53  Abstraction          : 0.03
% 3.31/1.53  MUC search           : 0.00
% 3.31/1.53  Cooper               : 0.00
% 3.31/1.53  Total                : 0.79
% 3.31/1.53  Index Insertion      : 0.00
% 3.31/1.54  Index Deletion       : 0.00
% 3.31/1.54  Index Matching       : 0.00
% 3.45/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
