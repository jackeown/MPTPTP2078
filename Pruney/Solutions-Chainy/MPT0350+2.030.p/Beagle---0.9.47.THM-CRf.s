%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:29 EST 2020

% Result     : Theorem 9.58s
% Output     : CNFRefutation 9.58s
% Verified   : 
% Statistics : Number of formulae       :   72 (  82 expanded)
%              Number of leaves         :   35 (  41 expanded)
%              Depth                    :   11
%              Number of atoms          :   79 (  93 expanded)
%              Number of equality atoms :   40 (  47 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_78,axiom,(
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

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_40,plain,(
    ! [A_26] : k2_subset_1(A_26) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_52,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_55,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_52])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_46,plain,(
    ! [A_31] : ~ v1_xboole_0(k1_zfmisc_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_412,plain,(
    ! [B_74,A_75] :
      ( r2_hidden(B_74,A_75)
      | ~ m1_subset_1(B_74,A_75)
      | v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_20,plain,(
    ! [C_23,A_19] :
      ( r1_tarski(C_23,A_19)
      | ~ r2_hidden(C_23,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_419,plain,(
    ! [B_74,A_19] :
      ( r1_tarski(B_74,A_19)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19)) ) ),
    inference(resolution,[status(thm)],[c_412,c_20])).

tff(c_870,plain,(
    ! [B_92,A_93] :
      ( r1_tarski(B_92,A_93)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_93)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_419])).

tff(c_883,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_870])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_887,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_883,c_6])).

tff(c_776,plain,(
    ! [A_88,B_89] :
      ( k4_xboole_0(A_88,B_89) = k3_subset_1(A_88,B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_789,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_776])).

tff(c_18,plain,(
    ! [A_17,B_18] : k5_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_82,plain,(
    ! [A_42,B_43] : k2_xboole_0(A_42,k3_xboole_0(A_42,B_43)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_88,plain,(
    ! [A_42] : k4_xboole_0(A_42,A_42) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_14])).

tff(c_522,plain,(
    ! [A_78,B_79] : k4_xboole_0(A_78,k4_xboole_0(A_78,B_79)) = k3_xboole_0(A_78,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_557,plain,(
    ! [A_42] : k4_xboole_0(A_42,k1_xboole_0) = k3_xboole_0(A_42,A_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_522])).

tff(c_602,plain,(
    ! [A_81] : k3_xboole_0(A_81,A_81) = A_81 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_557])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_622,plain,(
    ! [A_81] : k2_xboole_0(A_81,A_81) = A_81 ),
    inference(superposition,[status(thm),theory(equality)],[c_602,c_8])).

tff(c_1094,plain,(
    ! [A_104,B_105,C_106] : k4_xboole_0(k4_xboole_0(A_104,B_105),C_106) = k4_xboole_0(A_104,k2_xboole_0(B_105,C_106)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8359,plain,(
    ! [C_212,A_213,B_214] : k5_xboole_0(C_212,k4_xboole_0(A_213,k2_xboole_0(B_214,C_212))) = k2_xboole_0(C_212,k4_xboole_0(A_213,B_214)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1094,c_18])).

tff(c_8486,plain,(
    ! [A_81,A_213] : k5_xboole_0(A_81,k4_xboole_0(A_213,A_81)) = k2_xboole_0(A_81,k4_xboole_0(A_213,A_81)) ),
    inference(superposition,[status(thm),theory(equality)],[c_622,c_8359])).

tff(c_13727,plain,(
    ! [A_251,A_252] : k2_xboole_0(A_251,k4_xboole_0(A_252,A_251)) = k2_xboole_0(A_251,A_252) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_8486])).

tff(c_14033,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_789,c_13727])).

tff(c_14138,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_887,c_14033])).

tff(c_44,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k3_subset_1(A_29,B_30),k1_zfmisc_1(A_29))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3339,plain,(
    ! [A_154,B_155,C_156] :
      ( k4_subset_1(A_154,B_155,C_156) = k2_xboole_0(B_155,C_156)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(A_154))
      | ~ m1_subset_1(B_155,k1_zfmisc_1(A_154)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_26961,plain,(
    ! [A_340,B_341,B_342] :
      ( k4_subset_1(A_340,B_341,k3_subset_1(A_340,B_342)) = k2_xboole_0(B_341,k3_subset_1(A_340,B_342))
      | ~ m1_subset_1(B_341,k1_zfmisc_1(A_340))
      | ~ m1_subset_1(B_342,k1_zfmisc_1(A_340)) ) ),
    inference(resolution,[status(thm)],[c_44,c_3339])).

tff(c_27309,plain,(
    ! [B_345] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_345)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_345))
      | ~ m1_subset_1(B_345,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_54,c_26961])).

tff(c_27328,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_54,c_27309])).

tff(c_27336,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14138,c_27328])).

tff(c_27338,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55,c_27336])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:02:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.58/4.00  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.58/4.01  
% 9.58/4.01  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.58/4.01  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 9.58/4.01  
% 9.58/4.01  %Foreground sorts:
% 9.58/4.01  
% 9.58/4.01  
% 9.58/4.01  %Background operators:
% 9.58/4.01  
% 9.58/4.01  
% 9.58/4.01  %Foreground operators:
% 9.58/4.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.58/4.01  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.58/4.01  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.58/4.01  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.58/4.01  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.58/4.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.58/4.01  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.58/4.01  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 9.58/4.01  tff('#skF_3', type, '#skF_3': $i).
% 9.58/4.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.58/4.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.58/4.01  tff('#skF_4', type, '#skF_4': $i).
% 9.58/4.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.58/4.01  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.58/4.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.58/4.01  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.58/4.01  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.58/4.01  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 9.58/4.01  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.58/4.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.58/4.01  
% 9.58/4.03  tff(f_67, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 9.58/4.03  tff(f_93, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 9.58/4.03  tff(f_78, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 9.58/4.03  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 9.58/4.03  tff(f_52, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 9.58/4.03  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 9.58/4.03  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 9.58/4.03  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 9.58/4.03  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 9.58/4.03  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 9.58/4.03  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 9.58/4.03  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.58/4.03  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 9.58/4.03  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 9.58/4.03  tff(f_88, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 9.58/4.03  tff(c_40, plain, (![A_26]: (k2_subset_1(A_26)=A_26)), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.58/4.03  tff(c_52, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.58/4.03  tff(c_55, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_52])).
% 9.58/4.03  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.58/4.03  tff(c_46, plain, (![A_31]: (~v1_xboole_0(k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.58/4.03  tff(c_412, plain, (![B_74, A_75]: (r2_hidden(B_74, A_75) | ~m1_subset_1(B_74, A_75) | v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.58/4.03  tff(c_20, plain, (![C_23, A_19]: (r1_tarski(C_23, A_19) | ~r2_hidden(C_23, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.58/4.03  tff(c_419, plain, (![B_74, A_19]: (r1_tarski(B_74, A_19) | ~m1_subset_1(B_74, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)))), inference(resolution, [status(thm)], [c_412, c_20])).
% 9.58/4.03  tff(c_870, plain, (![B_92, A_93]: (r1_tarski(B_92, A_93) | ~m1_subset_1(B_92, k1_zfmisc_1(A_93)))), inference(negUnitSimplification, [status(thm)], [c_46, c_419])).
% 9.58/4.03  tff(c_883, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_870])).
% 9.58/4.03  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.58/4.03  tff(c_887, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_883, c_6])).
% 9.58/4.03  tff(c_776, plain, (![A_88, B_89]: (k4_xboole_0(A_88, B_89)=k3_subset_1(A_88, B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.58/4.03  tff(c_789, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_776])).
% 9.58/4.03  tff(c_18, plain, (![A_17, B_18]: (k5_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.58/4.03  tff(c_10, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.58/4.03  tff(c_82, plain, (![A_42, B_43]: (k2_xboole_0(A_42, k3_xboole_0(A_42, B_43))=A_42)), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.58/4.03  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k2_xboole_0(A_13, B_14))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.58/4.03  tff(c_88, plain, (![A_42]: (k4_xboole_0(A_42, A_42)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_82, c_14])).
% 9.58/4.03  tff(c_522, plain, (![A_78, B_79]: (k4_xboole_0(A_78, k4_xboole_0(A_78, B_79))=k3_xboole_0(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.58/4.03  tff(c_557, plain, (![A_42]: (k4_xboole_0(A_42, k1_xboole_0)=k3_xboole_0(A_42, A_42))), inference(superposition, [status(thm), theory('equality')], [c_88, c_522])).
% 9.58/4.03  tff(c_602, plain, (![A_81]: (k3_xboole_0(A_81, A_81)=A_81)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_557])).
% 9.58/4.03  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k3_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.58/4.03  tff(c_622, plain, (![A_81]: (k2_xboole_0(A_81, A_81)=A_81)), inference(superposition, [status(thm), theory('equality')], [c_602, c_8])).
% 9.58/4.03  tff(c_1094, plain, (![A_104, B_105, C_106]: (k4_xboole_0(k4_xboole_0(A_104, B_105), C_106)=k4_xboole_0(A_104, k2_xboole_0(B_105, C_106)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.58/4.03  tff(c_8359, plain, (![C_212, A_213, B_214]: (k5_xboole_0(C_212, k4_xboole_0(A_213, k2_xboole_0(B_214, C_212)))=k2_xboole_0(C_212, k4_xboole_0(A_213, B_214)))), inference(superposition, [status(thm), theory('equality')], [c_1094, c_18])).
% 9.58/4.03  tff(c_8486, plain, (![A_81, A_213]: (k5_xboole_0(A_81, k4_xboole_0(A_213, A_81))=k2_xboole_0(A_81, k4_xboole_0(A_213, A_81)))), inference(superposition, [status(thm), theory('equality')], [c_622, c_8359])).
% 9.58/4.03  tff(c_13727, plain, (![A_251, A_252]: (k2_xboole_0(A_251, k4_xboole_0(A_252, A_251))=k2_xboole_0(A_251, A_252))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_8486])).
% 9.58/4.03  tff(c_14033, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_789, c_13727])).
% 9.58/4.03  tff(c_14138, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_887, c_14033])).
% 9.58/4.03  tff(c_44, plain, (![A_29, B_30]: (m1_subset_1(k3_subset_1(A_29, B_30), k1_zfmisc_1(A_29)) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.58/4.03  tff(c_3339, plain, (![A_154, B_155, C_156]: (k4_subset_1(A_154, B_155, C_156)=k2_xboole_0(B_155, C_156) | ~m1_subset_1(C_156, k1_zfmisc_1(A_154)) | ~m1_subset_1(B_155, k1_zfmisc_1(A_154)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.58/4.03  tff(c_26961, plain, (![A_340, B_341, B_342]: (k4_subset_1(A_340, B_341, k3_subset_1(A_340, B_342))=k2_xboole_0(B_341, k3_subset_1(A_340, B_342)) | ~m1_subset_1(B_341, k1_zfmisc_1(A_340)) | ~m1_subset_1(B_342, k1_zfmisc_1(A_340)))), inference(resolution, [status(thm)], [c_44, c_3339])).
% 9.58/4.03  tff(c_27309, plain, (![B_345]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_345))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_345)) | ~m1_subset_1(B_345, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_54, c_26961])).
% 9.58/4.03  tff(c_27328, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_54, c_27309])).
% 9.58/4.03  tff(c_27336, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_14138, c_27328])).
% 9.58/4.03  tff(c_27338, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55, c_27336])).
% 9.58/4.03  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.58/4.03  
% 9.58/4.03  Inference rules
% 9.58/4.03  ----------------------
% 9.58/4.03  #Ref     : 0
% 9.58/4.03  #Sup     : 6760
% 9.58/4.03  #Fact    : 0
% 9.58/4.03  #Define  : 0
% 9.58/4.03  #Split   : 0
% 9.58/4.03  #Chain   : 0
% 9.58/4.03  #Close   : 0
% 9.58/4.03  
% 9.58/4.03  Ordering : KBO
% 9.58/4.03  
% 9.58/4.03  Simplification rules
% 9.58/4.03  ----------------------
% 9.58/4.03  #Subsume      : 24
% 9.58/4.03  #Demod        : 7734
% 9.58/4.03  #Tautology    : 5268
% 9.58/4.03  #SimpNegUnit  : 14
% 9.58/4.03  #BackRed      : 16
% 9.58/4.03  
% 9.58/4.03  #Partial instantiations: 0
% 9.58/4.03  #Strategies tried      : 1
% 9.58/4.03  
% 9.58/4.03  Timing (in seconds)
% 9.58/4.03  ----------------------
% 9.85/4.03  Preprocessing        : 0.31
% 9.85/4.03  Parsing              : 0.16
% 9.85/4.03  CNF conversion       : 0.02
% 9.85/4.03  Main loop            : 2.95
% 9.85/4.03  Inferencing          : 0.62
% 9.85/4.03  Reduction            : 1.68
% 9.85/4.03  Demodulation         : 1.49
% 9.85/4.03  BG Simplification    : 0.06
% 9.85/4.03  Subsumption          : 0.46
% 9.85/4.03  Abstraction          : 0.11
% 9.85/4.03  MUC search           : 0.00
% 9.85/4.03  Cooper               : 0.00
% 9.85/4.03  Total                : 3.30
% 9.85/4.03  Index Insertion      : 0.00
% 9.85/4.03  Index Deletion       : 0.00
% 9.85/4.03  Index Matching       : 0.00
% 9.85/4.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
