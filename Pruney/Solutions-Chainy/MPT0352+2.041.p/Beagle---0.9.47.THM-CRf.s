%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:52 EST 2020

% Result     : Theorem 7.28s
% Output     : CNFRefutation 7.28s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 108 expanded)
%              Number of leaves         :   32 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :  106 ( 175 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_100,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_90,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_58,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_82,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_52,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_145,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_52])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_436,plain,(
    ! [A_103,B_104] :
      ( k4_xboole_0(A_103,B_104) = k3_subset_1(A_103,B_104)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_453,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_436])).

tff(c_16,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_77,plain,(
    ! [A_48,B_49] :
      ( k2_xboole_0(A_48,B_49) = B_49
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_81,plain,(
    ! [A_16,B_17] : k2_xboole_0(k4_xboole_0(A_16,B_17),A_16) = A_16 ),
    inference(resolution,[status(thm)],[c_16,c_77])).

tff(c_264,plain,(
    ! [A_90,B_91,C_92] :
      ( r1_tarski(A_90,k2_xboole_0(B_91,C_92))
      | ~ r1_tarski(k4_xboole_0(A_90,B_91),C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_273,plain,(
    ! [A_93,B_94] : r1_tarski(A_93,k2_xboole_0(B_94,A_93)) ),
    inference(resolution,[status(thm)],[c_16,c_264])).

tff(c_316,plain,(
    ! [A_95] : r1_tarski(A_95,A_95) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_273])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_xboole_0(A_5,C_7)
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_427,plain,(
    ! [B_99,C_100] : r1_xboole_0(k4_xboole_0(B_99,C_100),C_100) ),
    inference(resolution,[status(thm)],[c_316,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_430,plain,(
    ! [C_100,B_99] : r1_xboole_0(C_100,k4_xboole_0(B_99,C_100)) ),
    inference(resolution,[status(thm)],[c_427,c_2])).

tff(c_539,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_453,c_430])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_452,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_436])).

tff(c_20,plain,(
    ! [A_20,B_21,C_22] :
      ( r1_tarski(A_20,k2_xboole_0(B_21,C_22))
      | ~ r1_tarski(k4_xboole_0(A_20,B_21),C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4615,plain,(
    ! [C_250] :
      ( r1_tarski('#skF_3',k2_xboole_0('#skF_5',C_250))
      | ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),C_250) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_20])).

tff(c_4684,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_82,c_4615])).

tff(c_46,plain,(
    ! [A_35] : ~ v1_xboole_0(k1_zfmisc_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_101,plain,(
    ! [B_54,A_55] :
      ( r2_hidden(B_54,A_55)
      | ~ m1_subset_1(B_54,A_55)
      | v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_24,plain,(
    ! [C_30,A_26] :
      ( r1_tarski(C_30,A_26)
      | ~ r2_hidden(C_30,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_105,plain,(
    ! [B_54,A_26] :
      ( r1_tarski(B_54,A_26)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_26))
      | v1_xboole_0(k1_zfmisc_1(A_26)) ) ),
    inference(resolution,[status(thm)],[c_101,c_24])).

tff(c_109,plain,(
    ! [B_56,A_57] :
      ( r1_tarski(B_56,A_57)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_105])).

tff(c_122,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_109])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,B_12) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_139,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_122,c_12])).

tff(c_175,plain,(
    ! [A_68,C_69,B_70] :
      ( r1_tarski(A_68,C_69)
      | ~ r1_tarski(k2_xboole_0(A_68,B_70),C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_178,plain,(
    ! [C_69] :
      ( r1_tarski('#skF_4',C_69)
      | ~ r1_tarski('#skF_3',C_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_175])).

tff(c_4919,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_4684,c_178])).

tff(c_22,plain,(
    ! [A_23,B_24,C_25] :
      ( r1_tarski(A_23,B_24)
      | ~ r1_xboole_0(A_23,C_25)
      | ~ r1_tarski(A_23,k2_xboole_0(B_24,C_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4944,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4919,c_22])).

tff(c_4950,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_4944])).

tff(c_4952,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_4950])).

tff(c_4953,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_4960,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4953,c_52])).

tff(c_5605,plain,(
    ! [A_325,B_326] :
      ( k4_xboole_0(A_325,B_326) = k3_subset_1(A_325,B_326)
      | ~ m1_subset_1(B_326,k1_zfmisc_1(A_325)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_5622,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_5605])).

tff(c_5621,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_5605])).

tff(c_14,plain,(
    ! [C_15,B_14,A_13] :
      ( r1_tarski(k4_xboole_0(C_15,B_14),k4_xboole_0(C_15,A_13))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10974,plain,(
    ! [A_491] :
      ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),k4_xboole_0('#skF_3',A_491))
      | ~ r1_tarski(A_491,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5621,c_14])).

tff(c_10993,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5622,c_10974])).

tff(c_11005,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4953,c_10993])).

tff(c_11007,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4960,c_11005])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n003.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 20:11:12 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.28/2.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.28/2.62  
% 7.28/2.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.28/2.62  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 7.28/2.62  
% 7.28/2.62  %Foreground sorts:
% 7.28/2.62  
% 7.28/2.62  
% 7.28/2.62  %Background operators:
% 7.28/2.62  
% 7.28/2.62  
% 7.28/2.62  %Foreground operators:
% 7.28/2.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.28/2.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.28/2.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.28/2.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.28/2.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.28/2.62  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.28/2.62  tff('#skF_5', type, '#skF_5': $i).
% 7.28/2.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.28/2.62  tff('#skF_3', type, '#skF_3': $i).
% 7.28/2.62  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.28/2.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.28/2.62  tff('#skF_4', type, '#skF_4': $i).
% 7.28/2.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.28/2.62  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.28/2.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.28/2.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.28/2.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.28/2.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.28/2.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.28/2.62  
% 7.28/2.63  tff(f_100, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 7.28/2.63  tff(f_87, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 7.28/2.63  tff(f_51, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 7.28/2.63  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.28/2.63  tff(f_57, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 7.28/2.63  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 7.28/2.63  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 7.28/2.63  tff(f_90, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 7.28/2.63  tff(f_83, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 7.28/2.63  tff(f_70, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 7.28/2.63  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 7.28/2.63  tff(f_63, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 7.28/2.63  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 7.28/2.63  tff(c_58, plain, (r1_tarski('#skF_4', '#skF_5') | r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.28/2.63  tff(c_82, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_58])).
% 7.28/2.63  tff(c_52, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.28/2.63  tff(c_145, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_52])).
% 7.28/2.63  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.28/2.63  tff(c_436, plain, (![A_103, B_104]: (k4_xboole_0(A_103, B_104)=k3_subset_1(A_103, B_104) | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.28/2.63  tff(c_453, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_436])).
% 7.28/2.63  tff(c_16, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.28/2.63  tff(c_77, plain, (![A_48, B_49]: (k2_xboole_0(A_48, B_49)=B_49 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.28/2.63  tff(c_81, plain, (![A_16, B_17]: (k2_xboole_0(k4_xboole_0(A_16, B_17), A_16)=A_16)), inference(resolution, [status(thm)], [c_16, c_77])).
% 7.28/2.63  tff(c_264, plain, (![A_90, B_91, C_92]: (r1_tarski(A_90, k2_xboole_0(B_91, C_92)) | ~r1_tarski(k4_xboole_0(A_90, B_91), C_92))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.28/2.63  tff(c_273, plain, (![A_93, B_94]: (r1_tarski(A_93, k2_xboole_0(B_94, A_93)))), inference(resolution, [status(thm)], [c_16, c_264])).
% 7.28/2.63  tff(c_316, plain, (![A_95]: (r1_tarski(A_95, A_95))), inference(superposition, [status(thm), theory('equality')], [c_81, c_273])).
% 7.28/2.63  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_xboole_0(A_5, C_7) | ~r1_tarski(A_5, k4_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.28/2.63  tff(c_427, plain, (![B_99, C_100]: (r1_xboole_0(k4_xboole_0(B_99, C_100), C_100))), inference(resolution, [status(thm)], [c_316, c_6])).
% 7.28/2.63  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.28/2.63  tff(c_430, plain, (![C_100, B_99]: (r1_xboole_0(C_100, k4_xboole_0(B_99, C_100)))), inference(resolution, [status(thm)], [c_427, c_2])).
% 7.28/2.63  tff(c_539, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_453, c_430])).
% 7.28/2.63  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.28/2.63  tff(c_452, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_436])).
% 7.28/2.63  tff(c_20, plain, (![A_20, B_21, C_22]: (r1_tarski(A_20, k2_xboole_0(B_21, C_22)) | ~r1_tarski(k4_xboole_0(A_20, B_21), C_22))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.28/2.63  tff(c_4615, plain, (![C_250]: (r1_tarski('#skF_3', k2_xboole_0('#skF_5', C_250)) | ~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), C_250))), inference(superposition, [status(thm), theory('equality')], [c_452, c_20])).
% 7.28/2.63  tff(c_4684, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_82, c_4615])).
% 7.28/2.63  tff(c_46, plain, (![A_35]: (~v1_xboole_0(k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.28/2.63  tff(c_101, plain, (![B_54, A_55]: (r2_hidden(B_54, A_55) | ~m1_subset_1(B_54, A_55) | v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.28/2.63  tff(c_24, plain, (![C_30, A_26]: (r1_tarski(C_30, A_26) | ~r2_hidden(C_30, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.28/2.63  tff(c_105, plain, (![B_54, A_26]: (r1_tarski(B_54, A_26) | ~m1_subset_1(B_54, k1_zfmisc_1(A_26)) | v1_xboole_0(k1_zfmisc_1(A_26)))), inference(resolution, [status(thm)], [c_101, c_24])).
% 7.28/2.63  tff(c_109, plain, (![B_56, A_57]: (r1_tarski(B_56, A_57) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)))), inference(negUnitSimplification, [status(thm)], [c_46, c_105])).
% 7.28/2.63  tff(c_122, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_109])).
% 7.28/2.63  tff(c_12, plain, (![A_11, B_12]: (k2_xboole_0(A_11, B_12)=B_12 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.28/2.63  tff(c_139, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_122, c_12])).
% 7.28/2.63  tff(c_175, plain, (![A_68, C_69, B_70]: (r1_tarski(A_68, C_69) | ~r1_tarski(k2_xboole_0(A_68, B_70), C_69))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.28/2.63  tff(c_178, plain, (![C_69]: (r1_tarski('#skF_4', C_69) | ~r1_tarski('#skF_3', C_69))), inference(superposition, [status(thm), theory('equality')], [c_139, c_175])).
% 7.28/2.63  tff(c_4919, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_4684, c_178])).
% 7.28/2.63  tff(c_22, plain, (![A_23, B_24, C_25]: (r1_tarski(A_23, B_24) | ~r1_xboole_0(A_23, C_25) | ~r1_tarski(A_23, k2_xboole_0(B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.28/2.63  tff(c_4944, plain, (r1_tarski('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_4919, c_22])).
% 7.28/2.63  tff(c_4950, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_539, c_4944])).
% 7.28/2.63  tff(c_4952, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_4950])).
% 7.28/2.63  tff(c_4953, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_58])).
% 7.28/2.63  tff(c_4960, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4953, c_52])).
% 7.28/2.63  tff(c_5605, plain, (![A_325, B_326]: (k4_xboole_0(A_325, B_326)=k3_subset_1(A_325, B_326) | ~m1_subset_1(B_326, k1_zfmisc_1(A_325)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.28/2.63  tff(c_5622, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_5605])).
% 7.28/2.63  tff(c_5621, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_5605])).
% 7.28/2.63  tff(c_14, plain, (![C_15, B_14, A_13]: (r1_tarski(k4_xboole_0(C_15, B_14), k4_xboole_0(C_15, A_13)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.28/2.63  tff(c_10974, plain, (![A_491]: (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k4_xboole_0('#skF_3', A_491)) | ~r1_tarski(A_491, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5621, c_14])).
% 7.28/2.63  tff(c_10993, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5622, c_10974])).
% 7.28/2.63  tff(c_11005, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4953, c_10993])).
% 7.28/2.63  tff(c_11007, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4960, c_11005])).
% 7.28/2.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.28/2.63  
% 7.28/2.63  Inference rules
% 7.28/2.63  ----------------------
% 7.28/2.63  #Ref     : 0
% 7.28/2.63  #Sup     : 2635
% 7.28/2.63  #Fact    : 0
% 7.28/2.63  #Define  : 0
% 7.28/2.63  #Split   : 6
% 7.28/2.63  #Chain   : 0
% 7.28/2.63  #Close   : 0
% 7.28/2.63  
% 7.28/2.63  Ordering : KBO
% 7.28/2.63  
% 7.28/2.63  Simplification rules
% 7.28/2.63  ----------------------
% 7.28/2.63  #Subsume      : 48
% 7.28/2.63  #Demod        : 1549
% 7.28/2.63  #Tautology    : 1576
% 7.28/2.63  #SimpNegUnit  : 12
% 7.28/2.63  #BackRed      : 0
% 7.28/2.63  
% 7.28/2.63  #Partial instantiations: 0
% 7.28/2.63  #Strategies tried      : 1
% 7.28/2.63  
% 7.28/2.63  Timing (in seconds)
% 7.28/2.63  ----------------------
% 7.28/2.64  Preprocessing        : 0.34
% 7.28/2.64  Parsing              : 0.19
% 7.28/2.64  CNF conversion       : 0.02
% 7.28/2.64  Main loop            : 1.51
% 7.28/2.64  Inferencing          : 0.46
% 7.28/2.64  Reduction            : 0.61
% 7.28/2.64  Demodulation         : 0.46
% 7.28/2.64  BG Simplification    : 0.05
% 7.28/2.64  Subsumption          : 0.28
% 7.28/2.64  Abstraction          : 0.06
% 7.28/2.64  MUC search           : 0.00
% 7.28/2.64  Cooper               : 0.00
% 7.28/2.64  Total                : 1.87
% 7.28/2.64  Index Insertion      : 0.00
% 7.28/2.64  Index Deletion       : 0.00
% 7.28/2.64  Index Matching       : 0.00
% 7.28/2.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
