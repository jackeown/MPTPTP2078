%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:58 EST 2020

% Result     : Theorem 9.64s
% Output     : CNFRefutation 9.64s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 144 expanded)
%              Number of leaves         :   29 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :   90 ( 224 expanded)
%              Number of equality atoms :   24 (  60 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(k3_subset_1(A,B),C)
             => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_61,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_64,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_42,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_44,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_356,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k3_subset_1(A_59,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_397,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_356])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    ! [A_21,B_22] : k6_subset_1(A_21,B_22) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    ! [A_18,B_19] : m1_subset_1(k6_subset_1(A_18,B_19),k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_49,plain,(
    ! [A_18,B_19] : m1_subset_1(k4_xboole_0(A_18,B_19),k1_zfmisc_1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32])).

tff(c_34,plain,(
    ! [A_20] : ~ v1_xboole_0(k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_138,plain,(
    ! [B_47,A_48] :
      ( r2_hidden(B_47,A_48)
      | ~ m1_subset_1(B_47,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [C_13,A_9] :
      ( r1_tarski(C_13,A_9)
      | ~ r2_hidden(C_13,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_142,plain,(
    ! [B_47,A_9] :
      ( r1_tarski(B_47,A_9)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_9))
      | v1_xboole_0(k1_zfmisc_1(A_9)) ) ),
    inference(resolution,[status(thm)],[c_138,c_10])).

tff(c_218,plain,(
    ! [B_55,A_56] :
      ( r1_tarski(B_55,A_56)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_142])).

tff(c_442,plain,(
    ! [A_61,B_62] : r1_tarski(k4_xboole_0(A_61,B_62),A_61) ),
    inference(resolution,[status(thm)],[c_49,c_218])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1331,plain,(
    ! [A_93,B_94] : k3_xboole_0(k4_xboole_0(A_93,B_94),A_93) = k4_xboole_0(A_93,B_94) ),
    inference(resolution,[status(thm)],[c_442,c_6])).

tff(c_1948,plain,(
    ! [A_101,B_102] : k3_xboole_0(A_101,k4_xboole_0(A_101,B_102)) = k4_xboole_0(A_101,B_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1331])).

tff(c_2020,plain,(
    k3_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = k4_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_1948])).

tff(c_2045,plain,(
    k3_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = k3_subset_1('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_2020])).

tff(c_247,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_218])).

tff(c_252,plain,(
    k3_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_247,c_6])).

tff(c_279,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_252])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_419,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = k3_xboole_0('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_8])).

tff(c_425,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_419])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_248,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_218])).

tff(c_256,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_248,c_6])).

tff(c_398,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_356])).

tff(c_381,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_subset_1(A_18,k4_xboole_0(A_18,B_19)) ),
    inference(resolution,[status(thm)],[c_49,c_356])).

tff(c_396,plain,(
    ! [A_18,B_19] : k3_subset_1(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_381])).

tff(c_1270,plain,(
    ! [A_90,C_91,B_92] :
      ( r1_tarski(k3_subset_1(A_90,C_91),k3_subset_1(A_90,B_92))
      | ~ r1_tarski(B_92,C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(A_90))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1303,plain,(
    ! [A_18,B_19,B_92] :
      ( r1_tarski(k3_xboole_0(A_18,B_19),k3_subset_1(A_18,B_92))
      | ~ r1_tarski(B_92,k4_xboole_0(A_18,B_19))
      | ~ m1_subset_1(k4_xboole_0(A_18,B_19),k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_1270])).

tff(c_8613,plain,(
    ! [A_178,B_179,B_180] :
      ( r1_tarski(k3_xboole_0(A_178,B_179),k3_subset_1(A_178,B_180))
      | ~ r1_tarski(B_180,k4_xboole_0(A_178,B_179))
      | ~ m1_subset_1(B_180,k1_zfmisc_1(A_178)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_1303])).

tff(c_8733,plain,(
    ! [A_18,B_179,B_19] :
      ( r1_tarski(k3_xboole_0(A_18,B_179),k3_xboole_0(A_18,B_19))
      | ~ r1_tarski(k4_xboole_0(A_18,B_19),k4_xboole_0(A_18,B_179))
      | ~ m1_subset_1(k4_xboole_0(A_18,B_19),k1_zfmisc_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_8613])).

tff(c_15844,plain,(
    ! [A_244,B_245,B_246] :
      ( r1_tarski(k3_xboole_0(A_244,B_245),k3_xboole_0(A_244,B_246))
      | ~ r1_tarski(k4_xboole_0(A_244,B_246),k4_xboole_0(A_244,B_245)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_8733])).

tff(c_15908,plain,(
    ! [B_245] :
      ( r1_tarski(k3_xboole_0('#skF_3',B_245),k3_xboole_0('#skF_3','#skF_4'))
      | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k4_xboole_0('#skF_3',B_245)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_15844])).

tff(c_15962,plain,(
    ! [B_247] :
      ( r1_tarski(k3_xboole_0('#skF_3',B_247),'#skF_4')
      | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k4_xboole_0('#skF_3',B_247)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_2,c_15908])).

tff(c_15975,plain,
    ( r1_tarski(k3_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')),'#skF_4')
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_15962])).

tff(c_15992,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_2045,c_15975])).

tff(c_15994,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_15992])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n001.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 14:19:00 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.64/3.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.64/3.65  
% 9.64/3.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.64/3.66  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 9.64/3.66  
% 9.64/3.66  %Foreground sorts:
% 9.64/3.66  
% 9.64/3.66  
% 9.64/3.66  %Background operators:
% 9.64/3.66  
% 9.64/3.66  
% 9.64/3.66  %Foreground operators:
% 9.64/3.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.64/3.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.64/3.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.64/3.66  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.64/3.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.64/3.66  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.64/3.66  tff('#skF_5', type, '#skF_5': $i).
% 9.64/3.66  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 9.64/3.66  tff('#skF_3', type, '#skF_3': $i).
% 9.64/3.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.64/3.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.64/3.66  tff('#skF_4', type, '#skF_4': $i).
% 9.64/3.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.64/3.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.64/3.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.64/3.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.64/3.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.64/3.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.64/3.66  
% 9.64/3.67  tff(f_85, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_subset_1)).
% 9.64/3.67  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 9.64/3.67  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.64/3.67  tff(f_66, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 9.64/3.67  tff(f_61, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 9.64/3.67  tff(f_64, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 9.64/3.67  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 9.64/3.67  tff(f_42, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 9.64/3.67  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 9.64/3.67  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.64/3.67  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 9.64/3.67  tff(c_42, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.64/3.67  tff(c_44, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.64/3.67  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.64/3.67  tff(c_356, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k3_subset_1(A_59, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.64/3.67  tff(c_397, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_356])).
% 9.64/3.67  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.64/3.67  tff(c_36, plain, (![A_21, B_22]: (k6_subset_1(A_21, B_22)=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.64/3.67  tff(c_32, plain, (![A_18, B_19]: (m1_subset_1(k6_subset_1(A_18, B_19), k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.64/3.67  tff(c_49, plain, (![A_18, B_19]: (m1_subset_1(k4_xboole_0(A_18, B_19), k1_zfmisc_1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32])).
% 9.64/3.67  tff(c_34, plain, (![A_20]: (~v1_xboole_0(k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 9.64/3.67  tff(c_138, plain, (![B_47, A_48]: (r2_hidden(B_47, A_48) | ~m1_subset_1(B_47, A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.64/3.67  tff(c_10, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 9.64/3.67  tff(c_142, plain, (![B_47, A_9]: (r1_tarski(B_47, A_9) | ~m1_subset_1(B_47, k1_zfmisc_1(A_9)) | v1_xboole_0(k1_zfmisc_1(A_9)))), inference(resolution, [status(thm)], [c_138, c_10])).
% 9.64/3.67  tff(c_218, plain, (![B_55, A_56]: (r1_tarski(B_55, A_56) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)))), inference(negUnitSimplification, [status(thm)], [c_34, c_142])).
% 9.64/3.67  tff(c_442, plain, (![A_61, B_62]: (r1_tarski(k4_xboole_0(A_61, B_62), A_61))), inference(resolution, [status(thm)], [c_49, c_218])).
% 9.64/3.67  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.64/3.67  tff(c_1331, plain, (![A_93, B_94]: (k3_xboole_0(k4_xboole_0(A_93, B_94), A_93)=k4_xboole_0(A_93, B_94))), inference(resolution, [status(thm)], [c_442, c_6])).
% 9.64/3.67  tff(c_1948, plain, (![A_101, B_102]: (k3_xboole_0(A_101, k4_xboole_0(A_101, B_102))=k4_xboole_0(A_101, B_102))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1331])).
% 9.64/3.67  tff(c_2020, plain, (k3_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))=k4_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_397, c_1948])).
% 9.64/3.67  tff(c_2045, plain, (k3_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))=k3_subset_1('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_397, c_2020])).
% 9.64/3.67  tff(c_247, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_218])).
% 9.64/3.67  tff(c_252, plain, (k3_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_247, c_6])).
% 9.64/3.67  tff(c_279, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2, c_252])).
% 9.64/3.67  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.64/3.67  tff(c_419, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))=k3_xboole_0('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_397, c_8])).
% 9.64/3.67  tff(c_425, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_279, c_419])).
% 9.64/3.67  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 9.64/3.67  tff(c_248, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_218])).
% 9.64/3.67  tff(c_256, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_248, c_6])).
% 9.64/3.67  tff(c_398, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_356])).
% 9.64/3.67  tff(c_381, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_subset_1(A_18, k4_xboole_0(A_18, B_19)))), inference(resolution, [status(thm)], [c_49, c_356])).
% 9.64/3.67  tff(c_396, plain, (![A_18, B_19]: (k3_subset_1(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_381])).
% 9.64/3.67  tff(c_1270, plain, (![A_90, C_91, B_92]: (r1_tarski(k3_subset_1(A_90, C_91), k3_subset_1(A_90, B_92)) | ~r1_tarski(B_92, C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(A_90)) | ~m1_subset_1(B_92, k1_zfmisc_1(A_90)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 9.64/3.67  tff(c_1303, plain, (![A_18, B_19, B_92]: (r1_tarski(k3_xboole_0(A_18, B_19), k3_subset_1(A_18, B_92)) | ~r1_tarski(B_92, k4_xboole_0(A_18, B_19)) | ~m1_subset_1(k4_xboole_0(A_18, B_19), k1_zfmisc_1(A_18)) | ~m1_subset_1(B_92, k1_zfmisc_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_396, c_1270])).
% 9.64/3.67  tff(c_8613, plain, (![A_178, B_179, B_180]: (r1_tarski(k3_xboole_0(A_178, B_179), k3_subset_1(A_178, B_180)) | ~r1_tarski(B_180, k4_xboole_0(A_178, B_179)) | ~m1_subset_1(B_180, k1_zfmisc_1(A_178)))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_1303])).
% 9.64/3.67  tff(c_8733, plain, (![A_18, B_179, B_19]: (r1_tarski(k3_xboole_0(A_18, B_179), k3_xboole_0(A_18, B_19)) | ~r1_tarski(k4_xboole_0(A_18, B_19), k4_xboole_0(A_18, B_179)) | ~m1_subset_1(k4_xboole_0(A_18, B_19), k1_zfmisc_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_396, c_8613])).
% 9.64/3.67  tff(c_15844, plain, (![A_244, B_245, B_246]: (r1_tarski(k3_xboole_0(A_244, B_245), k3_xboole_0(A_244, B_246)) | ~r1_tarski(k4_xboole_0(A_244, B_246), k4_xboole_0(A_244, B_245)))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_8733])).
% 9.64/3.67  tff(c_15908, plain, (![B_245]: (r1_tarski(k3_xboole_0('#skF_3', B_245), k3_xboole_0('#skF_3', '#skF_4')) | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k4_xboole_0('#skF_3', B_245)))), inference(superposition, [status(thm), theory('equality')], [c_398, c_15844])).
% 9.64/3.67  tff(c_15962, plain, (![B_247]: (r1_tarski(k3_xboole_0('#skF_3', B_247), '#skF_4') | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k4_xboole_0('#skF_3', B_247)))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_2, c_15908])).
% 9.64/3.67  tff(c_15975, plain, (r1_tarski(k3_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5')), '#skF_4') | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_425, c_15962])).
% 9.64/3.67  tff(c_15992, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_2045, c_15975])).
% 9.64/3.67  tff(c_15994, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_15992])).
% 9.64/3.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.64/3.67  
% 9.64/3.67  Inference rules
% 9.64/3.67  ----------------------
% 9.64/3.67  #Ref     : 0
% 9.64/3.67  #Sup     : 3998
% 9.64/3.67  #Fact    : 0
% 9.64/3.67  #Define  : 0
% 9.64/3.67  #Split   : 1
% 9.64/3.67  #Chain   : 0
% 9.64/3.67  #Close   : 0
% 9.64/3.67  
% 9.64/3.67  Ordering : KBO
% 9.64/3.67  
% 9.64/3.67  Simplification rules
% 9.64/3.67  ----------------------
% 9.64/3.67  #Subsume      : 162
% 9.64/3.67  #Demod        : 5031
% 9.64/3.67  #Tautology    : 2568
% 9.64/3.67  #SimpNegUnit  : 16
% 9.64/3.67  #BackRed      : 5
% 9.64/3.67  
% 9.64/3.67  #Partial instantiations: 0
% 9.64/3.67  #Strategies tried      : 1
% 9.64/3.67  
% 9.64/3.67  Timing (in seconds)
% 9.64/3.67  ----------------------
% 9.64/3.68  Preprocessing        : 0.31
% 9.64/3.68  Parsing              : 0.15
% 9.64/3.68  CNF conversion       : 0.02
% 9.64/3.68  Main loop            : 2.62
% 9.64/3.68  Inferencing          : 0.54
% 9.64/3.68  Reduction            : 1.40
% 9.64/3.68  Demodulation         : 1.22
% 9.64/3.68  BG Simplification    : 0.06
% 9.64/3.68  Subsumption          : 0.49
% 9.64/3.68  Abstraction          : 0.10
% 9.64/3.68  MUC search           : 0.00
% 9.64/3.68  Cooper               : 0.00
% 9.64/3.68  Total                : 2.96
% 9.64/3.68  Index Insertion      : 0.00
% 9.64/3.68  Index Deletion       : 0.00
% 9.64/3.68  Index Matching       : 0.00
% 9.64/3.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
