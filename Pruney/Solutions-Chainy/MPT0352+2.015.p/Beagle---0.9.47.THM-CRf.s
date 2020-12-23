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
% DateTime   : Thu Dec  3 09:55:48 EST 2020

% Result     : Theorem 10.47s
% Output     : CNFRefutation 10.55s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 117 expanded)
%              Number of leaves         :   29 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :  105 ( 193 expanded)
%              Number of equality atoms :   18 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_74,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_54,axiom,(
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
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(c_52,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_132,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_46,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_209,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_46])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_912,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(A_87,B_88) = k3_subset_1(A_87,B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_928,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_912])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] :
      ( r1_tarski(A_14,k2_xboole_0(B_15,C_16))
      | ~ r1_tarski(k4_xboole_0(A_14,B_15),C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1178,plain,(
    ! [C_99] :
      ( r1_tarski('#skF_3',k2_xboole_0('#skF_5',C_99))
      | ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),C_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_928,c_14])).

tff(c_1208,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_132,c_1178])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_40,plain,(
    ! [A_28] : ~ v1_xboole_0(k1_zfmisc_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_151,plain,(
    ! [B_47,A_48] :
      ( r2_hidden(B_47,A_48)
      | ~ m1_subset_1(B_47,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [C_23,A_19] :
      ( r1_tarski(C_23,A_19)
      | ~ r2_hidden(C_23,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_155,plain,(
    ! [B_47,A_19] :
      ( r1_tarski(B_47,A_19)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19)) ) ),
    inference(resolution,[status(thm)],[c_151,c_18])).

tff(c_159,plain,(
    ! [B_49,A_50] :
      ( r1_tarski(B_49,A_50)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_155])).

tff(c_172,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_159])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_191,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_172,c_8])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_929,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_912])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_503,plain,(
    ! [A_67,B_68,C_69] :
      ( r1_tarski(k4_xboole_0(A_67,B_68),C_69)
      | ~ r1_tarski(A_67,k2_xboole_0(B_68,C_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2853,plain,(
    ! [A_132,B_133,C_134] :
      ( r1_tarski(k3_xboole_0(A_132,B_133),C_134)
      | ~ r1_tarski(A_132,k2_xboole_0(k4_xboole_0(A_132,B_133),C_134)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_503])).

tff(c_7762,plain,(
    ! [A_244,B_245,A_246] :
      ( r1_tarski(k3_xboole_0(A_244,B_245),A_246)
      | ~ r1_tarski(A_244,k2_xboole_0(A_246,k4_xboole_0(A_244,B_245))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_2853])).

tff(c_7852,plain,(
    ! [A_246] :
      ( r1_tarski(k3_xboole_0('#skF_3','#skF_4'),A_246)
      | ~ r1_tarski('#skF_3',k2_xboole_0(A_246,k3_subset_1('#skF_3','#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_929,c_7762])).

tff(c_7961,plain,(
    ! [A_249] :
      ( r1_tarski('#skF_4',A_249)
      | ~ r1_tarski('#skF_3',k2_xboole_0(A_249,k3_subset_1('#skF_3','#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_4,c_7852])).

tff(c_7988,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_1208,c_7961])).

tff(c_8015,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_7988])).

tff(c_8016,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_8144,plain,(
    ! [B_266,A_267] :
      ( r2_hidden(B_266,A_267)
      | ~ m1_subset_1(B_266,A_267)
      | v1_xboole_0(A_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8151,plain,(
    ! [B_266,A_19] :
      ( r1_tarski(B_266,A_19)
      | ~ m1_subset_1(B_266,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19)) ) ),
    inference(resolution,[status(thm)],[c_8144,c_18])).

tff(c_8185,plain,(
    ! [B_271,A_272] :
      ( r1_tarski(B_271,A_272)
      | ~ m1_subset_1(B_271,k1_zfmisc_1(A_272)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_8151])).

tff(c_8202,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_8185])).

tff(c_8210,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8202,c_8])).

tff(c_8340,plain,(
    ! [A_280,B_281] :
      ( k4_xboole_0(A_280,B_281) = k3_subset_1(A_280,B_281)
      | ~ m1_subset_1(B_281,k1_zfmisc_1(A_280)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8357,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_8340])).

tff(c_8241,plain,(
    ! [A_273,B_274,C_275] :
      ( r1_tarski(A_273,k2_xboole_0(B_274,C_275))
      | ~ r1_tarski(k4_xboole_0(A_273,B_274),C_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10128,plain,(
    ! [A_338,B_339,C_340] :
      ( r1_tarski(A_338,k2_xboole_0(k4_xboole_0(A_338,B_339),C_340))
      | ~ r1_tarski(k3_xboole_0(A_338,B_339),C_340) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_8241])).

tff(c_14252,plain,(
    ! [A_440,B_441,B_442] :
      ( r1_tarski(A_440,k2_xboole_0(B_441,k4_xboole_0(A_440,B_442)))
      | ~ r1_tarski(k3_xboole_0(A_440,B_442),B_441) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10128])).

tff(c_14311,plain,(
    ! [B_441] :
      ( r1_tarski('#skF_3',k2_xboole_0(B_441,k3_subset_1('#skF_3','#skF_4')))
      | ~ r1_tarski(k3_xboole_0('#skF_3','#skF_4'),B_441) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8357,c_14252])).

tff(c_20042,plain,(
    ! [B_578] :
      ( r1_tarski('#skF_3',k2_xboole_0(B_578,k3_subset_1('#skF_3','#skF_4')))
      | ~ r1_tarski('#skF_4',B_578) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8210,c_4,c_14311])).

tff(c_8356,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_8340])).

tff(c_12,plain,(
    ! [A_11,B_12,C_13] :
      ( r1_tarski(k4_xboole_0(A_11,B_12),C_13)
      | ~ r1_tarski(A_11,k2_xboole_0(B_12,C_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_9307,plain,(
    ! [C_319] :
      ( r1_tarski(k3_subset_1('#skF_3','#skF_5'),C_319)
      | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_5',C_319)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8356,c_12])).

tff(c_8017,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_9318,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4'))) ),
    inference(resolution,[status(thm)],[c_9307,c_8017])).

tff(c_20069,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_20042,c_9318])).

tff(c_20093,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8016,c_20069])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:41:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.47/3.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.49/3.70  
% 10.49/3.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.49/3.71  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 10.49/3.71  
% 10.49/3.71  %Foreground sorts:
% 10.49/3.71  
% 10.49/3.71  
% 10.49/3.71  %Background operators:
% 10.49/3.71  
% 10.49/3.71  
% 10.49/3.71  %Foreground operators:
% 10.49/3.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.49/3.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.49/3.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.49/3.71  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.49/3.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.49/3.71  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.49/3.71  tff('#skF_5', type, '#skF_5': $i).
% 10.49/3.71  tff('#skF_3', type, '#skF_3': $i).
% 10.49/3.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.49/3.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.49/3.71  tff('#skF_4', type, '#skF_4': $i).
% 10.49/3.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.49/3.71  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 10.49/3.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.49/3.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.49/3.71  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 10.49/3.71  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 10.49/3.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.49/3.71  
% 10.55/3.72  tff(f_84, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 10.55/3.72  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 10.55/3.72  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 10.55/3.72  tff(f_74, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 10.55/3.72  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 10.55/3.72  tff(f_54, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 10.55/3.72  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.55/3.72  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.55/3.72  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 10.55/3.72  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.55/3.72  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 10.55/3.72  tff(c_52, plain, (r1_tarski('#skF_4', '#skF_5') | r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.55/3.72  tff(c_132, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_52])).
% 10.55/3.72  tff(c_46, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.55/3.72  tff(c_209, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_46])).
% 10.55/3.72  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.55/3.72  tff(c_912, plain, (![A_87, B_88]: (k4_xboole_0(A_87, B_88)=k3_subset_1(A_87, B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.55/3.72  tff(c_928, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_912])).
% 10.55/3.72  tff(c_14, plain, (![A_14, B_15, C_16]: (r1_tarski(A_14, k2_xboole_0(B_15, C_16)) | ~r1_tarski(k4_xboole_0(A_14, B_15), C_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.55/3.72  tff(c_1178, plain, (![C_99]: (r1_tarski('#skF_3', k2_xboole_0('#skF_5', C_99)) | ~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), C_99))), inference(superposition, [status(thm), theory('equality')], [c_928, c_14])).
% 10.55/3.72  tff(c_1208, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_132, c_1178])).
% 10.55/3.72  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 10.55/3.72  tff(c_40, plain, (![A_28]: (~v1_xboole_0(k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.55/3.72  tff(c_151, plain, (![B_47, A_48]: (r2_hidden(B_47, A_48) | ~m1_subset_1(B_47, A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.55/3.72  tff(c_18, plain, (![C_23, A_19]: (r1_tarski(C_23, A_19) | ~r2_hidden(C_23, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 10.55/3.72  tff(c_155, plain, (![B_47, A_19]: (r1_tarski(B_47, A_19) | ~m1_subset_1(B_47, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)))), inference(resolution, [status(thm)], [c_151, c_18])).
% 10.55/3.72  tff(c_159, plain, (![B_49, A_50]: (r1_tarski(B_49, A_50) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)))), inference(negUnitSimplification, [status(thm)], [c_40, c_155])).
% 10.55/3.72  tff(c_172, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_159])).
% 10.55/3.72  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.55/3.72  tff(c_191, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_172, c_8])).
% 10.55/3.72  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.55/3.72  tff(c_929, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_912])).
% 10.55/3.72  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.55/3.72  tff(c_16, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.55/3.72  tff(c_503, plain, (![A_67, B_68, C_69]: (r1_tarski(k4_xboole_0(A_67, B_68), C_69) | ~r1_tarski(A_67, k2_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.55/3.72  tff(c_2853, plain, (![A_132, B_133, C_134]: (r1_tarski(k3_xboole_0(A_132, B_133), C_134) | ~r1_tarski(A_132, k2_xboole_0(k4_xboole_0(A_132, B_133), C_134)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_503])).
% 10.55/3.72  tff(c_7762, plain, (![A_244, B_245, A_246]: (r1_tarski(k3_xboole_0(A_244, B_245), A_246) | ~r1_tarski(A_244, k2_xboole_0(A_246, k4_xboole_0(A_244, B_245))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_2853])).
% 10.55/3.72  tff(c_7852, plain, (![A_246]: (r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), A_246) | ~r1_tarski('#skF_3', k2_xboole_0(A_246, k3_subset_1('#skF_3', '#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_929, c_7762])).
% 10.55/3.72  tff(c_7961, plain, (![A_249]: (r1_tarski('#skF_4', A_249) | ~r1_tarski('#skF_3', k2_xboole_0(A_249, k3_subset_1('#skF_3', '#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_4, c_7852])).
% 10.55/3.72  tff(c_7988, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_1208, c_7961])).
% 10.55/3.72  tff(c_8015, plain, $false, inference(negUnitSimplification, [status(thm)], [c_209, c_7988])).
% 10.55/3.72  tff(c_8016, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_52])).
% 10.55/3.72  tff(c_8144, plain, (![B_266, A_267]: (r2_hidden(B_266, A_267) | ~m1_subset_1(B_266, A_267) | v1_xboole_0(A_267))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.55/3.72  tff(c_8151, plain, (![B_266, A_19]: (r1_tarski(B_266, A_19) | ~m1_subset_1(B_266, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)))), inference(resolution, [status(thm)], [c_8144, c_18])).
% 10.55/3.72  tff(c_8185, plain, (![B_271, A_272]: (r1_tarski(B_271, A_272) | ~m1_subset_1(B_271, k1_zfmisc_1(A_272)))), inference(negUnitSimplification, [status(thm)], [c_40, c_8151])).
% 10.55/3.72  tff(c_8202, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_8185])).
% 10.55/3.72  tff(c_8210, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_8202, c_8])).
% 10.55/3.72  tff(c_8340, plain, (![A_280, B_281]: (k4_xboole_0(A_280, B_281)=k3_subset_1(A_280, B_281) | ~m1_subset_1(B_281, k1_zfmisc_1(A_280)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.55/3.72  tff(c_8357, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_8340])).
% 10.55/3.72  tff(c_8241, plain, (![A_273, B_274, C_275]: (r1_tarski(A_273, k2_xboole_0(B_274, C_275)) | ~r1_tarski(k4_xboole_0(A_273, B_274), C_275))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.55/3.72  tff(c_10128, plain, (![A_338, B_339, C_340]: (r1_tarski(A_338, k2_xboole_0(k4_xboole_0(A_338, B_339), C_340)) | ~r1_tarski(k3_xboole_0(A_338, B_339), C_340))), inference(superposition, [status(thm), theory('equality')], [c_16, c_8241])).
% 10.55/3.72  tff(c_14252, plain, (![A_440, B_441, B_442]: (r1_tarski(A_440, k2_xboole_0(B_441, k4_xboole_0(A_440, B_442))) | ~r1_tarski(k3_xboole_0(A_440, B_442), B_441))), inference(superposition, [status(thm), theory('equality')], [c_2, c_10128])).
% 10.55/3.72  tff(c_14311, plain, (![B_441]: (r1_tarski('#skF_3', k2_xboole_0(B_441, k3_subset_1('#skF_3', '#skF_4'))) | ~r1_tarski(k3_xboole_0('#skF_3', '#skF_4'), B_441))), inference(superposition, [status(thm), theory('equality')], [c_8357, c_14252])).
% 10.55/3.72  tff(c_20042, plain, (![B_578]: (r1_tarski('#skF_3', k2_xboole_0(B_578, k3_subset_1('#skF_3', '#skF_4'))) | ~r1_tarski('#skF_4', B_578))), inference(demodulation, [status(thm), theory('equality')], [c_8210, c_4, c_14311])).
% 10.55/3.72  tff(c_8356, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_42, c_8340])).
% 10.55/3.72  tff(c_12, plain, (![A_11, B_12, C_13]: (r1_tarski(k4_xboole_0(A_11, B_12), C_13) | ~r1_tarski(A_11, k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.55/3.72  tff(c_9307, plain, (![C_319]: (r1_tarski(k3_subset_1('#skF_3', '#skF_5'), C_319) | ~r1_tarski('#skF_3', k2_xboole_0('#skF_5', C_319)))), inference(superposition, [status(thm), theory('equality')], [c_8356, c_12])).
% 10.55/3.72  tff(c_8017, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), k3_subset_1('#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_52])).
% 10.55/3.72  tff(c_9318, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_9307, c_8017])).
% 10.55/3.72  tff(c_20069, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_20042, c_9318])).
% 10.55/3.72  tff(c_20093, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8016, c_20069])).
% 10.55/3.72  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.55/3.72  
% 10.55/3.72  Inference rules
% 10.55/3.72  ----------------------
% 10.55/3.72  #Ref     : 0
% 10.55/3.72  #Sup     : 4801
% 10.55/3.72  #Fact    : 0
% 10.55/3.72  #Define  : 0
% 10.55/3.72  #Split   : 1
% 10.55/3.72  #Chain   : 0
% 10.55/3.72  #Close   : 0
% 10.55/3.72  
% 10.55/3.72  Ordering : KBO
% 10.55/3.72  
% 10.55/3.72  Simplification rules
% 10.55/3.72  ----------------------
% 10.55/3.72  #Subsume      : 189
% 10.55/3.72  #Demod        : 3941
% 10.55/3.72  #Tautology    : 2856
% 10.55/3.72  #SimpNegUnit  : 18
% 10.55/3.72  #BackRed      : 37
% 10.55/3.72  
% 10.55/3.72  #Partial instantiations: 0
% 10.55/3.72  #Strategies tried      : 1
% 10.55/3.72  
% 10.55/3.72  Timing (in seconds)
% 10.55/3.72  ----------------------
% 10.55/3.73  Preprocessing        : 0.32
% 10.55/3.73  Parsing              : 0.17
% 10.55/3.73  CNF conversion       : 0.02
% 10.55/3.73  Main loop            : 2.63
% 10.55/3.73  Inferencing          : 0.63
% 10.55/3.73  Reduction            : 1.31
% 10.55/3.73  Demodulation         : 1.10
% 10.55/3.73  BG Simplification    : 0.07
% 10.55/3.73  Subsumption          : 0.45
% 10.55/3.73  Abstraction          : 0.10
% 10.55/3.73  MUC search           : 0.00
% 10.55/3.73  Cooper               : 0.00
% 10.55/3.73  Total                : 2.99
% 10.55/3.73  Index Insertion      : 0.00
% 10.55/3.73  Index Deletion       : 0.00
% 10.55/3.73  Index Matching       : 0.00
% 10.55/3.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
