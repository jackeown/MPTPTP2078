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
% DateTime   : Thu Dec  3 09:55:59 EST 2020

% Result     : Theorem 5.46s
% Output     : CNFRefutation 5.46s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 169 expanded)
%              Number of leaves         :   30 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  112 ( 252 expanded)
%              Number of equality atoms :   36 (  84 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(k3_subset_1(A,B),C)
             => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_65,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_60,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_63,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_41,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_36,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_38,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_333,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = k3_subset_1(A_61,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_371,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_333])).

tff(c_30,plain,(
    ! [A_18,B_19] : k6_subset_1(A_18,B_19) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    ! [A_15,B_16] : m1_subset_1(k6_subset_1(A_15,B_16),k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_43,plain,(
    ! [A_15,B_16] : m1_subset_1(k4_xboole_0(A_15,B_16),k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_26])).

tff(c_551,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_43])).

tff(c_28,plain,(
    ! [A_17] : ~ v1_xboole_0(k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( r2_hidden(B_12,A_11)
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    ! [A_10] : k3_tarski(k1_zfmisc_1(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_5] : k4_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_143,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,k3_tarski(B_40))
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_817,plain,(
    ! [A_83,B_84] :
      ( k4_xboole_0(A_83,k3_tarski(B_84)) = k1_xboole_0
      | ~ r2_hidden(A_83,B_84) ) ),
    inference(resolution,[status(thm)],[c_143,c_6])).

tff(c_10,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k3_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_834,plain,(
    ! [A_83,B_84] :
      ( k3_xboole_0(A_83,k3_tarski(B_84)) = k4_xboole_0(A_83,k1_xboole_0)
      | ~ r2_hidden(A_83,B_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_817,c_10])).

tff(c_1550,plain,(
    ! [A_96,B_97] :
      ( k3_xboole_0(A_96,k3_tarski(B_97)) = A_96
      | ~ r2_hidden(A_96,B_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_834])).

tff(c_1688,plain,(
    ! [B_102,B_103] :
      ( k3_xboole_0(k3_tarski(B_102),B_103) = B_103
      | ~ r2_hidden(B_103,B_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1550])).

tff(c_1842,plain,(
    ! [A_108,B_109] :
      ( k3_xboole_0(A_108,B_109) = B_109
      | ~ r2_hidden(B_109,k1_zfmisc_1(A_108)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1688])).

tff(c_1846,plain,(
    ! [A_108,B_12] :
      ( k3_xboole_0(A_108,B_12) = B_12
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_108))
      | v1_xboole_0(k1_zfmisc_1(A_108)) ) ),
    inference(resolution,[status(thm)],[c_18,c_1842])).

tff(c_2386,plain,(
    ! [A_121,B_122] :
      ( k3_xboole_0(A_121,B_122) = B_122
      | ~ m1_subset_1(B_122,k1_zfmisc_1(A_121)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1846])).

tff(c_2425,plain,(
    k3_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_551,c_2386])).

tff(c_235,plain,(
    ! [B_54,A_55] :
      ( r2_hidden(B_54,A_55)
      | ~ m1_subset_1(B_54,A_55)
      | v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_149,plain,(
    ! [A_39,A_10] :
      ( r1_tarski(A_39,A_10)
      | ~ r2_hidden(A_39,k1_zfmisc_1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_143])).

tff(c_239,plain,(
    ! [B_54,A_10] :
      ( r1_tarski(B_54,A_10)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_10))
      | v1_xboole_0(k1_zfmisc_1(A_10)) ) ),
    inference(resolution,[status(thm)],[c_235,c_149])).

tff(c_281,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(B_58,A_59)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_239])).

tff(c_318,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_281])).

tff(c_328,plain,(
    k4_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_318,c_6])).

tff(c_451,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_10])).

tff(c_457,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_451])).

tff(c_548,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_10])).

tff(c_554,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_548])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_372,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_333])).

tff(c_444,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_43])).

tff(c_319,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_281])).

tff(c_332,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_319,c_6])).

tff(c_401,plain,(
    k4_xboole_0('#skF_2',k1_xboole_0) = k3_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_10])).

tff(c_407,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_401])).

tff(c_355,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_subset_1(A_15,k4_xboole_0(A_15,B_16)) ),
    inference(resolution,[status(thm)],[c_43,c_333])).

tff(c_1077,plain,(
    ! [A_90,B_91] : k3_subset_1(A_90,k4_xboole_0(A_90,B_91)) = k3_xboole_0(A_90,B_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_355])).

tff(c_1116,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_1077])).

tff(c_1148,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_1116])).

tff(c_34,plain,(
    ! [A_20,C_23,B_21] :
      ( r1_tarski(k3_subset_1(A_20,C_23),k3_subset_1(A_20,B_21))
      | ~ r1_tarski(B_21,C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(A_20))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1083,plain,(
    ! [A_90,B_91,B_21] :
      ( r1_tarski(k3_xboole_0(A_90,B_91),k3_subset_1(A_90,B_21))
      | ~ r1_tarski(B_21,k4_xboole_0(A_90,B_91))
      | ~ m1_subset_1(k4_xboole_0(A_90,B_91),k1_zfmisc_1(A_90))
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_90)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1077,c_34])).

tff(c_5431,plain,(
    ! [A_157,B_158,B_159] :
      ( r1_tarski(k3_xboole_0(A_157,B_158),k3_subset_1(A_157,B_159))
      | ~ r1_tarski(B_159,k4_xboole_0(A_157,B_158))
      | ~ m1_subset_1(B_159,k1_zfmisc_1(A_157)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_1083])).

tff(c_5491,plain,(
    ! [B_158] :
      ( r1_tarski(k3_xboole_0('#skF_1',B_158),'#skF_2')
      | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),k4_xboole_0('#skF_1',B_158))
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1148,c_5431])).

tff(c_6585,plain,(
    ! [B_173] :
      ( r1_tarski(k3_xboole_0('#skF_1',B_173),'#skF_2')
      | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),k4_xboole_0('#skF_1',B_173)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_5491])).

tff(c_6599,plain,
    ( r1_tarski(k3_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')),'#skF_2')
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_6585])).

tff(c_6629,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2425,c_6599])).

tff(c_6631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_6629])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:23:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.46/2.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.46/2.17  
% 5.46/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.46/2.17  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.46/2.17  
% 5.46/2.17  %Foreground sorts:
% 5.46/2.17  
% 5.46/2.17  
% 5.46/2.17  %Background operators:
% 5.46/2.17  
% 5.46/2.17  
% 5.46/2.17  %Foreground operators:
% 5.46/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.46/2.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.46/2.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.46/2.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.46/2.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.46/2.17  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.46/2.17  tff('#skF_2', type, '#skF_2': $i).
% 5.46/2.17  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 5.46/2.17  tff('#skF_3', type, '#skF_3': $i).
% 5.46/2.17  tff('#skF_1', type, '#skF_1': $i).
% 5.46/2.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.46/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.46/2.17  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.46/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.46/2.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.46/2.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.46/2.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.46/2.17  
% 5.46/2.20  tff(f_84, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_subset_1)).
% 5.46/2.20  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.46/2.20  tff(f_65, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 5.46/2.20  tff(f_60, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 5.46/2.20  tff(f_63, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 5.46/2.20  tff(f_54, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 5.46/2.20  tff(f_41, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 5.46/2.20  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.46/2.20  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 5.46/2.20  tff(f_39, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 5.46/2.20  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.46/2.20  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.46/2.20  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 5.46/2.20  tff(c_36, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.46/2.20  tff(c_38, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.46/2.20  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.46/2.20  tff(c_333, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=k3_subset_1(A_61, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.46/2.20  tff(c_371, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_333])).
% 5.46/2.20  tff(c_30, plain, (![A_18, B_19]: (k6_subset_1(A_18, B_19)=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.46/2.20  tff(c_26, plain, (![A_15, B_16]: (m1_subset_1(k6_subset_1(A_15, B_16), k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.46/2.20  tff(c_43, plain, (![A_15, B_16]: (m1_subset_1(k4_xboole_0(A_15, B_16), k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_26])).
% 5.46/2.20  tff(c_551, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_371, c_43])).
% 5.46/2.20  tff(c_28, plain, (![A_17]: (~v1_xboole_0(k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.46/2.20  tff(c_18, plain, (![B_12, A_11]: (r2_hidden(B_12, A_11) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.46/2.20  tff(c_14, plain, (![A_10]: (k3_tarski(k1_zfmisc_1(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.46/2.20  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.46/2.20  tff(c_8, plain, (![A_5]: (k4_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.46/2.20  tff(c_143, plain, (![A_39, B_40]: (r1_tarski(A_39, k3_tarski(B_40)) | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.46/2.20  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.46/2.20  tff(c_817, plain, (![A_83, B_84]: (k4_xboole_0(A_83, k3_tarski(B_84))=k1_xboole_0 | ~r2_hidden(A_83, B_84))), inference(resolution, [status(thm)], [c_143, c_6])).
% 5.46/2.20  tff(c_10, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.46/2.20  tff(c_834, plain, (![A_83, B_84]: (k3_xboole_0(A_83, k3_tarski(B_84))=k4_xboole_0(A_83, k1_xboole_0) | ~r2_hidden(A_83, B_84))), inference(superposition, [status(thm), theory('equality')], [c_817, c_10])).
% 5.46/2.20  tff(c_1550, plain, (![A_96, B_97]: (k3_xboole_0(A_96, k3_tarski(B_97))=A_96 | ~r2_hidden(A_96, B_97))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_834])).
% 5.46/2.20  tff(c_1688, plain, (![B_102, B_103]: (k3_xboole_0(k3_tarski(B_102), B_103)=B_103 | ~r2_hidden(B_103, B_102))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1550])).
% 5.46/2.20  tff(c_1842, plain, (![A_108, B_109]: (k3_xboole_0(A_108, B_109)=B_109 | ~r2_hidden(B_109, k1_zfmisc_1(A_108)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1688])).
% 5.46/2.20  tff(c_1846, plain, (![A_108, B_12]: (k3_xboole_0(A_108, B_12)=B_12 | ~m1_subset_1(B_12, k1_zfmisc_1(A_108)) | v1_xboole_0(k1_zfmisc_1(A_108)))), inference(resolution, [status(thm)], [c_18, c_1842])).
% 5.46/2.20  tff(c_2386, plain, (![A_121, B_122]: (k3_xboole_0(A_121, B_122)=B_122 | ~m1_subset_1(B_122, k1_zfmisc_1(A_121)))), inference(negUnitSimplification, [status(thm)], [c_28, c_1846])).
% 5.46/2.20  tff(c_2425, plain, (k3_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_551, c_2386])).
% 5.46/2.20  tff(c_235, plain, (![B_54, A_55]: (r2_hidden(B_54, A_55) | ~m1_subset_1(B_54, A_55) | v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.46/2.20  tff(c_149, plain, (![A_39, A_10]: (r1_tarski(A_39, A_10) | ~r2_hidden(A_39, k1_zfmisc_1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_143])).
% 5.46/2.20  tff(c_239, plain, (![B_54, A_10]: (r1_tarski(B_54, A_10) | ~m1_subset_1(B_54, k1_zfmisc_1(A_10)) | v1_xboole_0(k1_zfmisc_1(A_10)))), inference(resolution, [status(thm)], [c_235, c_149])).
% 5.46/2.20  tff(c_281, plain, (![B_58, A_59]: (r1_tarski(B_58, A_59) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)))), inference(negUnitSimplification, [status(thm)], [c_28, c_239])).
% 5.46/2.20  tff(c_318, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_281])).
% 5.46/2.20  tff(c_328, plain, (k4_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_318, c_6])).
% 5.46/2.20  tff(c_451, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_328, c_10])).
% 5.46/2.20  tff(c_457, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_451])).
% 5.46/2.20  tff(c_548, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_371, c_10])).
% 5.46/2.20  tff(c_554, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_457, c_548])).
% 5.46/2.20  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.46/2.20  tff(c_372, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_333])).
% 5.46/2.20  tff(c_444, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_372, c_43])).
% 5.46/2.20  tff(c_319, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_281])).
% 5.46/2.20  tff(c_332, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_319, c_6])).
% 5.46/2.20  tff(c_401, plain, (k4_xboole_0('#skF_2', k1_xboole_0)=k3_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_332, c_10])).
% 5.46/2.20  tff(c_407, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_401])).
% 5.46/2.20  tff(c_355, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_subset_1(A_15, k4_xboole_0(A_15, B_16)))), inference(resolution, [status(thm)], [c_43, c_333])).
% 5.46/2.20  tff(c_1077, plain, (![A_90, B_91]: (k3_subset_1(A_90, k4_xboole_0(A_90, B_91))=k3_xboole_0(A_90, B_91))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_355])).
% 5.46/2.20  tff(c_1116, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_372, c_1077])).
% 5.46/2.20  tff(c_1148, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_407, c_1116])).
% 5.46/2.20  tff(c_34, plain, (![A_20, C_23, B_21]: (r1_tarski(k3_subset_1(A_20, C_23), k3_subset_1(A_20, B_21)) | ~r1_tarski(B_21, C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(A_20)) | ~m1_subset_1(B_21, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.46/2.20  tff(c_1083, plain, (![A_90, B_91, B_21]: (r1_tarski(k3_xboole_0(A_90, B_91), k3_subset_1(A_90, B_21)) | ~r1_tarski(B_21, k4_xboole_0(A_90, B_91)) | ~m1_subset_1(k4_xboole_0(A_90, B_91), k1_zfmisc_1(A_90)) | ~m1_subset_1(B_21, k1_zfmisc_1(A_90)))), inference(superposition, [status(thm), theory('equality')], [c_1077, c_34])).
% 5.46/2.20  tff(c_5431, plain, (![A_157, B_158, B_159]: (r1_tarski(k3_xboole_0(A_157, B_158), k3_subset_1(A_157, B_159)) | ~r1_tarski(B_159, k4_xboole_0(A_157, B_158)) | ~m1_subset_1(B_159, k1_zfmisc_1(A_157)))), inference(demodulation, [status(thm), theory('equality')], [c_43, c_1083])).
% 5.46/2.20  tff(c_5491, plain, (![B_158]: (r1_tarski(k3_xboole_0('#skF_1', B_158), '#skF_2') | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', B_158)) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1148, c_5431])).
% 5.46/2.20  tff(c_6585, plain, (![B_173]: (r1_tarski(k3_xboole_0('#skF_1', B_173), '#skF_2') | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', B_173)))), inference(demodulation, [status(thm), theory('equality')], [c_444, c_5491])).
% 5.46/2.20  tff(c_6599, plain, (r1_tarski(k3_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3')), '#skF_2') | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_554, c_6585])).
% 5.46/2.20  tff(c_6629, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2425, c_6599])).
% 5.46/2.20  tff(c_6631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_6629])).
% 5.46/2.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.46/2.20  
% 5.46/2.20  Inference rules
% 5.46/2.20  ----------------------
% 5.46/2.20  #Ref     : 0
% 5.46/2.20  #Sup     : 1592
% 5.46/2.20  #Fact    : 0
% 5.46/2.20  #Define  : 0
% 5.46/2.20  #Split   : 0
% 5.46/2.20  #Chain   : 0
% 5.46/2.20  #Close   : 0
% 5.46/2.20  
% 5.46/2.20  Ordering : KBO
% 5.46/2.20  
% 5.46/2.20  Simplification rules
% 5.46/2.20  ----------------------
% 5.46/2.20  #Subsume      : 107
% 5.46/2.20  #Demod        : 1927
% 5.46/2.20  #Tautology    : 1136
% 5.46/2.20  #SimpNegUnit  : 6
% 5.46/2.20  #BackRed      : 2
% 5.46/2.20  
% 5.46/2.20  #Partial instantiations: 0
% 5.46/2.20  #Strategies tried      : 1
% 5.46/2.20  
% 5.46/2.20  Timing (in seconds)
% 5.46/2.20  ----------------------
% 5.46/2.20  Preprocessing        : 0.30
% 5.46/2.20  Parsing              : 0.16
% 5.46/2.20  CNF conversion       : 0.02
% 5.46/2.20  Main loop            : 1.12
% 5.46/2.20  Inferencing          : 0.30
% 5.46/2.20  Reduction            : 0.56
% 5.46/2.20  Demodulation         : 0.47
% 5.46/2.20  BG Simplification    : 0.03
% 5.46/2.20  Subsumption          : 0.17
% 5.46/2.20  Abstraction          : 0.05
% 5.46/2.20  MUC search           : 0.00
% 5.46/2.20  Cooper               : 0.00
% 5.46/2.20  Total                : 1.47
% 5.46/2.20  Index Insertion      : 0.00
% 5.46/2.20  Index Deletion       : 0.00
% 5.46/2.20  Index Matching       : 0.00
% 5.46/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
