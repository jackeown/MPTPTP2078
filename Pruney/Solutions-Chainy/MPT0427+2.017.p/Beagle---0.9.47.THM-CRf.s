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
% DateTime   : Thu Dec  3 09:57:58 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 306 expanded)
%              Number of leaves         :   29 ( 111 expanded)
%              Depth                    :    9
%              Number of atoms          :  121 ( 638 expanded)
%              Number of equality atoms :   42 ( 240 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_176,plain,(
    ! [A_54,B_55] :
      ( k6_setfam_1(A_54,B_55) = k1_setfam_1(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(A_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_188,plain,(
    k6_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_176])).

tff(c_317,plain,(
    ! [A_73,B_74] :
      ( k8_setfam_1(A_73,B_74) = k6_setfam_1(A_73,B_74)
      | k1_xboole_0 = B_74
      | ~ m1_subset_1(B_74,k1_zfmisc_1(k1_zfmisc_1(A_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_328,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = k6_setfam_1('#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_317])).

tff(c_335,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_328])).

tff(c_338,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_335])).

tff(c_18,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_148,plain,(
    ! [B_47,A_48] :
      ( ~ r1_xboole_0(B_47,A_48)
      | ~ r1_tarski(B_47,A_48)
      | v1_xboole_0(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_151,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_148])).

tff(c_154,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_151])).

tff(c_90,plain,(
    ! [A_37,B_38] :
      ( r2_hidden('#skF_2'(A_37,B_38),A_37)
      | r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_94,plain,(
    ! [A_37,B_38] :
      ( ~ v1_xboole_0(A_37)
      | r1_tarski(A_37,B_38) ) ),
    inference(resolution,[status(thm)],[c_90,c_2])).

tff(c_34,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,k1_zfmisc_1(B_22))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_171,plain,(
    ! [A_53] :
      ( k8_setfam_1(A_53,k1_xboole_0) = A_53
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_198,plain,(
    ! [A_56] :
      ( k8_setfam_1(A_56,k1_xboole_0) = A_56
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_56)) ) ),
    inference(resolution,[status(thm)],[c_34,c_171])).

tff(c_201,plain,(
    ! [A_56] :
      ( k8_setfam_1(A_56,k1_xboole_0) = A_56
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_94,c_198])).

tff(c_204,plain,(
    ! [A_56] : k8_setfam_1(A_56,k1_xboole_0) = A_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_201])).

tff(c_342,plain,(
    ! [A_56] : k8_setfam_1(A_56,'#skF_4') = A_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_204])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_189,plain,(
    k6_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_176])).

tff(c_331,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k6_setfam_1('#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_317])).

tff(c_337,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_331])).

tff(c_393,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_337])).

tff(c_394,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_393])).

tff(c_38,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),k8_setfam_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_364,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_38])).

tff(c_395,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_394,c_364])).

tff(c_406,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_342,c_395])).

tff(c_407,plain,(
    k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_393])).

tff(c_409,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_364])).

tff(c_265,plain,(
    ! [A_66,B_67] :
      ( m1_subset_1(k8_setfam_1(A_66,B_67),k1_zfmisc_1(A_66))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1(A_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_32,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | ~ m1_subset_1(A_21,k1_zfmisc_1(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_424,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(k8_setfam_1(A_78,B_79),A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k1_zfmisc_1(A_78))) ) ),
    inference(resolution,[status(thm)],[c_265,c_32])).

tff(c_434,plain,(
    r1_tarski(k8_setfam_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_424])).

tff(c_440,plain,(
    r1_tarski(k1_setfam_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_434])).

tff(c_442,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_409,c_440])).

tff(c_444,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_335])).

tff(c_40,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_36,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k1_setfam_1(B_24),k1_setfam_1(A_23))
      | k1_xboole_0 = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_95,plain,(
    ! [A_39,B_40] :
      ( ~ v1_xboole_0(A_39)
      | r1_tarski(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_90,c_2])).

tff(c_73,plain,(
    ! [B_35,A_36] :
      ( B_35 = A_36
      | ~ r1_tarski(B_35,A_36)
      | ~ r1_tarski(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_88,plain,
    ( '#skF_5' = '#skF_4'
    | ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_73])).

tff(c_89,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_104,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_95,c_89])).

tff(c_475,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_337])).

tff(c_483,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_154])).

tff(c_487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_483])).

tff(c_488,plain,(
    k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_337])).

tff(c_443,plain,(
    k8_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_335])).

tff(c_445,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_38])).

tff(c_490,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_445])).

tff(c_503,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_490])).

tff(c_509,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_503])).

tff(c_511,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_444,c_509])).

tff(c_512,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_515,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_4'),k8_setfam_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_38])).

tff(c_521,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_515])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:54:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.43  
% 2.64/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.43  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.64/1.43  
% 2.64/1.43  %Foreground sorts:
% 2.64/1.43  
% 2.64/1.43  
% 2.64/1.43  %Background operators:
% 2.64/1.43  
% 2.64/1.43  
% 2.64/1.43  %Foreground operators:
% 2.64/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.64/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.64/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.64/1.43  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.64/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.64/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.64/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.64/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.64/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.64/1.43  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.64/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.64/1.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.64/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.64/1.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.64/1.43  
% 2.64/1.45  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.64/1.45  tff(f_103, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.64/1.45  tff(f_83, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.64/1.45  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.64/1.45  tff(f_56, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.64/1.45  tff(f_64, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.64/1.45  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.64/1.45  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.64/1.45  tff(f_87, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.64/1.45  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.64/1.45  tff(f_93, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.64/1.45  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.64/1.45  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.64/1.45  tff(c_176, plain, (![A_54, B_55]: (k6_setfam_1(A_54, B_55)=k1_setfam_1(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(k1_zfmisc_1(A_54))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.64/1.45  tff(c_188, plain, (k6_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_176])).
% 2.64/1.45  tff(c_317, plain, (![A_73, B_74]: (k8_setfam_1(A_73, B_74)=k6_setfam_1(A_73, B_74) | k1_xboole_0=B_74 | ~m1_subset_1(B_74, k1_zfmisc_1(k1_zfmisc_1(A_73))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.64/1.45  tff(c_328, plain, (k8_setfam_1('#skF_3', '#skF_4')=k6_setfam_1('#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_44, c_317])).
% 2.64/1.45  tff(c_335, plain, (k8_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_188, c_328])).
% 2.64/1.45  tff(c_338, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_335])).
% 2.64/1.45  tff(c_18, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.64/1.45  tff(c_148, plain, (![B_47, A_48]: (~r1_xboole_0(B_47, A_48) | ~r1_tarski(B_47, A_48) | v1_xboole_0(B_47))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.64/1.45  tff(c_151, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_148])).
% 2.64/1.45  tff(c_154, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_151])).
% 2.64/1.45  tff(c_90, plain, (![A_37, B_38]: (r2_hidden('#skF_2'(A_37, B_38), A_37) | r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.64/1.45  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.64/1.45  tff(c_94, plain, (![A_37, B_38]: (~v1_xboole_0(A_37) | r1_tarski(A_37, B_38))), inference(resolution, [status(thm)], [c_90, c_2])).
% 2.64/1.45  tff(c_34, plain, (![A_21, B_22]: (m1_subset_1(A_21, k1_zfmisc_1(B_22)) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.64/1.45  tff(c_171, plain, (![A_53]: (k8_setfam_1(A_53, k1_xboole_0)=A_53 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_53))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.64/1.45  tff(c_198, plain, (![A_56]: (k8_setfam_1(A_56, k1_xboole_0)=A_56 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_56)))), inference(resolution, [status(thm)], [c_34, c_171])).
% 2.64/1.45  tff(c_201, plain, (![A_56]: (k8_setfam_1(A_56, k1_xboole_0)=A_56 | ~v1_xboole_0(k1_xboole_0))), inference(resolution, [status(thm)], [c_94, c_198])).
% 2.64/1.45  tff(c_204, plain, (![A_56]: (k8_setfam_1(A_56, k1_xboole_0)=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_154, c_201])).
% 2.64/1.45  tff(c_342, plain, (![A_56]: (k8_setfam_1(A_56, '#skF_4')=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_338, c_204])).
% 2.64/1.45  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.64/1.45  tff(c_189, plain, (k6_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(resolution, [status(thm)], [c_42, c_176])).
% 2.64/1.45  tff(c_331, plain, (k8_setfam_1('#skF_3', '#skF_5')=k6_setfam_1('#skF_3', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_42, c_317])).
% 2.64/1.45  tff(c_337, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_189, c_331])).
% 2.64/1.45  tff(c_393, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_338, c_337])).
% 2.64/1.45  tff(c_394, plain, ('#skF_5'='#skF_4'), inference(splitLeft, [status(thm)], [c_393])).
% 2.64/1.45  tff(c_38, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), k8_setfam_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.64/1.45  tff(c_364, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_342, c_38])).
% 2.64/1.45  tff(c_395, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_394, c_364])).
% 2.64/1.45  tff(c_406, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_342, c_395])).
% 2.64/1.45  tff(c_407, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(splitRight, [status(thm)], [c_393])).
% 2.64/1.45  tff(c_409, plain, (~r1_tarski(k1_setfam_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_407, c_364])).
% 2.64/1.45  tff(c_265, plain, (![A_66, B_67]: (m1_subset_1(k8_setfam_1(A_66, B_67), k1_zfmisc_1(A_66)) | ~m1_subset_1(B_67, k1_zfmisc_1(k1_zfmisc_1(A_66))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.64/1.45  tff(c_32, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | ~m1_subset_1(A_21, k1_zfmisc_1(B_22)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.64/1.45  tff(c_424, plain, (![A_78, B_79]: (r1_tarski(k8_setfam_1(A_78, B_79), A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(k1_zfmisc_1(A_78))))), inference(resolution, [status(thm)], [c_265, c_32])).
% 2.64/1.45  tff(c_434, plain, (r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_42, c_424])).
% 2.64/1.45  tff(c_440, plain, (r1_tarski(k1_setfam_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_407, c_434])).
% 2.64/1.45  tff(c_442, plain, $false, inference(negUnitSimplification, [status(thm)], [c_409, c_440])).
% 2.64/1.45  tff(c_444, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_335])).
% 2.64/1.45  tff(c_40, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.64/1.45  tff(c_36, plain, (![B_24, A_23]: (r1_tarski(k1_setfam_1(B_24), k1_setfam_1(A_23)) | k1_xboole_0=A_23 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.64/1.45  tff(c_95, plain, (![A_39, B_40]: (~v1_xboole_0(A_39) | r1_tarski(A_39, B_40))), inference(resolution, [status(thm)], [c_90, c_2])).
% 2.64/1.45  tff(c_73, plain, (![B_35, A_36]: (B_35=A_36 | ~r1_tarski(B_35, A_36) | ~r1_tarski(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.64/1.45  tff(c_88, plain, ('#skF_5'='#skF_4' | ~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_73])).
% 2.64/1.45  tff(c_89, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_88])).
% 2.64/1.45  tff(c_104, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_95, c_89])).
% 2.64/1.45  tff(c_475, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_337])).
% 2.64/1.45  tff(c_483, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_475, c_154])).
% 2.64/1.45  tff(c_487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_483])).
% 2.64/1.45  tff(c_488, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(splitRight, [status(thm)], [c_337])).
% 2.64/1.45  tff(c_443, plain, (k8_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4')), inference(splitRight, [status(thm)], [c_335])).
% 2.64/1.45  tff(c_445, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), k1_setfam_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_443, c_38])).
% 2.64/1.45  tff(c_490, plain, (~r1_tarski(k1_setfam_1('#skF_5'), k1_setfam_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_488, c_445])).
% 2.64/1.45  tff(c_503, plain, (k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_36, c_490])).
% 2.64/1.45  tff(c_509, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_503])).
% 2.64/1.45  tff(c_511, plain, $false, inference(negUnitSimplification, [status(thm)], [c_444, c_509])).
% 2.64/1.45  tff(c_512, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_88])).
% 2.64/1.45  tff(c_515, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_4'), k8_setfam_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_512, c_38])).
% 2.64/1.45  tff(c_521, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_515])).
% 2.64/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.45  
% 2.64/1.45  Inference rules
% 2.64/1.45  ----------------------
% 2.64/1.45  #Ref     : 0
% 2.64/1.45  #Sup     : 96
% 2.64/1.45  #Fact    : 0
% 2.64/1.45  #Define  : 0
% 2.64/1.45  #Split   : 8
% 2.64/1.45  #Chain   : 0
% 2.64/1.45  #Close   : 0
% 2.64/1.45  
% 2.64/1.45  Ordering : KBO
% 2.64/1.45  
% 2.64/1.45  Simplification rules
% 2.64/1.45  ----------------------
% 2.64/1.45  #Subsume      : 12
% 2.64/1.45  #Demod        : 68
% 2.64/1.45  #Tautology    : 39
% 2.64/1.45  #SimpNegUnit  : 4
% 2.64/1.45  #BackRed      : 38
% 2.64/1.45  
% 2.64/1.45  #Partial instantiations: 0
% 2.64/1.45  #Strategies tried      : 1
% 2.64/1.45  
% 2.64/1.45  Timing (in seconds)
% 2.64/1.45  ----------------------
% 2.64/1.45  Preprocessing        : 0.34
% 2.64/1.45  Parsing              : 0.18
% 2.64/1.45  CNF conversion       : 0.02
% 2.64/1.45  Main loop            : 0.27
% 2.64/1.45  Inferencing          : 0.10
% 2.64/1.45  Reduction            : 0.08
% 2.64/1.45  Demodulation         : 0.06
% 2.64/1.45  BG Simplification    : 0.02
% 2.64/1.45  Subsumption          : 0.06
% 2.64/1.45  Abstraction          : 0.02
% 2.64/1.45  MUC search           : 0.00
% 2.64/1.45  Cooper               : 0.00
% 2.64/1.45  Total                : 0.65
% 2.64/1.45  Index Insertion      : 0.00
% 2.64/1.45  Index Deletion       : 0.00
% 2.64/1.45  Index Matching       : 0.00
% 2.64/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
