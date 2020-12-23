%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:57 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 351 expanded)
%              Number of leaves         :   34 ( 130 expanded)
%              Depth                    :   11
%              Number of atoms          :  126 ( 704 expanded)
%              Number of equality atoms :   46 ( 185 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_98,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_39,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_77,plain,(
    ! [A_44,B_45] :
      ( k2_xboole_0(k1_tarski(A_44),B_45) = B_45
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),B_14) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_102,plain,(
    ! [B_48,A_49] :
      ( k1_xboole_0 != B_48
      | ~ r2_hidden(A_49,B_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_14])).

tff(c_109,plain,(
    ! [A_1] :
      ( k1_xboole_0 != A_1
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_102])).

tff(c_36,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_30,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(A_26,k1_zfmisc_1(B_27))
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_88,plain,(
    ! [B_46,A_47] :
      ( v1_xboole_0(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_xboole_0(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_123,plain,(
    ! [A_51,B_52] :
      ( v1_xboole_0(A_51)
      | ~ v1_xboole_0(B_52)
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_30,c_88])).

tff(c_135,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_123])).

tff(c_136,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_149,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_109,c_136])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_165,plain,(
    ! [A_59,B_60] :
      ( k6_setfam_1(A_59,B_60) = k1_setfam_1(B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k1_zfmisc_1(A_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_178,plain,(
    k6_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_165])).

tff(c_261,plain,(
    ! [A_71,B_72] :
      ( k8_setfam_1(A_71,B_72) = k6_setfam_1(A_71,B_72)
      | k1_xboole_0 = B_72
      | ~ m1_subset_1(B_72,k1_zfmisc_1(k1_zfmisc_1(A_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_275,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k6_setfam_1('#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_38,c_261])).

tff(c_281,plain,
    ( k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_275])).

tff(c_282,plain,(
    k8_setfam_1('#skF_3','#skF_5') = k1_setfam_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_281])).

tff(c_209,plain,(
    ! [A_65,B_66] :
      ( m1_subset_1(k8_setfam_1(A_65,B_66),k1_zfmisc_1(A_65))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k1_zfmisc_1(A_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_223,plain,(
    ! [A_67,B_68] :
      ( r1_tarski(k8_setfam_1(A_67,B_68),A_67)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(k1_zfmisc_1(A_67))) ) ),
    inference(resolution,[status(thm)],[c_209,c_28])).

tff(c_237,plain,(
    r1_tarski(k8_setfam_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_223])).

tff(c_283,plain,(
    r1_tarski(k1_setfam_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_237])).

tff(c_55,plain,(
    ! [A_40,B_41] :
      ( r1_tarski(A_40,B_41)
      | ~ m1_subset_1(A_40,k1_zfmisc_1(B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_66,plain,(
    r1_tarski('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_55])).

tff(c_177,plain,(
    k6_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_165])).

tff(c_272,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = k6_setfam_1('#skF_3','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_261])).

tff(c_279,plain,
    ( k8_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_272])).

tff(c_313,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_279])).

tff(c_159,plain,(
    ! [A_57] :
      ( k8_setfam_1(A_57,k1_xboole_0) = A_57
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_163,plain,(
    ! [A_57] :
      ( k8_setfam_1(A_57,k1_xboole_0) = A_57
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_57)) ) ),
    inference(resolution,[status(thm)],[c_30,c_159])).

tff(c_367,plain,(
    ! [A_80] :
      ( k8_setfam_1(A_80,'#skF_4') = A_80
      | ~ r1_tarski('#skF_4',k1_zfmisc_1(A_80)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_313,c_163])).

tff(c_371,plain,(
    k8_setfam_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_66,c_367])).

tff(c_34,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_5'),k8_setfam_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_284,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),k8_setfam_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_34])).

tff(c_372,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_284])).

tff(c_376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_372])).

tff(c_378,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_32,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k1_setfam_1(B_29),k1_setfam_1(A_28))
      | k1_xboole_0 = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_377,plain,(
    k8_setfam_1('#skF_3','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_279])).

tff(c_379,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_5'),k1_setfam_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_377,c_284])).

tff(c_402,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_379])).

tff(c_405,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_402])).

tff(c_407,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_378,c_405])).

tff(c_408,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_43,plain,(
    ! [A_35] :
      ( r2_hidden('#skF_2'(A_35),A_35)
      | k1_xboole_0 = A_35 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_47,plain,(
    ! [A_35] :
      ( ~ v1_xboole_0(A_35)
      | k1_xboole_0 = A_35 ) ),
    inference(resolution,[status(thm)],[c_43,c_2])).

tff(c_413,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_408,c_47])).

tff(c_18,plain,(
    ! [A_18] :
      ( k8_setfam_1(A_18,k1_xboole_0) = A_18
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_496,plain,(
    ! [A_92] :
      ( k8_setfam_1(A_92,'#skF_4') = A_92
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1(A_92))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_413,c_18])).

tff(c_504,plain,(
    k8_setfam_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_40,c_496])).

tff(c_409,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_417,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_409,c_47])).

tff(c_428,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_417])).

tff(c_431,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_3','#skF_4'),k8_setfam_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_428,c_34])).

tff(c_515,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_504,c_431])).

tff(c_548,plain,(
    ! [A_100,B_101] :
      ( m1_subset_1(k8_setfam_1(A_100,B_101),k1_zfmisc_1(A_100))
      | ~ m1_subset_1(B_101,k1_zfmisc_1(k1_zfmisc_1(A_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_561,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_504,c_548])).

tff(c_566,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_561])).

tff(c_572,plain,(
    r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_566,c_28])).

tff(c_577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_515,c_572])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 12:37:56 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.37  
% 2.64/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.38  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 2.64/1.38  
% 2.64/1.38  %Foreground sorts:
% 2.64/1.38  
% 2.64/1.38  
% 2.64/1.38  %Background operators:
% 2.64/1.38  
% 2.64/1.38  
% 2.64/1.38  %Foreground operators:
% 2.64/1.38  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.64/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.64/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.64/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.64/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.64/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.64/1.38  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.64/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.64/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.64/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.64/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.64/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.64/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.64/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.64/1.38  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.64/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.64/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.64/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.64/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.64/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.64/1.38  
% 2.64/1.39  tff(f_98, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.64/1.39  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.64/1.39  tff(f_47, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 2.64/1.39  tff(f_50, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.64/1.39  tff(f_82, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.64/1.39  tff(f_57, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.64/1.39  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.64/1.39  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.64/1.39  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.64/1.39  tff(f_88, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.64/1.39  tff(f_39, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.64/1.39  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.64/1.39  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.64/1.39  tff(c_77, plain, (![A_44, B_45]: (k2_xboole_0(k1_tarski(A_44), B_45)=B_45 | ~r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.64/1.39  tff(c_14, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.64/1.39  tff(c_102, plain, (![B_48, A_49]: (k1_xboole_0!=B_48 | ~r2_hidden(A_49, B_48))), inference(superposition, [status(thm), theory('equality')], [c_77, c_14])).
% 2.64/1.39  tff(c_109, plain, (![A_1]: (k1_xboole_0!=A_1 | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_102])).
% 2.64/1.39  tff(c_36, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.64/1.39  tff(c_30, plain, (![A_26, B_27]: (m1_subset_1(A_26, k1_zfmisc_1(B_27)) | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.64/1.39  tff(c_88, plain, (![B_46, A_47]: (v1_xboole_0(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_xboole_0(A_47))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.64/1.39  tff(c_123, plain, (![A_51, B_52]: (v1_xboole_0(A_51) | ~v1_xboole_0(B_52) | ~r1_tarski(A_51, B_52))), inference(resolution, [status(thm)], [c_30, c_88])).
% 2.64/1.39  tff(c_135, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_36, c_123])).
% 2.64/1.39  tff(c_136, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_135])).
% 2.64/1.39  tff(c_149, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_109, c_136])).
% 2.64/1.39  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.64/1.39  tff(c_165, plain, (![A_59, B_60]: (k6_setfam_1(A_59, B_60)=k1_setfam_1(B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(k1_zfmisc_1(A_59))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.64/1.39  tff(c_178, plain, (k6_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_165])).
% 2.64/1.39  tff(c_261, plain, (![A_71, B_72]: (k8_setfam_1(A_71, B_72)=k6_setfam_1(A_71, B_72) | k1_xboole_0=B_72 | ~m1_subset_1(B_72, k1_zfmisc_1(k1_zfmisc_1(A_71))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.64/1.39  tff(c_275, plain, (k8_setfam_1('#skF_3', '#skF_5')=k6_setfam_1('#skF_3', '#skF_5') | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_38, c_261])).
% 2.64/1.39  tff(c_281, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_178, c_275])).
% 2.64/1.39  tff(c_282, plain, (k8_setfam_1('#skF_3', '#skF_5')=k1_setfam_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_149, c_281])).
% 2.64/1.39  tff(c_209, plain, (![A_65, B_66]: (m1_subset_1(k8_setfam_1(A_65, B_66), k1_zfmisc_1(A_65)) | ~m1_subset_1(B_66, k1_zfmisc_1(k1_zfmisc_1(A_65))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.64/1.39  tff(c_28, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~m1_subset_1(A_26, k1_zfmisc_1(B_27)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.64/1.39  tff(c_223, plain, (![A_67, B_68]: (r1_tarski(k8_setfam_1(A_67, B_68), A_67) | ~m1_subset_1(B_68, k1_zfmisc_1(k1_zfmisc_1(A_67))))), inference(resolution, [status(thm)], [c_209, c_28])).
% 2.64/1.39  tff(c_237, plain, (r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_38, c_223])).
% 2.64/1.39  tff(c_283, plain, (r1_tarski(k1_setfam_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_282, c_237])).
% 2.64/1.39  tff(c_55, plain, (![A_40, B_41]: (r1_tarski(A_40, B_41) | ~m1_subset_1(A_40, k1_zfmisc_1(B_41)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.64/1.39  tff(c_66, plain, (r1_tarski('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_55])).
% 2.64/1.39  tff(c_177, plain, (k6_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_165])).
% 2.64/1.39  tff(c_272, plain, (k8_setfam_1('#skF_3', '#skF_4')=k6_setfam_1('#skF_3', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_40, c_261])).
% 2.64/1.39  tff(c_279, plain, (k8_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_177, c_272])).
% 2.64/1.39  tff(c_313, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_279])).
% 2.64/1.39  tff(c_159, plain, (![A_57]: (k8_setfam_1(A_57, k1_xboole_0)=A_57 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_57))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.64/1.39  tff(c_163, plain, (![A_57]: (k8_setfam_1(A_57, k1_xboole_0)=A_57 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_57)))), inference(resolution, [status(thm)], [c_30, c_159])).
% 2.64/1.39  tff(c_367, plain, (![A_80]: (k8_setfam_1(A_80, '#skF_4')=A_80 | ~r1_tarski('#skF_4', k1_zfmisc_1(A_80)))), inference(demodulation, [status(thm), theory('equality')], [c_313, c_313, c_163])).
% 2.64/1.39  tff(c_371, plain, (k8_setfam_1('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_66, c_367])).
% 2.64/1.40  tff(c_34, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_5'), k8_setfam_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.64/1.40  tff(c_284, plain, (~r1_tarski(k1_setfam_1('#skF_5'), k8_setfam_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_34])).
% 2.64/1.40  tff(c_372, plain, (~r1_tarski(k1_setfam_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_371, c_284])).
% 2.64/1.40  tff(c_376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_283, c_372])).
% 2.64/1.40  tff(c_378, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_279])).
% 2.64/1.40  tff(c_32, plain, (![B_29, A_28]: (r1_tarski(k1_setfam_1(B_29), k1_setfam_1(A_28)) | k1_xboole_0=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.64/1.40  tff(c_377, plain, (k8_setfam_1('#skF_3', '#skF_4')=k1_setfam_1('#skF_4')), inference(splitRight, [status(thm)], [c_279])).
% 2.64/1.40  tff(c_379, plain, (~r1_tarski(k1_setfam_1('#skF_5'), k1_setfam_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_377, c_284])).
% 2.64/1.40  tff(c_402, plain, (k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_32, c_379])).
% 2.64/1.40  tff(c_405, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_402])).
% 2.64/1.40  tff(c_407, plain, $false, inference(negUnitSimplification, [status(thm)], [c_378, c_405])).
% 2.64/1.40  tff(c_408, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_135])).
% 2.64/1.40  tff(c_43, plain, (![A_35]: (r2_hidden('#skF_2'(A_35), A_35) | k1_xboole_0=A_35)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.64/1.40  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.64/1.40  tff(c_47, plain, (![A_35]: (~v1_xboole_0(A_35) | k1_xboole_0=A_35)), inference(resolution, [status(thm)], [c_43, c_2])).
% 2.64/1.40  tff(c_413, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_408, c_47])).
% 2.64/1.40  tff(c_18, plain, (![A_18]: (k8_setfam_1(A_18, k1_xboole_0)=A_18 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_18))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.64/1.40  tff(c_496, plain, (![A_92]: (k8_setfam_1(A_92, '#skF_4')=A_92 | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1(A_92))))), inference(demodulation, [status(thm), theory('equality')], [c_413, c_413, c_18])).
% 2.64/1.40  tff(c_504, plain, (k8_setfam_1('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_40, c_496])).
% 2.64/1.40  tff(c_409, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_135])).
% 2.64/1.40  tff(c_417, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_409, c_47])).
% 2.64/1.40  tff(c_428, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_413, c_417])).
% 2.64/1.40  tff(c_431, plain, (~r1_tarski(k8_setfam_1('#skF_3', '#skF_4'), k8_setfam_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_428, c_34])).
% 2.64/1.40  tff(c_515, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_504, c_504, c_431])).
% 2.64/1.40  tff(c_548, plain, (![A_100, B_101]: (m1_subset_1(k8_setfam_1(A_100, B_101), k1_zfmisc_1(A_100)) | ~m1_subset_1(B_101, k1_zfmisc_1(k1_zfmisc_1(A_100))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.64/1.40  tff(c_561, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_504, c_548])).
% 2.64/1.40  tff(c_566, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_561])).
% 2.64/1.40  tff(c_572, plain, (r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_566, c_28])).
% 2.64/1.40  tff(c_577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_515, c_572])).
% 2.64/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.40  
% 2.64/1.40  Inference rules
% 2.64/1.40  ----------------------
% 2.64/1.40  #Ref     : 0
% 2.64/1.40  #Sup     : 114
% 2.64/1.40  #Fact    : 0
% 2.64/1.40  #Define  : 0
% 2.64/1.40  #Split   : 5
% 2.64/1.40  #Chain   : 0
% 2.64/1.40  #Close   : 0
% 2.64/1.40  
% 2.64/1.40  Ordering : KBO
% 2.64/1.40  
% 2.64/1.40  Simplification rules
% 2.64/1.40  ----------------------
% 2.64/1.40  #Subsume      : 17
% 2.64/1.40  #Demod        : 59
% 2.64/1.40  #Tautology    : 51
% 2.64/1.40  #SimpNegUnit  : 3
% 2.64/1.40  #BackRed      : 30
% 2.64/1.40  
% 2.64/1.40  #Partial instantiations: 0
% 2.64/1.40  #Strategies tried      : 1
% 2.64/1.40  
% 2.64/1.40  Timing (in seconds)
% 2.64/1.40  ----------------------
% 2.64/1.40  Preprocessing        : 0.31
% 2.64/1.40  Parsing              : 0.17
% 2.64/1.40  CNF conversion       : 0.02
% 2.64/1.40  Main loop            : 0.29
% 2.64/1.40  Inferencing          : 0.11
% 2.64/1.40  Reduction            : 0.09
% 2.64/1.40  Demodulation         : 0.06
% 2.64/1.40  BG Simplification    : 0.02
% 2.64/1.40  Subsumption          : 0.04
% 2.64/1.40  Abstraction          : 0.02
% 2.64/1.40  MUC search           : 0.00
% 2.64/1.40  Cooper               : 0.00
% 2.64/1.40  Total                : 0.65
% 2.64/1.40  Index Insertion      : 0.00
% 2.64/1.40  Index Deletion       : 0.00
% 2.64/1.40  Index Matching       : 0.00
% 2.64/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
