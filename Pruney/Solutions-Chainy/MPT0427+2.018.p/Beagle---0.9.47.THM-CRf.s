%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:58 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 311 expanded)
%              Number of leaves         :   29 ( 111 expanded)
%              Depth                    :   10
%              Number of atoms          :  140 ( 652 expanded)
%              Number of equality atoms :   46 ( 222 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_80,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_97,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_12,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_38,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_103,plain,(
    ! [C_39,B_40,A_41] :
      ( ~ v1_xboole_0(C_39)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(C_39))
      | ~ r2_hidden(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_124,plain,(
    ! [B_46,A_47,A_48] :
      ( ~ v1_xboole_0(B_46)
      | ~ r2_hidden(A_47,A_48)
      | ~ r1_tarski(A_48,B_46) ) ),
    inference(resolution,[status(thm)],[c_30,c_103])).

tff(c_128,plain,(
    ! [B_49,A_50] :
      ( ~ v1_xboole_0(B_49)
      | ~ r1_tarski(A_50,B_49)
      | v1_xboole_0(A_50) ) ),
    inference(resolution,[status(thm)],[c_4,c_124])).

tff(c_148,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_128])).

tff(c_149,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_150,plain,(
    ! [A_51,B_52] :
      ( k6_setfam_1(A_51,B_52) = k1_setfam_1(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_162,plain,(
    k6_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_150])).

tff(c_201,plain,(
    ! [A_57,B_58] :
      ( k8_setfam_1(A_57,B_58) = k6_setfam_1(A_57,B_58)
      | k1_xboole_0 = B_58
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k1_zfmisc_1(A_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_212,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k6_setfam_1('#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_42,c_201])).

tff(c_219,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_212])).

tff(c_222,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_163,plain,(
    k6_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_150])).

tff(c_215,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k6_setfam_1('#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_201])).

tff(c_221,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_215])).

tff(c_253,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_221])).

tff(c_254,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_253])).

tff(c_14,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_72,plain,(
    ! [B_35,A_36] :
      ( ~ r1_xboole_0(B_35,A_36)
      | ~ r1_tarski(B_35,A_36)
      | v1_xboole_0(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_75,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_72])).

tff(c_78,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_75])).

tff(c_227,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_78])).

tff(c_258,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_227])).

tff(c_268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_258])).

tff(c_269,plain,(
    k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_253])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k8_setfam_1(A_13,B_14),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(k1_zfmisc_1(A_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_275,plain,
    ( m1_subset_1(k1_setfam_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_24])).

tff(c_279,plain,(
    m1_subset_1(k1_setfam_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_275])).

tff(c_28,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_287,plain,(
    r1_tarski(k1_setfam_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_279,c_28])).

tff(c_59,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | ~ m1_subset_1(A_33,k1_zfmisc_1(B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_70,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_42,c_59])).

tff(c_114,plain,(
    ! [A_42] :
      ( k8_setfam_1(A_42,k1_xboole_0) = A_42
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_118,plain,(
    ! [A_42] :
      ( k8_setfam_1(A_42,k1_xboole_0) = A_42
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_42)) ) ),
    inference(resolution,[status(thm)],[c_30,c_114])).

tff(c_296,plain,(
    ! [A_61] :
      ( k8_setfam_1(A_61,'#skF_3') = A_61
      | ~ r1_tarski('#skF_3',k1_zfmisc_1(A_61)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_222,c_118])).

tff(c_300,plain,(
    k8_setfam_1('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_70,c_296])).

tff(c_36,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k8_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_271,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),k8_setfam_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_36])).

tff(c_301,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_271])).

tff(c_304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_301])).

tff(c_306,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_34,plain,(
    ! [B_23,A_22] :
      ( r1_tarski(k1_setfam_1(B_23),k1_setfam_1(A_22))
      | k1_xboole_0 = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_332,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_338,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_78])).

tff(c_343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_338])).

tff(c_344,plain,(
    k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_305,plain,(
    k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_307,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k1_setfam_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_305,c_36])).

tff(c_346,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),k1_setfam_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_307])).

tff(c_358,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_346])).

tff(c_361,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_358])).

tff(c_363,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_306,c_361])).

tff(c_365,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_373,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_365,c_6])).

tff(c_364,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_369,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_364,c_6])).

tff(c_386,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_369])).

tff(c_79,plain,(
    ! [B_37,A_38] :
      ( B_37 = A_38
      | ~ r1_tarski(B_37,A_38)
      | ~ r1_tarski(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_94,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_79])).

tff(c_100,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_393,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_100])).

tff(c_401,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_393])).

tff(c_402,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_410,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k8_setfam_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_36])).

tff(c_416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_410])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:45:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.32  
% 2.48/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.32  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.48/1.32  
% 2.48/1.32  %Foreground sorts:
% 2.48/1.32  
% 2.48/1.32  
% 2.48/1.32  %Background operators:
% 2.48/1.32  
% 2.48/1.32  
% 2.48/1.32  %Foreground operators:
% 2.48/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.48/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.32  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.48/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.48/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.48/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.48/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.48/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.48/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.48/1.32  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.48/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.48/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.48/1.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.48/1.32  
% 2.48/1.34  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.48/1.34  tff(f_107, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.48/1.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.48/1.34  tff(f_84, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.48/1.34  tff(f_91, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 2.48/1.34  tff(f_80, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.48/1.34  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.48/1.34  tff(f_53, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.48/1.34  tff(f_61, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.48/1.34  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.48/1.34  tff(f_97, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.48/1.34  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.48/1.34  tff(c_12, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.48/1.34  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.48/1.34  tff(c_38, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.48/1.34  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.34  tff(c_30, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.48/1.34  tff(c_103, plain, (![C_39, B_40, A_41]: (~v1_xboole_0(C_39) | ~m1_subset_1(B_40, k1_zfmisc_1(C_39)) | ~r2_hidden(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.48/1.34  tff(c_124, plain, (![B_46, A_47, A_48]: (~v1_xboole_0(B_46) | ~r2_hidden(A_47, A_48) | ~r1_tarski(A_48, B_46))), inference(resolution, [status(thm)], [c_30, c_103])).
% 2.48/1.34  tff(c_128, plain, (![B_49, A_50]: (~v1_xboole_0(B_49) | ~r1_tarski(A_50, B_49) | v1_xboole_0(A_50))), inference(resolution, [status(thm)], [c_4, c_124])).
% 2.48/1.34  tff(c_148, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_128])).
% 2.48/1.34  tff(c_149, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_148])).
% 2.48/1.34  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.48/1.34  tff(c_150, plain, (![A_51, B_52]: (k6_setfam_1(A_51, B_52)=k1_setfam_1(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(k1_zfmisc_1(A_51))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.48/1.34  tff(c_162, plain, (k6_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_42, c_150])).
% 2.48/1.34  tff(c_201, plain, (![A_57, B_58]: (k8_setfam_1(A_57, B_58)=k6_setfam_1(A_57, B_58) | k1_xboole_0=B_58 | ~m1_subset_1(B_58, k1_zfmisc_1(k1_zfmisc_1(A_57))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.48/1.34  tff(c_212, plain, (k8_setfam_1('#skF_2', '#skF_3')=k6_setfam_1('#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_42, c_201])).
% 2.48/1.34  tff(c_219, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_162, c_212])).
% 2.48/1.34  tff(c_222, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_219])).
% 2.48/1.34  tff(c_163, plain, (k6_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_150])).
% 2.48/1.34  tff(c_215, plain, (k8_setfam_1('#skF_2', '#skF_4')=k6_setfam_1('#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_40, c_201])).
% 2.48/1.34  tff(c_221, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_163, c_215])).
% 2.48/1.34  tff(c_253, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_222, c_221])).
% 2.48/1.34  tff(c_254, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_253])).
% 2.48/1.34  tff(c_14, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.48/1.34  tff(c_72, plain, (![B_35, A_36]: (~r1_xboole_0(B_35, A_36) | ~r1_tarski(B_35, A_36) | v1_xboole_0(B_35))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.48/1.34  tff(c_75, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0) | v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_72])).
% 2.48/1.34  tff(c_78, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_75])).
% 2.48/1.34  tff(c_227, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_222, c_78])).
% 2.48/1.34  tff(c_258, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_254, c_227])).
% 2.48/1.34  tff(c_268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_258])).
% 2.48/1.34  tff(c_269, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(splitRight, [status(thm)], [c_253])).
% 2.48/1.34  tff(c_24, plain, (![A_13, B_14]: (m1_subset_1(k8_setfam_1(A_13, B_14), k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(k1_zfmisc_1(A_13))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.48/1.34  tff(c_275, plain, (m1_subset_1(k1_setfam_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_269, c_24])).
% 2.48/1.34  tff(c_279, plain, (m1_subset_1(k1_setfam_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_275])).
% 2.48/1.34  tff(c_28, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.48/1.34  tff(c_287, plain, (r1_tarski(k1_setfam_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_279, c_28])).
% 2.48/1.34  tff(c_59, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | ~m1_subset_1(A_33, k1_zfmisc_1(B_34)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.48/1.34  tff(c_70, plain, (r1_tarski('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_59])).
% 2.48/1.34  tff(c_114, plain, (![A_42]: (k8_setfam_1(A_42, k1_xboole_0)=A_42 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_42))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.48/1.34  tff(c_118, plain, (![A_42]: (k8_setfam_1(A_42, k1_xboole_0)=A_42 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_42)))), inference(resolution, [status(thm)], [c_30, c_114])).
% 2.48/1.34  tff(c_296, plain, (![A_61]: (k8_setfam_1(A_61, '#skF_3')=A_61 | ~r1_tarski('#skF_3', k1_zfmisc_1(A_61)))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_222, c_118])).
% 2.48/1.34  tff(c_300, plain, (k8_setfam_1('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_70, c_296])).
% 2.48/1.34  tff(c_36, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k8_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 2.48/1.34  tff(c_271, plain, (~r1_tarski(k1_setfam_1('#skF_4'), k8_setfam_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_36])).
% 2.48/1.34  tff(c_301, plain, (~r1_tarski(k1_setfam_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_300, c_271])).
% 2.48/1.34  tff(c_304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_287, c_301])).
% 2.48/1.34  tff(c_306, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_219])).
% 2.48/1.34  tff(c_34, plain, (![B_23, A_22]: (r1_tarski(k1_setfam_1(B_23), k1_setfam_1(A_22)) | k1_xboole_0=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.48/1.34  tff(c_332, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_221])).
% 2.48/1.34  tff(c_338, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_332, c_78])).
% 2.48/1.34  tff(c_343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_338])).
% 2.48/1.34  tff(c_344, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(splitRight, [status(thm)], [c_221])).
% 2.48/1.34  tff(c_305, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_219])).
% 2.48/1.34  tff(c_307, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k1_setfam_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_305, c_36])).
% 2.48/1.34  tff(c_346, plain, (~r1_tarski(k1_setfam_1('#skF_4'), k1_setfam_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_344, c_307])).
% 2.48/1.34  tff(c_358, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_34, c_346])).
% 2.48/1.34  tff(c_361, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_358])).
% 2.48/1.34  tff(c_363, plain, $false, inference(negUnitSimplification, [status(thm)], [c_306, c_361])).
% 2.48/1.34  tff(c_365, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_148])).
% 2.48/1.34  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.48/1.34  tff(c_373, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_365, c_6])).
% 2.48/1.34  tff(c_364, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_148])).
% 2.48/1.34  tff(c_369, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_364, c_6])).
% 2.48/1.34  tff(c_386, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_373, c_369])).
% 2.48/1.34  tff(c_79, plain, (![B_37, A_38]: (B_37=A_38 | ~r1_tarski(B_37, A_38) | ~r1_tarski(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.48/1.34  tff(c_94, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_79])).
% 2.48/1.34  tff(c_100, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_94])).
% 2.48/1.34  tff(c_393, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_386, c_100])).
% 2.48/1.34  tff(c_401, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_393])).
% 2.48/1.34  tff(c_402, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_94])).
% 2.48/1.34  tff(c_410, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k8_setfam_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_402, c_36])).
% 2.48/1.34  tff(c_416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_410])).
% 2.48/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.48/1.34  
% 2.48/1.34  Inference rules
% 2.48/1.34  ----------------------
% 2.48/1.34  #Ref     : 0
% 2.48/1.34  #Sup     : 70
% 2.48/1.34  #Fact    : 0
% 2.48/1.34  #Define  : 0
% 2.48/1.34  #Split   : 10
% 2.48/1.34  #Chain   : 0
% 2.48/1.34  #Close   : 0
% 2.48/1.34  
% 2.48/1.34  Ordering : KBO
% 2.48/1.34  
% 2.48/1.34  Simplification rules
% 2.48/1.34  ----------------------
% 2.48/1.34  #Subsume      : 5
% 2.48/1.34  #Demod        : 83
% 2.48/1.34  #Tautology    : 31
% 2.48/1.34  #SimpNegUnit  : 3
% 2.48/1.34  #BackRed      : 52
% 2.48/1.34  
% 2.48/1.34  #Partial instantiations: 0
% 2.48/1.34  #Strategies tried      : 1
% 2.48/1.34  
% 2.48/1.34  Timing (in seconds)
% 2.48/1.34  ----------------------
% 2.48/1.34  Preprocessing        : 0.32
% 2.48/1.34  Parsing              : 0.16
% 2.48/1.34  CNF conversion       : 0.02
% 2.48/1.34  Main loop            : 0.26
% 2.48/1.34  Inferencing          : 0.08
% 2.48/1.34  Reduction            : 0.09
% 2.48/1.34  Demodulation         : 0.06
% 2.48/1.34  BG Simplification    : 0.02
% 2.48/1.34  Subsumption          : 0.05
% 2.48/1.34  Abstraction          : 0.02
% 2.48/1.34  MUC search           : 0.00
% 2.48/1.34  Cooper               : 0.00
% 2.48/1.34  Total                : 0.61
% 2.48/1.34  Index Insertion      : 0.00
% 2.48/1.34  Index Deletion       : 0.00
% 2.48/1.34  Index Matching       : 0.00
% 2.48/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
