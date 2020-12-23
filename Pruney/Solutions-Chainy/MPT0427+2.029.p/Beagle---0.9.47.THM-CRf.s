%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:00 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 267 expanded)
%              Number of leaves         :   23 (  95 expanded)
%              Depth                    :   10
%              Number of atoms          :  113 ( 569 expanded)
%              Number of equality atoms :   47 ( 245 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_43,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_86,plain,(
    ! [A_30,B_31] :
      ( k6_setfam_1(A_30,B_31) = k1_setfam_1(B_31)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(k1_zfmisc_1(A_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_98,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_86])).

tff(c_154,plain,(
    ! [A_41,B_42] :
      ( k8_setfam_1(A_41,B_42) = k6_setfam_1(A_41,B_42)
      | k1_xboole_0 = B_42
      | ~ m1_subset_1(B_42,k1_zfmisc_1(k1_zfmisc_1(A_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_165,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_34,c_154])).

tff(c_172,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_165])).

tff(c_175,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_99,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_86])).

tff(c_168,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_154])).

tff(c_174,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_168])).

tff(c_201,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_174])).

tff(c_202,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_30,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_57,plain,(
    ! [B_24,A_25] :
      ( B_24 = A_25
      | ~ r1_tarski(B_24,A_25)
      | ~ r1_tarski(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_57])).

tff(c_73,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_209,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_73])).

tff(c_217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_209])).

tff(c_218,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_18,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(k8_setfam_1(A_9,B_10),k1_zfmisc_1(A_9))
      | ~ m1_subset_1(B_10,k1_zfmisc_1(k1_zfmisc_1(A_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_224,plain,
    ( m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_18])).

tff(c_228,plain,(
    m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_224])).

tff(c_22,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_233,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_228,c_22])).

tff(c_44,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_55,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_34,c_44])).

tff(c_24,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,k1_zfmisc_1(B_14))
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_75,plain,(
    ! [A_26] :
      ( k8_setfam_1(A_26,k1_xboole_0) = A_26
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_79,plain,(
    ! [A_26] :
      ( k8_setfam_1(A_26,k1_xboole_0) = A_26
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_26)) ) ),
    inference(resolution,[status(thm)],[c_24,c_75])).

tff(c_238,plain,(
    ! [A_45] :
      ( k8_setfam_1(A_45,'#skF_2') = A_45
      | ~ r1_tarski('#skF_2',k1_zfmisc_1(A_45)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_175,c_79])).

tff(c_242,plain,(
    k8_setfam_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_55,c_238])).

tff(c_28,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_220,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_28])).

tff(c_252,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_220])).

tff(c_255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_252])).

tff(c_257,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_setfam_1(B_16),k1_setfam_1(A_15))
      | k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_275,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_174])).

tff(c_276,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_257])).

tff(c_8,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_124,plain,(
    ! [A_34,B_35,C_36] :
      ( k1_xboole_0 = A_34
      | ~ r1_xboole_0(B_35,C_36)
      | ~ r1_tarski(A_34,C_36)
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_127,plain,(
    ! [A_34] :
      ( k1_xboole_0 = A_34
      | ~ r1_tarski(A_34,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_124])).

tff(c_295,plain,(
    ! [A_48] :
      ( A_48 = '#skF_3'
      | ~ r1_tarski(A_48,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_275,c_127])).

tff(c_302,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_295])).

tff(c_308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_276,c_302])).

tff(c_309,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_174])).

tff(c_256,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_258,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_28])).

tff(c_311,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_258])).

tff(c_323,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_311])).

tff(c_326,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_323])).

tff(c_328,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_257,c_326])).

tff(c_329,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_332,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_28])).

tff(c_338,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_332])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n023.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 19:11:20 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.41  
% 2.09/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.41  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.09/1.41  
% 2.09/1.41  %Foreground sorts:
% 2.09/1.41  
% 2.09/1.41  
% 2.09/1.41  %Background operators:
% 2.09/1.41  
% 2.09/1.41  
% 2.09/1.41  %Foreground operators:
% 2.09/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.41  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.09/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.09/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.41  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.09/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.41  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.09/1.41  
% 2.09/1.43  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.09/1.43  tff(f_90, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.09/1.43  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.09/1.43  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.09/1.43  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.09/1.43  tff(f_74, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.09/1.43  tff(f_80, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.09/1.43  tff(f_43, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.09/1.43  tff(f_51, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 2.09/1.43  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.09/1.43  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.09/1.43  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.09/1.43  tff(c_86, plain, (![A_30, B_31]: (k6_setfam_1(A_30, B_31)=k1_setfam_1(B_31) | ~m1_subset_1(B_31, k1_zfmisc_1(k1_zfmisc_1(A_30))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.09/1.43  tff(c_98, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_86])).
% 2.09/1.43  tff(c_154, plain, (![A_41, B_42]: (k8_setfam_1(A_41, B_42)=k6_setfam_1(A_41, B_42) | k1_xboole_0=B_42 | ~m1_subset_1(B_42, k1_zfmisc_1(k1_zfmisc_1(A_41))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.09/1.43  tff(c_165, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_34, c_154])).
% 2.09/1.43  tff(c_172, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_165])).
% 2.09/1.43  tff(c_175, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_172])).
% 2.09/1.43  tff(c_99, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_86])).
% 2.09/1.43  tff(c_168, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_32, c_154])).
% 2.09/1.43  tff(c_174, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_99, c_168])).
% 2.09/1.43  tff(c_201, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_175, c_174])).
% 2.09/1.43  tff(c_202, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_201])).
% 2.09/1.43  tff(c_30, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.09/1.43  tff(c_57, plain, (![B_24, A_25]: (B_24=A_25 | ~r1_tarski(B_24, A_25) | ~r1_tarski(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.09/1.43  tff(c_72, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_57])).
% 2.09/1.43  tff(c_73, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_72])).
% 2.09/1.43  tff(c_209, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_202, c_73])).
% 2.09/1.43  tff(c_217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_209])).
% 2.09/1.43  tff(c_218, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_201])).
% 2.09/1.43  tff(c_18, plain, (![A_9, B_10]: (m1_subset_1(k8_setfam_1(A_9, B_10), k1_zfmisc_1(A_9)) | ~m1_subset_1(B_10, k1_zfmisc_1(k1_zfmisc_1(A_9))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.09/1.43  tff(c_224, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_218, c_18])).
% 2.09/1.43  tff(c_228, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_224])).
% 2.09/1.43  tff(c_22, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.09/1.43  tff(c_233, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_228, c_22])).
% 2.09/1.43  tff(c_44, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.09/1.43  tff(c_55, plain, (r1_tarski('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_34, c_44])).
% 2.09/1.43  tff(c_24, plain, (![A_13, B_14]: (m1_subset_1(A_13, k1_zfmisc_1(B_14)) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.09/1.43  tff(c_75, plain, (![A_26]: (k8_setfam_1(A_26, k1_xboole_0)=A_26 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_26))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.09/1.43  tff(c_79, plain, (![A_26]: (k8_setfam_1(A_26, k1_xboole_0)=A_26 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_26)))), inference(resolution, [status(thm)], [c_24, c_75])).
% 2.09/1.43  tff(c_238, plain, (![A_45]: (k8_setfam_1(A_45, '#skF_2')=A_45 | ~r1_tarski('#skF_2', k1_zfmisc_1(A_45)))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_175, c_79])).
% 2.09/1.43  tff(c_242, plain, (k8_setfam_1('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_55, c_238])).
% 2.09/1.43  tff(c_28, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.09/1.43  tff(c_220, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_218, c_28])).
% 2.09/1.43  tff(c_252, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_242, c_220])).
% 2.09/1.43  tff(c_255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_233, c_252])).
% 2.09/1.43  tff(c_257, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_172])).
% 2.09/1.43  tff(c_26, plain, (![B_16, A_15]: (r1_tarski(k1_setfam_1(B_16), k1_setfam_1(A_15)) | k1_xboole_0=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.09/1.43  tff(c_275, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_174])).
% 2.09/1.43  tff(c_276, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_275, c_257])).
% 2.09/1.43  tff(c_8, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.09/1.43  tff(c_124, plain, (![A_34, B_35, C_36]: (k1_xboole_0=A_34 | ~r1_xboole_0(B_35, C_36) | ~r1_tarski(A_34, C_36) | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.09/1.43  tff(c_127, plain, (![A_34]: (k1_xboole_0=A_34 | ~r1_tarski(A_34, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_124])).
% 2.09/1.43  tff(c_295, plain, (![A_48]: (A_48='#skF_3' | ~r1_tarski(A_48, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_275, c_275, c_127])).
% 2.09/1.43  tff(c_302, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_30, c_295])).
% 2.09/1.43  tff(c_308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_276, c_302])).
% 2.09/1.43  tff(c_309, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_174])).
% 2.09/1.43  tff(c_256, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_172])).
% 2.09/1.43  tff(c_258, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_28])).
% 2.09/1.43  tff(c_311, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_258])).
% 2.09/1.43  tff(c_323, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_311])).
% 2.09/1.43  tff(c_326, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_323])).
% 2.09/1.43  tff(c_328, plain, $false, inference(negUnitSimplification, [status(thm)], [c_257, c_326])).
% 2.09/1.43  tff(c_329, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_72])).
% 2.09/1.43  tff(c_332, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_329, c_28])).
% 2.09/1.43  tff(c_338, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_332])).
% 2.09/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.43  
% 2.09/1.43  Inference rules
% 2.09/1.43  ----------------------
% 2.09/1.43  #Ref     : 0
% 2.09/1.43  #Sup     : 56
% 2.09/1.43  #Fact    : 0
% 2.09/1.43  #Define  : 0
% 2.09/1.43  #Split   : 7
% 2.09/1.43  #Chain   : 0
% 2.09/1.43  #Close   : 0
% 2.09/1.43  
% 2.09/1.43  Ordering : KBO
% 2.09/1.43  
% 2.09/1.43  Simplification rules
% 2.09/1.43  ----------------------
% 2.09/1.43  #Subsume      : 2
% 2.09/1.43  #Demod        : 63
% 2.09/1.43  #Tautology    : 29
% 2.09/1.43  #SimpNegUnit  : 2
% 2.09/1.43  #BackRed      : 36
% 2.09/1.43  
% 2.09/1.43  #Partial instantiations: 0
% 2.09/1.43  #Strategies tried      : 1
% 2.09/1.43  
% 2.09/1.43  Timing (in seconds)
% 2.09/1.43  ----------------------
% 2.09/1.43  Preprocessing        : 0.32
% 2.09/1.43  Parsing              : 0.16
% 2.09/1.43  CNF conversion       : 0.02
% 2.09/1.43  Main loop            : 0.22
% 2.09/1.43  Inferencing          : 0.07
% 2.09/1.43  Reduction            : 0.07
% 2.09/1.43  Demodulation         : 0.05
% 2.09/1.43  BG Simplification    : 0.01
% 2.09/1.43  Subsumption          : 0.05
% 2.09/1.43  Abstraction          : 0.01
% 2.09/1.43  MUC search           : 0.00
% 2.09/1.43  Cooper               : 0.00
% 2.09/1.43  Total                : 0.57
% 2.09/1.43  Index Insertion      : 0.00
% 2.09/1.43  Index Deletion       : 0.00
% 2.09/1.43  Index Matching       : 0.00
% 2.09/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
