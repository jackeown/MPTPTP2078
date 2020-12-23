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
% DateTime   : Thu Dec  3 09:58:02 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 503 expanded)
%              Number of leaves         :   27 ( 171 expanded)
%              Depth                    :   13
%              Number of atoms          :  177 (1043 expanded)
%              Number of equality atoms :   59 ( 231 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_34,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_36,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(c_28,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_4,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_65,plain,(
    ! [C_29,B_30,A_31] :
      ( ~ v1_xboole_0(C_29)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(C_29))
      | ~ r2_hidden(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_121,plain,(
    ! [B_36,A_37,A_38] :
      ( ~ v1_xboole_0(B_36)
      | ~ r2_hidden(A_37,A_38)
      | ~ r1_tarski(A_38,B_36) ) ),
    inference(resolution,[status(thm)],[c_18,c_65])).

tff(c_125,plain,(
    ! [B_39,A_40] :
      ( ~ v1_xboole_0(B_39)
      | ~ r1_tarski(A_40,B_39)
      | k1_xboole_0 = A_40 ) ),
    inference(resolution,[status(thm)],[c_4,c_121])).

tff(c_142,plain,
    ( ~ v1_xboole_0('#skF_4')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_125])).

tff(c_148,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_142])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_166,plain,(
    ! [A_45,C_46,B_47] :
      ( m1_subset_1(A_45,C_46)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(C_46))
      | ~ r2_hidden(A_45,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_179,plain,(
    ! [A_48] :
      ( m1_subset_1(A_48,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_48,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_32,c_166])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_190,plain,(
    ! [A_49] :
      ( r1_tarski(A_49,'#skF_2')
      | ~ r2_hidden(A_49,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_179,c_16])).

tff(c_195,plain,
    ( r1_tarski('#skF_1'('#skF_3'),'#skF_2')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4,c_190])).

tff(c_196,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_195])).

tff(c_342,plain,(
    ! [A_65] :
      ( r2_hidden('#skF_1'(A_65),A_65)
      | A_65 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_4])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_253,plain,(
    ! [A_55] :
      ( m1_subset_1(A_55,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_55,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_166])).

tff(c_263,plain,(
    ! [A_55] :
      ( r1_tarski(A_55,'#skF_2')
      | ~ r2_hidden(A_55,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_253,c_16])).

tff(c_356,plain,
    ( r1_tarski('#skF_1'('#skF_4'),'#skF_2')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_342,c_263])).

tff(c_367,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_356])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_205,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_2])).

tff(c_376,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_367,c_205])).

tff(c_379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_376])).

tff(c_381,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_356])).

tff(c_79,plain,(
    ! [A_32,B_33] :
      ( k6_setfam_1(A_32,B_33) = k1_setfam_1(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(A_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_96,plain,(
    k6_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_79])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( k8_setfam_1(A_4,B_5) = k6_setfam_1(A_4,B_5)
      | k1_xboole_0 = B_5
      | ~ m1_subset_1(B_5,k1_zfmisc_1(k1_zfmisc_1(A_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_310,plain,(
    ! [A_60,B_61] :
      ( k8_setfam_1(A_60,B_61) = k6_setfam_1(A_60,B_61)
      | B_61 = '#skF_3'
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_10])).

tff(c_329,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k6_setfam_1('#skF_2','#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_310])).

tff(c_337,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_329])).

tff(c_415,plain,(
    k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_337])).

tff(c_6,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    ! [A_4] :
      ( k8_setfam_1(A_4,k1_xboole_0) = A_4
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,(
    ! [A_4] : k8_setfam_1(A_4,k1_xboole_0) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_203,plain,(
    ! [A_4] : k8_setfam_1(A_4,'#skF_3') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_34])).

tff(c_26,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k8_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_264,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_26])).

tff(c_416,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_415,c_264])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k8_setfam_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(A_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_420,plain,
    ( m1_subset_1(k1_setfam_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_415,c_12])).

tff(c_424,plain,(
    m1_subset_1(k1_setfam_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_420])).

tff(c_432,plain,(
    r1_tarski(k1_setfam_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_424,c_16])).

tff(c_438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_416,c_432])).

tff(c_440,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_195])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_setfam_1(B_19),k1_setfam_1(A_18))
      | k1_xboole_0 = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_493,plain,(
    ! [A_77] :
      ( m1_subset_1(A_77,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_77,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_166])).

tff(c_515,plain,(
    ! [A_81] :
      ( r1_tarski(A_81,'#skF_2')
      | ~ r2_hidden(A_81,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_493,c_16])).

tff(c_520,plain,
    ( r1_tarski('#skF_1'('#skF_4'),'#skF_2')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4,c_515])).

tff(c_526,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_520])).

tff(c_572,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_2])).

tff(c_574,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_572])).

tff(c_576,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_520])).

tff(c_624,plain,(
    ! [A_92,B_93] :
      ( k8_setfam_1(A_92,B_93) = k6_setfam_1(A_92,B_93)
      | k1_xboole_0 = B_93
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k1_zfmisc_1(A_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_646,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k6_setfam_1('#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_624])).

tff(c_660,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_646])).

tff(c_661,plain,(
    k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_576,c_660])).

tff(c_95,plain,(
    k6_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_79])).

tff(c_643,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k6_setfam_1('#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_624])).

tff(c_657,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_643])).

tff(c_658,plain,(
    k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_440,c_657])).

tff(c_665,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k1_setfam_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_658,c_26])).

tff(c_694,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),k1_setfam_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_661,c_665])).

tff(c_697,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_694])).

tff(c_700,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_697])).

tff(c_702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_440,c_700])).

tff(c_703,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_712,plain,(
    ! [A_3] : m1_subset_1('#skF_3',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_703,c_6])).

tff(c_711,plain,(
    ! [A_4] : k8_setfam_1(A_4,'#skF_3') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_703,c_34])).

tff(c_797,plain,(
    ! [A_105,B_106] :
      ( m1_subset_1(k8_setfam_1(A_105,B_106),k1_zfmisc_1(A_105))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(k1_zfmisc_1(A_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_811,plain,(
    ! [A_4] :
      ( m1_subset_1(A_4,k1_zfmisc_1(A_4))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_4))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_711,c_797])).

tff(c_839,plain,(
    ! [A_109] : m1_subset_1(A_109,k1_zfmisc_1(A_109)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_712,c_811])).

tff(c_854,plain,(
    ! [A_109] : r1_tarski(A_109,A_109) ),
    inference(resolution,[status(thm)],[c_839,c_16])).

tff(c_710,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | A_1 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_703,c_4])).

tff(c_722,plain,(
    ! [A_96,C_97,B_98] :
      ( m1_subset_1(A_96,C_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(C_97))
      | ~ r2_hidden(A_96,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_779,plain,(
    ! [A_103] :
      ( m1_subset_1(A_103,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_103,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_722])).

tff(c_790,plain,(
    ! [A_104] :
      ( r1_tarski(A_104,'#skF_2')
      | ~ r2_hidden(A_104,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_779,c_16])).

tff(c_795,plain,
    ( r1_tarski('#skF_1'('#skF_4'),'#skF_2')
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_710,c_790])).

tff(c_796,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_795])).

tff(c_820,plain,(
    ! [A_4] : k8_setfam_1(A_4,'#skF_4') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_796,c_711])).

tff(c_750,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_711,c_26])).

tff(c_856,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_820,c_750])).

tff(c_859,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_854,c_856])).

tff(c_861,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_795])).

tff(c_704,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_142])).

tff(c_862,plain,(
    ! [A_111,B_112] :
      ( m1_subset_1(k8_setfam_1(A_111,B_112),k1_zfmisc_1(A_111))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(k1_zfmisc_1(A_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_876,plain,(
    ! [A_4] :
      ( m1_subset_1(A_4,k1_zfmisc_1(A_4))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_4))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_711,c_862])).

tff(c_883,plain,(
    ! [A_113] : m1_subset_1(A_113,k1_zfmisc_1(A_113)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_712,c_876])).

tff(c_22,plain,(
    ! [C_17,B_16,A_15] :
      ( ~ v1_xboole_0(C_17)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(C_17))
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_901,plain,(
    ! [A_115,A_116] :
      ( ~ v1_xboole_0(A_115)
      | ~ r2_hidden(A_116,A_115) ) ),
    inference(resolution,[status(thm)],[c_883,c_22])).

tff(c_906,plain,(
    ! [A_117] :
      ( ~ v1_xboole_0(A_117)
      | A_117 = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_710,c_901])).

tff(c_912,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_704,c_906])).

tff(c_918,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_861,c_912])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:05:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.60  
% 3.02/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.60  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.02/1.60  
% 3.02/1.60  %Foreground sorts:
% 3.02/1.60  
% 3.02/1.60  
% 3.02/1.60  %Background operators:
% 3.02/1.60  
% 3.02/1.60  
% 3.02/1.60  %Foreground operators:
% 3.02/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.02/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.02/1.60  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.02/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.02/1.60  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 3.02/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.02/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.02/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.02/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.02/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.02/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.02/1.60  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.02/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.02/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.02/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.02/1.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.02/1.60  
% 3.02/1.62  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 3.02/1.62  tff(f_34, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.02/1.62  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.02/1.62  tff(f_72, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 3.02/1.62  tff(f_65, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.02/1.62  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.02/1.62  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.02/1.62  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.02/1.62  tff(f_36, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.02/1.62  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 3.02/1.62  tff(f_78, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.02/1.62  tff(c_28, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.02/1.62  tff(c_4, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.02/1.62  tff(c_18, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.02/1.62  tff(c_65, plain, (![C_29, B_30, A_31]: (~v1_xboole_0(C_29) | ~m1_subset_1(B_30, k1_zfmisc_1(C_29)) | ~r2_hidden(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.02/1.62  tff(c_121, plain, (![B_36, A_37, A_38]: (~v1_xboole_0(B_36) | ~r2_hidden(A_37, A_38) | ~r1_tarski(A_38, B_36))), inference(resolution, [status(thm)], [c_18, c_65])).
% 3.02/1.62  tff(c_125, plain, (![B_39, A_40]: (~v1_xboole_0(B_39) | ~r1_tarski(A_40, B_39) | k1_xboole_0=A_40)), inference(resolution, [status(thm)], [c_4, c_121])).
% 3.02/1.62  tff(c_142, plain, (~v1_xboole_0('#skF_4') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_28, c_125])).
% 3.02/1.62  tff(c_148, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_142])).
% 3.02/1.62  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.02/1.62  tff(c_166, plain, (![A_45, C_46, B_47]: (m1_subset_1(A_45, C_46) | ~m1_subset_1(B_47, k1_zfmisc_1(C_46)) | ~r2_hidden(A_45, B_47))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.02/1.62  tff(c_179, plain, (![A_48]: (m1_subset_1(A_48, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_48, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_166])).
% 3.02/1.62  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.02/1.62  tff(c_190, plain, (![A_49]: (r1_tarski(A_49, '#skF_2') | ~r2_hidden(A_49, '#skF_3'))), inference(resolution, [status(thm)], [c_179, c_16])).
% 3.02/1.62  tff(c_195, plain, (r1_tarski('#skF_1'('#skF_3'), '#skF_2') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_4, c_190])).
% 3.02/1.62  tff(c_196, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_195])).
% 3.02/1.62  tff(c_342, plain, (![A_65]: (r2_hidden('#skF_1'(A_65), A_65) | A_65='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_4])).
% 3.02/1.62  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.02/1.62  tff(c_253, plain, (![A_55]: (m1_subset_1(A_55, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_55, '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_166])).
% 3.02/1.62  tff(c_263, plain, (![A_55]: (r1_tarski(A_55, '#skF_2') | ~r2_hidden(A_55, '#skF_4'))), inference(resolution, [status(thm)], [c_253, c_16])).
% 3.02/1.62  tff(c_356, plain, (r1_tarski('#skF_1'('#skF_4'), '#skF_2') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_342, c_263])).
% 3.02/1.62  tff(c_367, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_356])).
% 3.02/1.62  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.02/1.62  tff(c_205, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_196, c_2])).
% 3.02/1.62  tff(c_376, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_367, c_205])).
% 3.02/1.62  tff(c_379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_376])).
% 3.02/1.62  tff(c_381, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_356])).
% 3.02/1.62  tff(c_79, plain, (![A_32, B_33]: (k6_setfam_1(A_32, B_33)=k1_setfam_1(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(k1_zfmisc_1(A_32))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.02/1.62  tff(c_96, plain, (k6_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_79])).
% 3.02/1.62  tff(c_10, plain, (![A_4, B_5]: (k8_setfam_1(A_4, B_5)=k6_setfam_1(A_4, B_5) | k1_xboole_0=B_5 | ~m1_subset_1(B_5, k1_zfmisc_1(k1_zfmisc_1(A_4))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.02/1.62  tff(c_310, plain, (![A_60, B_61]: (k8_setfam_1(A_60, B_61)=k6_setfam_1(A_60, B_61) | B_61='#skF_3' | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(A_60))))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_10])).
% 3.02/1.62  tff(c_329, plain, (k8_setfam_1('#skF_2', '#skF_4')=k6_setfam_1('#skF_2', '#skF_4') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_30, c_310])).
% 3.02/1.62  tff(c_337, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_329])).
% 3.02/1.62  tff(c_415, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_381, c_337])).
% 3.02/1.62  tff(c_6, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.02/1.62  tff(c_8, plain, (![A_4]: (k8_setfam_1(A_4, k1_xboole_0)=A_4 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_4))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.02/1.62  tff(c_34, plain, (![A_4]: (k8_setfam_1(A_4, k1_xboole_0)=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 3.02/1.62  tff(c_203, plain, (![A_4]: (k8_setfam_1(A_4, '#skF_3')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_196, c_34])).
% 3.02/1.62  tff(c_26, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k8_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.02/1.62  tff(c_264, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_203, c_26])).
% 3.02/1.62  tff(c_416, plain, (~r1_tarski(k1_setfam_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_415, c_264])).
% 3.02/1.62  tff(c_12, plain, (![A_6, B_7]: (m1_subset_1(k8_setfam_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(k1_zfmisc_1(A_6))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.02/1.62  tff(c_420, plain, (m1_subset_1(k1_setfam_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_415, c_12])).
% 3.02/1.62  tff(c_424, plain, (m1_subset_1(k1_setfam_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_420])).
% 3.02/1.62  tff(c_432, plain, (r1_tarski(k1_setfam_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_424, c_16])).
% 3.02/1.62  tff(c_438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_416, c_432])).
% 3.02/1.62  tff(c_440, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_195])).
% 3.02/1.62  tff(c_24, plain, (![B_19, A_18]: (r1_tarski(k1_setfam_1(B_19), k1_setfam_1(A_18)) | k1_xboole_0=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.02/1.62  tff(c_493, plain, (![A_77]: (m1_subset_1(A_77, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_77, '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_166])).
% 3.02/1.62  tff(c_515, plain, (![A_81]: (r1_tarski(A_81, '#skF_2') | ~r2_hidden(A_81, '#skF_4'))), inference(resolution, [status(thm)], [c_493, c_16])).
% 3.02/1.62  tff(c_520, plain, (r1_tarski('#skF_1'('#skF_4'), '#skF_2') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4, c_515])).
% 3.02/1.62  tff(c_526, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_520])).
% 3.02/1.62  tff(c_572, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_526, c_2])).
% 3.02/1.62  tff(c_574, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_572])).
% 3.02/1.62  tff(c_576, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_520])).
% 3.02/1.62  tff(c_624, plain, (![A_92, B_93]: (k8_setfam_1(A_92, B_93)=k6_setfam_1(A_92, B_93) | k1_xboole_0=B_93 | ~m1_subset_1(B_93, k1_zfmisc_1(k1_zfmisc_1(A_92))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.02/1.62  tff(c_646, plain, (k8_setfam_1('#skF_2', '#skF_4')=k6_setfam_1('#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_30, c_624])).
% 3.02/1.62  tff(c_660, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_646])).
% 3.02/1.62  tff(c_661, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_576, c_660])).
% 3.02/1.62  tff(c_95, plain, (k6_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_79])).
% 3.02/1.62  tff(c_643, plain, (k8_setfam_1('#skF_2', '#skF_3')=k6_setfam_1('#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_32, c_624])).
% 3.02/1.62  tff(c_657, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_643])).
% 3.02/1.62  tff(c_658, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_440, c_657])).
% 3.02/1.62  tff(c_665, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k1_setfam_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_658, c_26])).
% 3.02/1.62  tff(c_694, plain, (~r1_tarski(k1_setfam_1('#skF_4'), k1_setfam_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_661, c_665])).
% 3.02/1.62  tff(c_697, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_24, c_694])).
% 3.02/1.62  tff(c_700, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_697])).
% 3.02/1.62  tff(c_702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_440, c_700])).
% 3.02/1.62  tff(c_703, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_142])).
% 3.02/1.62  tff(c_712, plain, (![A_3]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_703, c_6])).
% 3.02/1.62  tff(c_711, plain, (![A_4]: (k8_setfam_1(A_4, '#skF_3')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_703, c_34])).
% 3.02/1.62  tff(c_797, plain, (![A_105, B_106]: (m1_subset_1(k8_setfam_1(A_105, B_106), k1_zfmisc_1(A_105)) | ~m1_subset_1(B_106, k1_zfmisc_1(k1_zfmisc_1(A_105))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.02/1.62  tff(c_811, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_4))))), inference(superposition, [status(thm), theory('equality')], [c_711, c_797])).
% 3.02/1.62  tff(c_839, plain, (![A_109]: (m1_subset_1(A_109, k1_zfmisc_1(A_109)))), inference(demodulation, [status(thm), theory('equality')], [c_712, c_811])).
% 3.02/1.62  tff(c_854, plain, (![A_109]: (r1_tarski(A_109, A_109))), inference(resolution, [status(thm)], [c_839, c_16])).
% 3.02/1.62  tff(c_710, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | A_1='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_703, c_4])).
% 3.02/1.62  tff(c_722, plain, (![A_96, C_97, B_98]: (m1_subset_1(A_96, C_97) | ~m1_subset_1(B_98, k1_zfmisc_1(C_97)) | ~r2_hidden(A_96, B_98))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.02/1.62  tff(c_779, plain, (![A_103]: (m1_subset_1(A_103, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_103, '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_722])).
% 3.02/1.62  tff(c_790, plain, (![A_104]: (r1_tarski(A_104, '#skF_2') | ~r2_hidden(A_104, '#skF_4'))), inference(resolution, [status(thm)], [c_779, c_16])).
% 3.02/1.62  tff(c_795, plain, (r1_tarski('#skF_1'('#skF_4'), '#skF_2') | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_710, c_790])).
% 3.02/1.62  tff(c_796, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_795])).
% 3.02/1.62  tff(c_820, plain, (![A_4]: (k8_setfam_1(A_4, '#skF_4')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_796, c_711])).
% 3.02/1.62  tff(c_750, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_711, c_26])).
% 3.02/1.62  tff(c_856, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_820, c_750])).
% 3.02/1.62  tff(c_859, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_854, c_856])).
% 3.02/1.62  tff(c_861, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_795])).
% 3.02/1.62  tff(c_704, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_142])).
% 3.02/1.62  tff(c_862, plain, (![A_111, B_112]: (m1_subset_1(k8_setfam_1(A_111, B_112), k1_zfmisc_1(A_111)) | ~m1_subset_1(B_112, k1_zfmisc_1(k1_zfmisc_1(A_111))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.02/1.62  tff(c_876, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_4))))), inference(superposition, [status(thm), theory('equality')], [c_711, c_862])).
% 3.02/1.62  tff(c_883, plain, (![A_113]: (m1_subset_1(A_113, k1_zfmisc_1(A_113)))), inference(demodulation, [status(thm), theory('equality')], [c_712, c_876])).
% 3.02/1.62  tff(c_22, plain, (![C_17, B_16, A_15]: (~v1_xboole_0(C_17) | ~m1_subset_1(B_16, k1_zfmisc_1(C_17)) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.02/1.62  tff(c_901, plain, (![A_115, A_116]: (~v1_xboole_0(A_115) | ~r2_hidden(A_116, A_115))), inference(resolution, [status(thm)], [c_883, c_22])).
% 3.02/1.62  tff(c_906, plain, (![A_117]: (~v1_xboole_0(A_117) | A_117='#skF_3')), inference(resolution, [status(thm)], [c_710, c_901])).
% 3.02/1.62  tff(c_912, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_704, c_906])).
% 3.02/1.62  tff(c_918, plain, $false, inference(negUnitSimplification, [status(thm)], [c_861, c_912])).
% 3.02/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.62  
% 3.02/1.62  Inference rules
% 3.02/1.62  ----------------------
% 3.02/1.62  #Ref     : 0
% 3.02/1.62  #Sup     : 181
% 3.02/1.62  #Fact    : 0
% 3.02/1.62  #Define  : 0
% 3.02/1.62  #Split   : 10
% 3.02/1.62  #Chain   : 0
% 3.02/1.62  #Close   : 0
% 3.02/1.62  
% 3.02/1.62  Ordering : KBO
% 3.02/1.62  
% 3.02/1.62  Simplification rules
% 3.02/1.62  ----------------------
% 3.02/1.62  #Subsume      : 18
% 3.02/1.62  #Demod        : 101
% 3.02/1.62  #Tautology    : 62
% 3.02/1.62  #SimpNegUnit  : 9
% 3.02/1.62  #BackRed      : 53
% 3.02/1.62  
% 3.02/1.62  #Partial instantiations: 0
% 3.02/1.62  #Strategies tried      : 1
% 3.02/1.62  
% 3.02/1.62  Timing (in seconds)
% 3.02/1.62  ----------------------
% 3.02/1.62  Preprocessing        : 0.34
% 3.02/1.62  Parsing              : 0.15
% 3.02/1.62  CNF conversion       : 0.03
% 3.02/1.62  Main loop            : 0.41
% 3.02/1.62  Inferencing          : 0.15
% 3.02/1.62  Reduction            : 0.13
% 3.02/1.62  Demodulation         : 0.09
% 3.02/1.62  BG Simplification    : 0.03
% 3.02/1.62  Subsumption          : 0.06
% 3.02/1.62  Abstraction          : 0.03
% 3.02/1.62  MUC search           : 0.00
% 3.02/1.62  Cooper               : 0.00
% 3.02/1.62  Total                : 0.79
% 3.02/1.62  Index Insertion      : 0.00
% 3.02/1.62  Index Deletion       : 0.00
% 3.02/1.62  Index Matching       : 0.00
% 3.02/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
