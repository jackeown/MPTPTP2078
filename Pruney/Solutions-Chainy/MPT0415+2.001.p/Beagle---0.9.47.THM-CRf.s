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
% DateTime   : Thu Dec  3 09:57:45 EST 2020

% Result     : Theorem 12.08s
% Output     : CNFRefutation 12.23s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 315 expanded)
%              Number of leaves         :   33 ( 120 expanded)
%              Depth                    :   11
%              Number of atoms          :  198 ( 628 expanded)
%              Number of equality atoms :   55 ( 216 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_70,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_48,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_46,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_480,plain,(
    ! [A_82,B_83] :
      ( m1_subset_1(k7_setfam_1(A_82,B_83),k1_zfmisc_1(k1_zfmisc_1(A_82)))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k1_zfmisc_1(A_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_491,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_480])).

tff(c_496,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_491])).

tff(c_588,plain,(
    ! [A_84,B_85,C_86] :
      ( m1_subset_1('#skF_1'(A_84,B_85,C_86),k1_zfmisc_1(A_84))
      | k7_setfam_1(A_84,B_85) = C_86
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k1_zfmisc_1(A_84)))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(k1_zfmisc_1(A_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_40,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | ~ m1_subset_1(A_32,k1_zfmisc_1(B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4235,plain,(
    ! [A_167,B_168,C_169] :
      ( r1_tarski('#skF_1'(A_167,B_168,C_169),A_167)
      | k7_setfam_1(A_167,B_168) = C_169
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k1_zfmisc_1(A_167)))
      | ~ m1_subset_1(B_168,k1_zfmisc_1(k1_zfmisc_1(A_167))) ) ),
    inference(resolution,[status(thm)],[c_588,c_40])).

tff(c_8923,plain,(
    ! [B_250] :
      ( r1_tarski('#skF_1'('#skF_2',B_250,k1_xboole_0),'#skF_2')
      | k7_setfam_1('#skF_2',B_250) = k1_xboole_0
      | ~ m1_subset_1(B_250,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_496,c_4235])).

tff(c_8971,plain,
    ( r1_tarski('#skF_1'('#skF_2',k1_xboole_0,k1_xboole_0),'#skF_2')
    | k7_setfam_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_496,c_8923])).

tff(c_13062,plain,(
    k7_setfam_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_8971])).

tff(c_1312,plain,(
    ! [A_123,B_124,C_125] :
      ( r2_hidden('#skF_1'(A_123,B_124,C_125),C_125)
      | r2_hidden(k3_subset_1(A_123,'#skF_1'(A_123,B_124,C_125)),B_124)
      | k7_setfam_1(A_123,B_124) = C_125
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k1_zfmisc_1(A_123)))
      | ~ m1_subset_1(B_124,k1_zfmisc_1(k1_zfmisc_1(A_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_78,plain,(
    ! [A_39,B_40] : ~ r2_hidden(A_39,k2_zfmisc_1(A_39,B_40)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_81,plain,(
    ! [A_7] : ~ r2_hidden(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_78])).

tff(c_16306,plain,(
    ! [A_338,C_339] :
      ( r2_hidden('#skF_1'(A_338,k1_xboole_0,C_339),C_339)
      | k7_setfam_1(A_338,k1_xboole_0) = C_339
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k1_zfmisc_1(A_338)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_338))) ) ),
    inference(resolution,[status(thm)],[c_1312,c_81])).

tff(c_16334,plain,
    ( r2_hidden('#skF_1'('#skF_2',k1_xboole_0,'#skF_3'),'#skF_3')
    | k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3'
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_50,c_16306])).

tff(c_16354,plain,
    ( r2_hidden('#skF_1'('#skF_2',k1_xboole_0,'#skF_3'),'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_13062,c_16334])).

tff(c_16355,plain,(
    r2_hidden('#skF_1'('#skF_2',k1_xboole_0,'#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_16354])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_157,plain,(
    ! [A_56,B_57] : k1_setfam_1(k2_tarski(A_56,B_57)) = k3_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_172,plain,(
    ! [B_58,A_59] : k1_setfam_1(k2_tarski(B_58,A_59)) = k3_xboole_0(A_59,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_157])).

tff(c_38,plain,(
    ! [A_30,B_31] : k1_setfam_1(k2_tarski(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_178,plain,(
    ! [B_58,A_59] : k3_xboole_0(B_58,A_59) = k3_xboole_0(A_59,B_58) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_38])).

tff(c_331,plain,(
    ! [A_72,C_73,B_74] :
      ( m1_subset_1(A_72,C_73)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(C_73))
      | ~ r2_hidden(A_72,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_346,plain,(
    ! [A_72] :
      ( m1_subset_1(A_72,k1_zfmisc_1('#skF_2'))
      | ~ r2_hidden(A_72,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_331])).

tff(c_4272,plain,(
    ! [B_170] :
      ( r1_tarski('#skF_1'('#skF_2',B_170,'#skF_3'),'#skF_2')
      | k7_setfam_1('#skF_2',B_170) = '#skF_3'
      | ~ m1_subset_1(B_170,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_50,c_4235])).

tff(c_4312,plain,
    ( r1_tarski('#skF_1'('#skF_2',k1_xboole_0,'#skF_3'),'#skF_2')
    | k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_496,c_4272])).

tff(c_4358,plain,(
    k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4312])).

tff(c_36,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k7_setfam_1(A_28,B_29),k1_zfmisc_1(k1_zfmisc_1(A_28)))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(k1_zfmisc_1(A_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_982,plain,(
    ! [A_104,D_105,B_106] :
      ( r2_hidden(k3_subset_1(A_104,D_105),B_106)
      | ~ r2_hidden(D_105,k7_setfam_1(A_104,B_106))
      | ~ m1_subset_1(D_105,k1_zfmisc_1(A_104))
      | ~ m1_subset_1(k7_setfam_1(A_104,B_106),k1_zfmisc_1(k1_zfmisc_1(A_104)))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(k1_zfmisc_1(A_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4145,plain,(
    ! [A_164,D_165,B_166] :
      ( r2_hidden(k3_subset_1(A_164,D_165),B_166)
      | ~ r2_hidden(D_165,k7_setfam_1(A_164,B_166))
      | ~ m1_subset_1(D_165,k1_zfmisc_1(A_164))
      | ~ m1_subset_1(B_166,k1_zfmisc_1(k1_zfmisc_1(A_164))) ) ),
    inference(resolution,[status(thm)],[c_36,c_982])).

tff(c_4154,plain,(
    ! [D_165] :
      ( r2_hidden(k3_subset_1('#skF_2',D_165),k1_xboole_0)
      | ~ r2_hidden(D_165,k7_setfam_1('#skF_2',k1_xboole_0))
      | ~ m1_subset_1(D_165,k1_zfmisc_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_496,c_4145])).

tff(c_4176,plain,(
    ! [D_165] :
      ( ~ r2_hidden(D_165,k7_setfam_1('#skF_2',k1_xboole_0))
      | ~ m1_subset_1(D_165,k1_zfmisc_1('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_4154])).

tff(c_4382,plain,(
    ! [D_176] :
      ( ~ r2_hidden(D_176,'#skF_3')
      | ~ m1_subset_1(D_176,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4358,c_4176])).

tff(c_4407,plain,(
    ! [A_72] : ~ r2_hidden(A_72,'#skF_3') ),
    inference(resolution,[status(thm)],[c_346,c_4382])).

tff(c_4308,plain,
    ( r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_2')
    | k7_setfam_1('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_50,c_4272])).

tff(c_4319,plain,
    ( r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_2')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_4308])).

tff(c_4320,plain,(
    r1_tarski('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_4319])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4328,plain,(
    k3_xboole_0('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_2') = '#skF_1'('#skF_2','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_4320,c_2])).

tff(c_265,plain,(
    ! [B_68,A_69] : k3_xboole_0(B_68,A_69) = k3_xboole_0(A_69,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_38])).

tff(c_195,plain,(
    ! [A_60,B_61] : k4_xboole_0(A_60,k4_xboole_0(A_60,B_61)) = k3_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_15,B_16] : k6_subset_1(A_15,B_16) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    ! [A_13,B_14] : m1_subset_1(k6_subset_1(A_13,B_14),k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_51,plain,(
    ! [A_13,B_14] : m1_subset_1(k4_xboole_0(A_13,B_14),k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18])).

tff(c_207,plain,(
    ! [A_60,B_61] : m1_subset_1(k3_xboole_0(A_60,B_61),k1_zfmisc_1(A_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_51])).

tff(c_283,plain,(
    ! [A_69,B_68] : m1_subset_1(k3_xboole_0(A_69,B_68),k1_zfmisc_1(B_68)) ),
    inference(superposition,[status(thm),theory(equality)],[c_265,c_207])).

tff(c_4491,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4328,c_283])).

tff(c_32,plain,(
    ! [D_27,A_17,B_18] :
      ( r2_hidden(D_27,k7_setfam_1(A_17,B_18))
      | ~ r2_hidden(k3_subset_1(A_17,D_27),B_18)
      | ~ m1_subset_1(D_27,k1_zfmisc_1(A_17))
      | ~ m1_subset_1(k7_setfam_1(A_17,B_18),k1_zfmisc_1(k1_zfmisc_1(A_17)))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4653,plain,(
    ! [A_183,B_184,C_185] :
      ( r2_hidden('#skF_1'(A_183,B_184,C_185),k7_setfam_1(A_183,B_184))
      | ~ m1_subset_1('#skF_1'(A_183,B_184,C_185),k1_zfmisc_1(A_183))
      | ~ m1_subset_1(k7_setfam_1(A_183,B_184),k1_zfmisc_1(k1_zfmisc_1(A_183)))
      | r2_hidden('#skF_1'(A_183,B_184,C_185),C_185)
      | k7_setfam_1(A_183,B_184) = C_185
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k1_zfmisc_1(A_183)))
      | ~ m1_subset_1(B_184,k1_zfmisc_1(k1_zfmisc_1(A_183))) ) ),
    inference(resolution,[status(thm)],[c_1312,c_32])).

tff(c_4662,plain,(
    ! [C_185] :
      ( r2_hidden('#skF_1'('#skF_2','#skF_3',C_185),k7_setfam_1('#skF_2','#skF_3'))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3',C_185),k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | r2_hidden('#skF_1'('#skF_2','#skF_3',C_185),C_185)
      | k7_setfam_1('#skF_2','#skF_3') = C_185
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_4653])).

tff(c_4669,plain,(
    ! [C_185] :
      ( r2_hidden('#skF_1'('#skF_2','#skF_3',C_185),k1_xboole_0)
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3',C_185),k1_zfmisc_1('#skF_2'))
      | r2_hidden('#skF_1'('#skF_2','#skF_3',C_185),C_185)
      | k1_xboole_0 = C_185
      | ~ m1_subset_1(C_185,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_496,c_46,c_4662])).

tff(c_7846,plain,(
    ! [C_228] :
      ( ~ m1_subset_1('#skF_1'('#skF_2','#skF_3',C_228),k1_zfmisc_1('#skF_2'))
      | r2_hidden('#skF_1'('#skF_2','#skF_3',C_228),C_228)
      | k1_xboole_0 = C_228
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_4669])).

tff(c_7848,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_4491,c_7846])).

tff(c_7857,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_3'),'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_7848])).

tff(c_7859,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_4407,c_7857])).

tff(c_7860,plain,(
    r1_tarski('#skF_1'('#skF_2',k1_xboole_0,'#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_4312])).

tff(c_7869,plain,(
    k3_xboole_0('#skF_1'('#skF_2',k1_xboole_0,'#skF_3'),'#skF_2') = '#skF_1'('#skF_2',k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_7860,c_2])).

tff(c_8615,plain,(
    k3_xboole_0('#skF_2','#skF_1'('#skF_2',k1_xboole_0,'#skF_3')) = '#skF_1'('#skF_2',k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_7869])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_375,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(A_78,B_79) = k3_subset_1(A_78,B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_390,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_subset_1(A_13,k4_xboole_0(A_13,B_14)) ),
    inference(resolution,[status(thm)],[c_51,c_375])).

tff(c_399,plain,(
    ! [A_13,B_14] : k3_subset_1(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_390])).

tff(c_842,plain,(
    ! [D_96,A_97,B_98] :
      ( r2_hidden(D_96,k7_setfam_1(A_97,B_98))
      | ~ r2_hidden(k3_subset_1(A_97,D_96),B_98)
      | ~ m1_subset_1(D_96,k1_zfmisc_1(A_97))
      | ~ m1_subset_1(k7_setfam_1(A_97,B_98),k1_zfmisc_1(k1_zfmisc_1(A_97)))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k1_zfmisc_1(A_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_844,plain,(
    ! [A_13,B_14,B_98] :
      ( r2_hidden(k4_xboole_0(A_13,B_14),k7_setfam_1(A_13,B_98))
      | ~ r2_hidden(k3_xboole_0(A_13,B_14),B_98)
      | ~ m1_subset_1(k4_xboole_0(A_13,B_14),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(k7_setfam_1(A_13,B_98),k1_zfmisc_1(k1_zfmisc_1(A_13)))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(k1_zfmisc_1(A_13))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_842])).

tff(c_17671,plain,(
    ! [A_361,B_362,B_363] :
      ( r2_hidden(k4_xboole_0(A_361,B_362),k7_setfam_1(A_361,B_363))
      | ~ r2_hidden(k3_xboole_0(A_361,B_362),B_363)
      | ~ m1_subset_1(k7_setfam_1(A_361,B_363),k1_zfmisc_1(k1_zfmisc_1(A_361)))
      | ~ m1_subset_1(B_363,k1_zfmisc_1(k1_zfmisc_1(A_361))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_844])).

tff(c_17684,plain,(
    ! [B_362] :
      ( r2_hidden(k4_xboole_0('#skF_2',B_362),k7_setfam_1('#skF_2','#skF_3'))
      | ~ r2_hidden(k3_xboole_0('#skF_2',B_362),'#skF_3')
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_17671])).

tff(c_17695,plain,(
    ! [B_362] :
      ( r2_hidden(k4_xboole_0('#skF_2',B_362),k1_xboole_0)
      | ~ r2_hidden(k3_xboole_0('#skF_2',B_362),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_496,c_46,c_17684])).

tff(c_17697,plain,(
    ! [B_364] : ~ r2_hidden(k3_xboole_0('#skF_2',B_364),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_17695])).

tff(c_17699,plain,(
    ~ r2_hidden('#skF_1'('#skF_2',k1_xboole_0,'#skF_3'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8615,c_17697])).

tff(c_17732,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16355,c_17699])).

tff(c_17734,plain,(
    k7_setfam_1('#skF_2',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_8971])).

tff(c_20944,plain,(
    ! [A_400,C_401] :
      ( r2_hidden('#skF_1'(A_400,k1_xboole_0,C_401),C_401)
      | k7_setfam_1(A_400,k1_xboole_0) = C_401
      | ~ m1_subset_1(C_401,k1_zfmisc_1(k1_zfmisc_1(A_400)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_400))) ) ),
    inference(resolution,[status(thm)],[c_1312,c_81])).

tff(c_20960,plain,
    ( r2_hidden('#skF_1'('#skF_2',k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k7_setfam_1('#skF_2',k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_496,c_20944])).

tff(c_20994,plain,
    ( r2_hidden('#skF_1'('#skF_2',k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k7_setfam_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_20960])).

tff(c_20996,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17734,c_81,c_20994])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.08/4.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.08/4.59  
% 12.08/4.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.08/4.60  %$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 12.08/4.60  
% 12.08/4.60  %Foreground sorts:
% 12.08/4.60  
% 12.08/4.60  
% 12.08/4.60  %Background operators:
% 12.08/4.60  
% 12.08/4.60  
% 12.08/4.60  %Foreground operators:
% 12.08/4.60  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.08/4.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.08/4.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.08/4.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.08/4.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.08/4.60  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 12.08/4.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.08/4.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.08/4.60  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 12.08/4.60  tff('#skF_2', type, '#skF_2': $i).
% 12.08/4.60  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 12.08/4.60  tff('#skF_3', type, '#skF_3': $i).
% 12.08/4.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.08/4.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.08/4.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.08/4.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.08/4.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.08/4.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.08/4.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 12.08/4.60  
% 12.23/4.62  tff(f_89, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 12.23/4.62  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 12.23/4.62  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 12.23/4.62  tff(f_74, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 12.23/4.62  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 12.23/4.62  tff(f_42, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 12.23/4.62  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 12.23/4.62  tff(f_70, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 12.23/4.62  tff(f_80, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 12.23/4.62  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 12.23/4.62  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 12.23/4.62  tff(f_50, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 12.23/4.62  tff(f_48, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 12.23/4.62  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 12.23/4.62  tff(c_48, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_89])).
% 12.23/4.62  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 12.23/4.62  tff(c_46, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_89])).
% 12.23/4.62  tff(c_480, plain, (![A_82, B_83]: (m1_subset_1(k7_setfam_1(A_82, B_83), k1_zfmisc_1(k1_zfmisc_1(A_82))) | ~m1_subset_1(B_83, k1_zfmisc_1(k1_zfmisc_1(A_82))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.23/4.62  tff(c_491, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_46, c_480])).
% 12.23/4.62  tff(c_496, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_491])).
% 12.23/4.62  tff(c_588, plain, (![A_84, B_85, C_86]: (m1_subset_1('#skF_1'(A_84, B_85, C_86), k1_zfmisc_1(A_84)) | k7_setfam_1(A_84, B_85)=C_86 | ~m1_subset_1(C_86, k1_zfmisc_1(k1_zfmisc_1(A_84))) | ~m1_subset_1(B_85, k1_zfmisc_1(k1_zfmisc_1(A_84))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.23/4.62  tff(c_40, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | ~m1_subset_1(A_32, k1_zfmisc_1(B_33)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 12.23/4.62  tff(c_4235, plain, (![A_167, B_168, C_169]: (r1_tarski('#skF_1'(A_167, B_168, C_169), A_167) | k7_setfam_1(A_167, B_168)=C_169 | ~m1_subset_1(C_169, k1_zfmisc_1(k1_zfmisc_1(A_167))) | ~m1_subset_1(B_168, k1_zfmisc_1(k1_zfmisc_1(A_167))))), inference(resolution, [status(thm)], [c_588, c_40])).
% 12.23/4.62  tff(c_8923, plain, (![B_250]: (r1_tarski('#skF_1'('#skF_2', B_250, k1_xboole_0), '#skF_2') | k7_setfam_1('#skF_2', B_250)=k1_xboole_0 | ~m1_subset_1(B_250, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(resolution, [status(thm)], [c_496, c_4235])).
% 12.23/4.62  tff(c_8971, plain, (r1_tarski('#skF_1'('#skF_2', k1_xboole_0, k1_xboole_0), '#skF_2') | k7_setfam_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_496, c_8923])).
% 12.23/4.62  tff(c_13062, plain, (k7_setfam_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(splitLeft, [status(thm)], [c_8971])).
% 12.23/4.62  tff(c_1312, plain, (![A_123, B_124, C_125]: (r2_hidden('#skF_1'(A_123, B_124, C_125), C_125) | r2_hidden(k3_subset_1(A_123, '#skF_1'(A_123, B_124, C_125)), B_124) | k7_setfam_1(A_123, B_124)=C_125 | ~m1_subset_1(C_125, k1_zfmisc_1(k1_zfmisc_1(A_123))) | ~m1_subset_1(B_124, k1_zfmisc_1(k1_zfmisc_1(A_123))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.23/4.62  tff(c_10, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.23/4.62  tff(c_78, plain, (![A_39, B_40]: (~r2_hidden(A_39, k2_zfmisc_1(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 12.23/4.62  tff(c_81, plain, (![A_7]: (~r2_hidden(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_78])).
% 12.23/4.62  tff(c_16306, plain, (![A_338, C_339]: (r2_hidden('#skF_1'(A_338, k1_xboole_0, C_339), C_339) | k7_setfam_1(A_338, k1_xboole_0)=C_339 | ~m1_subset_1(C_339, k1_zfmisc_1(k1_zfmisc_1(A_338))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_338))))), inference(resolution, [status(thm)], [c_1312, c_81])).
% 12.23/4.62  tff(c_16334, plain, (r2_hidden('#skF_1'('#skF_2', k1_xboole_0, '#skF_3'), '#skF_3') | k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3' | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_50, c_16306])).
% 12.23/4.62  tff(c_16354, plain, (r2_hidden('#skF_1'('#skF_2', k1_xboole_0, '#skF_3'), '#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_496, c_13062, c_16334])).
% 12.23/4.62  tff(c_16355, plain, (r2_hidden('#skF_1'('#skF_2', k1_xboole_0, '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_48, c_16354])).
% 12.23/4.62  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.23/4.62  tff(c_157, plain, (![A_56, B_57]: (k1_setfam_1(k2_tarski(A_56, B_57))=k3_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_70])).
% 12.23/4.62  tff(c_172, plain, (![B_58, A_59]: (k1_setfam_1(k2_tarski(B_58, A_59))=k3_xboole_0(A_59, B_58))), inference(superposition, [status(thm), theory('equality')], [c_6, c_157])).
% 12.23/4.62  tff(c_38, plain, (![A_30, B_31]: (k1_setfam_1(k2_tarski(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_70])).
% 12.23/4.62  tff(c_178, plain, (![B_58, A_59]: (k3_xboole_0(B_58, A_59)=k3_xboole_0(A_59, B_58))), inference(superposition, [status(thm), theory('equality')], [c_172, c_38])).
% 12.23/4.62  tff(c_331, plain, (![A_72, C_73, B_74]: (m1_subset_1(A_72, C_73) | ~m1_subset_1(B_74, k1_zfmisc_1(C_73)) | ~r2_hidden(A_72, B_74))), inference(cnfTransformation, [status(thm)], [f_80])).
% 12.23/4.62  tff(c_346, plain, (![A_72]: (m1_subset_1(A_72, k1_zfmisc_1('#skF_2')) | ~r2_hidden(A_72, '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_331])).
% 12.23/4.62  tff(c_4272, plain, (![B_170]: (r1_tarski('#skF_1'('#skF_2', B_170, '#skF_3'), '#skF_2') | k7_setfam_1('#skF_2', B_170)='#skF_3' | ~m1_subset_1(B_170, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(resolution, [status(thm)], [c_50, c_4235])).
% 12.23/4.62  tff(c_4312, plain, (r1_tarski('#skF_1'('#skF_2', k1_xboole_0, '#skF_3'), '#skF_2') | k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3'), inference(resolution, [status(thm)], [c_496, c_4272])).
% 12.23/4.62  tff(c_4358, plain, (k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3'), inference(splitLeft, [status(thm)], [c_4312])).
% 12.23/4.62  tff(c_36, plain, (![A_28, B_29]: (m1_subset_1(k7_setfam_1(A_28, B_29), k1_zfmisc_1(k1_zfmisc_1(A_28))) | ~m1_subset_1(B_29, k1_zfmisc_1(k1_zfmisc_1(A_28))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 12.23/4.62  tff(c_982, plain, (![A_104, D_105, B_106]: (r2_hidden(k3_subset_1(A_104, D_105), B_106) | ~r2_hidden(D_105, k7_setfam_1(A_104, B_106)) | ~m1_subset_1(D_105, k1_zfmisc_1(A_104)) | ~m1_subset_1(k7_setfam_1(A_104, B_106), k1_zfmisc_1(k1_zfmisc_1(A_104))) | ~m1_subset_1(B_106, k1_zfmisc_1(k1_zfmisc_1(A_104))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.23/4.62  tff(c_4145, plain, (![A_164, D_165, B_166]: (r2_hidden(k3_subset_1(A_164, D_165), B_166) | ~r2_hidden(D_165, k7_setfam_1(A_164, B_166)) | ~m1_subset_1(D_165, k1_zfmisc_1(A_164)) | ~m1_subset_1(B_166, k1_zfmisc_1(k1_zfmisc_1(A_164))))), inference(resolution, [status(thm)], [c_36, c_982])).
% 12.23/4.62  tff(c_4154, plain, (![D_165]: (r2_hidden(k3_subset_1('#skF_2', D_165), k1_xboole_0) | ~r2_hidden(D_165, k7_setfam_1('#skF_2', k1_xboole_0)) | ~m1_subset_1(D_165, k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_496, c_4145])).
% 12.23/4.62  tff(c_4176, plain, (![D_165]: (~r2_hidden(D_165, k7_setfam_1('#skF_2', k1_xboole_0)) | ~m1_subset_1(D_165, k1_zfmisc_1('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_81, c_4154])).
% 12.23/4.62  tff(c_4382, plain, (![D_176]: (~r2_hidden(D_176, '#skF_3') | ~m1_subset_1(D_176, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4358, c_4176])).
% 12.23/4.62  tff(c_4407, plain, (![A_72]: (~r2_hidden(A_72, '#skF_3'))), inference(resolution, [status(thm)], [c_346, c_4382])).
% 12.23/4.62  tff(c_4308, plain, (r1_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_2') | k7_setfam_1('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_50, c_4272])).
% 12.23/4.62  tff(c_4319, plain, (r1_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_2') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_4308])).
% 12.23/4.62  tff(c_4320, plain, (r1_tarski('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_48, c_4319])).
% 12.23/4.62  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.23/4.62  tff(c_4328, plain, (k3_xboole_0('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_2')='#skF_1'('#skF_2', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_4320, c_2])).
% 12.23/4.62  tff(c_265, plain, (![B_68, A_69]: (k3_xboole_0(B_68, A_69)=k3_xboole_0(A_69, B_68))), inference(superposition, [status(thm), theory('equality')], [c_172, c_38])).
% 12.23/4.62  tff(c_195, plain, (![A_60, B_61]: (k4_xboole_0(A_60, k4_xboole_0(A_60, B_61))=k3_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.23/4.62  tff(c_20, plain, (![A_15, B_16]: (k6_subset_1(A_15, B_16)=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 12.23/4.62  tff(c_18, plain, (![A_13, B_14]: (m1_subset_1(k6_subset_1(A_13, B_14), k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.23/4.62  tff(c_51, plain, (![A_13, B_14]: (m1_subset_1(k4_xboole_0(A_13, B_14), k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18])).
% 12.23/4.62  tff(c_207, plain, (![A_60, B_61]: (m1_subset_1(k3_xboole_0(A_60, B_61), k1_zfmisc_1(A_60)))), inference(superposition, [status(thm), theory('equality')], [c_195, c_51])).
% 12.23/4.62  tff(c_283, plain, (![A_69, B_68]: (m1_subset_1(k3_xboole_0(A_69, B_68), k1_zfmisc_1(B_68)))), inference(superposition, [status(thm), theory('equality')], [c_265, c_207])).
% 12.23/4.62  tff(c_4491, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_3'), k1_zfmisc_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_4328, c_283])).
% 12.23/4.62  tff(c_32, plain, (![D_27, A_17, B_18]: (r2_hidden(D_27, k7_setfam_1(A_17, B_18)) | ~r2_hidden(k3_subset_1(A_17, D_27), B_18) | ~m1_subset_1(D_27, k1_zfmisc_1(A_17)) | ~m1_subset_1(k7_setfam_1(A_17, B_18), k1_zfmisc_1(k1_zfmisc_1(A_17))) | ~m1_subset_1(B_18, k1_zfmisc_1(k1_zfmisc_1(A_17))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.23/4.62  tff(c_4653, plain, (![A_183, B_184, C_185]: (r2_hidden('#skF_1'(A_183, B_184, C_185), k7_setfam_1(A_183, B_184)) | ~m1_subset_1('#skF_1'(A_183, B_184, C_185), k1_zfmisc_1(A_183)) | ~m1_subset_1(k7_setfam_1(A_183, B_184), k1_zfmisc_1(k1_zfmisc_1(A_183))) | r2_hidden('#skF_1'(A_183, B_184, C_185), C_185) | k7_setfam_1(A_183, B_184)=C_185 | ~m1_subset_1(C_185, k1_zfmisc_1(k1_zfmisc_1(A_183))) | ~m1_subset_1(B_184, k1_zfmisc_1(k1_zfmisc_1(A_183))))), inference(resolution, [status(thm)], [c_1312, c_32])).
% 12.23/4.62  tff(c_4662, plain, (![C_185]: (r2_hidden('#skF_1'('#skF_2', '#skF_3', C_185), k7_setfam_1('#skF_2', '#skF_3')) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', C_185), k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | r2_hidden('#skF_1'('#skF_2', '#skF_3', C_185), C_185) | k7_setfam_1('#skF_2', '#skF_3')=C_185 | ~m1_subset_1(C_185, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_46, c_4653])).
% 12.23/4.62  tff(c_4669, plain, (![C_185]: (r2_hidden('#skF_1'('#skF_2', '#skF_3', C_185), k1_xboole_0) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', C_185), k1_zfmisc_1('#skF_2')) | r2_hidden('#skF_1'('#skF_2', '#skF_3', C_185), C_185) | k1_xboole_0=C_185 | ~m1_subset_1(C_185, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_496, c_46, c_4662])).
% 12.23/4.62  tff(c_7846, plain, (![C_228]: (~m1_subset_1('#skF_1'('#skF_2', '#skF_3', C_228), k1_zfmisc_1('#skF_2')) | r2_hidden('#skF_1'('#skF_2', '#skF_3', C_228), C_228) | k1_xboole_0=C_228 | ~m1_subset_1(C_228, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_81, c_4669])).
% 12.23/4.62  tff(c_7848, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3') | k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_4491, c_7846])).
% 12.23/4.62  tff(c_7857, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_3'), '#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_7848])).
% 12.23/4.62  tff(c_7859, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_4407, c_7857])).
% 12.23/4.62  tff(c_7860, plain, (r1_tarski('#skF_1'('#skF_2', k1_xboole_0, '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_4312])).
% 12.23/4.62  tff(c_7869, plain, (k3_xboole_0('#skF_1'('#skF_2', k1_xboole_0, '#skF_3'), '#skF_2')='#skF_1'('#skF_2', k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_7860, c_2])).
% 12.23/4.62  tff(c_8615, plain, (k3_xboole_0('#skF_2', '#skF_1'('#skF_2', k1_xboole_0, '#skF_3'))='#skF_1'('#skF_2', k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_178, c_7869])).
% 12.23/4.62  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.23/4.62  tff(c_375, plain, (![A_78, B_79]: (k4_xboole_0(A_78, B_79)=k3_subset_1(A_78, B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 12.23/4.62  tff(c_390, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_subset_1(A_13, k4_xboole_0(A_13, B_14)))), inference(resolution, [status(thm)], [c_51, c_375])).
% 12.23/4.62  tff(c_399, plain, (![A_13, B_14]: (k3_subset_1(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_390])).
% 12.23/4.62  tff(c_842, plain, (![D_96, A_97, B_98]: (r2_hidden(D_96, k7_setfam_1(A_97, B_98)) | ~r2_hidden(k3_subset_1(A_97, D_96), B_98) | ~m1_subset_1(D_96, k1_zfmisc_1(A_97)) | ~m1_subset_1(k7_setfam_1(A_97, B_98), k1_zfmisc_1(k1_zfmisc_1(A_97))) | ~m1_subset_1(B_98, k1_zfmisc_1(k1_zfmisc_1(A_97))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.23/4.62  tff(c_844, plain, (![A_13, B_14, B_98]: (r2_hidden(k4_xboole_0(A_13, B_14), k7_setfam_1(A_13, B_98)) | ~r2_hidden(k3_xboole_0(A_13, B_14), B_98) | ~m1_subset_1(k4_xboole_0(A_13, B_14), k1_zfmisc_1(A_13)) | ~m1_subset_1(k7_setfam_1(A_13, B_98), k1_zfmisc_1(k1_zfmisc_1(A_13))) | ~m1_subset_1(B_98, k1_zfmisc_1(k1_zfmisc_1(A_13))))), inference(superposition, [status(thm), theory('equality')], [c_399, c_842])).
% 12.23/4.62  tff(c_17671, plain, (![A_361, B_362, B_363]: (r2_hidden(k4_xboole_0(A_361, B_362), k7_setfam_1(A_361, B_363)) | ~r2_hidden(k3_xboole_0(A_361, B_362), B_363) | ~m1_subset_1(k7_setfam_1(A_361, B_363), k1_zfmisc_1(k1_zfmisc_1(A_361))) | ~m1_subset_1(B_363, k1_zfmisc_1(k1_zfmisc_1(A_361))))), inference(demodulation, [status(thm), theory('equality')], [c_51, c_844])).
% 12.23/4.62  tff(c_17684, plain, (![B_362]: (r2_hidden(k4_xboole_0('#skF_2', B_362), k7_setfam_1('#skF_2', '#skF_3')) | ~r2_hidden(k3_xboole_0('#skF_2', B_362), '#skF_3') | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_46, c_17671])).
% 12.23/4.62  tff(c_17695, plain, (![B_362]: (r2_hidden(k4_xboole_0('#skF_2', B_362), k1_xboole_0) | ~r2_hidden(k3_xboole_0('#skF_2', B_362), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_496, c_46, c_17684])).
% 12.23/4.62  tff(c_17697, plain, (![B_364]: (~r2_hidden(k3_xboole_0('#skF_2', B_364), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_81, c_17695])).
% 12.23/4.62  tff(c_17699, plain, (~r2_hidden('#skF_1'('#skF_2', k1_xboole_0, '#skF_3'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8615, c_17697])).
% 12.23/4.62  tff(c_17732, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16355, c_17699])).
% 12.23/4.62  tff(c_17734, plain, (k7_setfam_1('#skF_2', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_8971])).
% 12.23/4.62  tff(c_20944, plain, (![A_400, C_401]: (r2_hidden('#skF_1'(A_400, k1_xboole_0, C_401), C_401) | k7_setfam_1(A_400, k1_xboole_0)=C_401 | ~m1_subset_1(C_401, k1_zfmisc_1(k1_zfmisc_1(A_400))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_400))))), inference(resolution, [status(thm)], [c_1312, c_81])).
% 12.23/4.62  tff(c_20960, plain, (r2_hidden('#skF_1'('#skF_2', k1_xboole_0, k1_xboole_0), k1_xboole_0) | k7_setfam_1('#skF_2', k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_496, c_20944])).
% 12.23/4.62  tff(c_20994, plain, (r2_hidden('#skF_1'('#skF_2', k1_xboole_0, k1_xboole_0), k1_xboole_0) | k7_setfam_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_496, c_20960])).
% 12.23/4.62  tff(c_20996, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17734, c_81, c_20994])).
% 12.23/4.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.23/4.62  
% 12.23/4.62  Inference rules
% 12.23/4.62  ----------------------
% 12.23/4.62  #Ref     : 0
% 12.23/4.62  #Sup     : 5190
% 12.23/4.62  #Fact    : 0
% 12.23/4.62  #Define  : 0
% 12.23/4.62  #Split   : 14
% 12.23/4.62  #Chain   : 0
% 12.23/4.62  #Close   : 0
% 12.23/4.62  
% 12.23/4.62  Ordering : KBO
% 12.23/4.62  
% 12.23/4.62  Simplification rules
% 12.23/4.62  ----------------------
% 12.23/4.62  #Subsume      : 547
% 12.23/4.62  #Demod        : 6087
% 12.23/4.62  #Tautology    : 2780
% 12.23/4.62  #SimpNegUnit  : 70
% 12.23/4.62  #BackRed      : 30
% 12.23/4.62  
% 12.23/4.62  #Partial instantiations: 0
% 12.23/4.62  #Strategies tried      : 1
% 12.23/4.62  
% 12.23/4.62  Timing (in seconds)
% 12.23/4.62  ----------------------
% 12.23/4.62  Preprocessing        : 0.33
% 12.23/4.62  Parsing              : 0.17
% 12.23/4.62  CNF conversion       : 0.02
% 12.23/4.62  Main loop            : 3.51
% 12.23/4.62  Inferencing          : 0.77
% 12.23/4.62  Reduction            : 1.82
% 12.23/4.62  Demodulation         : 1.53
% 12.23/4.62  BG Simplification    : 0.09
% 12.23/4.62  Subsumption          : 0.63
% 12.23/4.62  Abstraction          : 0.14
% 12.23/4.62  MUC search           : 0.00
% 12.23/4.62  Cooper               : 0.00
% 12.23/4.62  Total                : 3.89
% 12.23/4.62  Index Insertion      : 0.00
% 12.23/4.62  Index Deletion       : 0.00
% 12.23/4.62  Index Matching       : 0.00
% 12.23/4.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
