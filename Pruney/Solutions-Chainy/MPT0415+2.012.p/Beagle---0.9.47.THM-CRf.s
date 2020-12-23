%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:47 EST 2020

% Result     : Theorem 10.19s
% Output     : CNFRefutation 10.19s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 219 expanded)
%              Number of leaves         :   24 (  84 expanded)
%              Depth                    :   11
%              Number of atoms          :  122 ( 431 expanded)
%              Number of equality atoms :   44 ( 167 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k7_setfam_1 > k6_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_32,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_44,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_38,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_64,plain,(
    ! [B_33,A_34] :
      ( ~ r2_hidden(B_33,A_34)
      | k4_xboole_0(A_34,k1_tarski(B_33)) != A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_69,plain,(
    ! [B_33] : ~ r2_hidden(B_33,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_64])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_34,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_309,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1(k7_setfam_1(A_60,B_61),k1_zfmisc_1(k1_zfmisc_1(A_60)))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_319,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_309])).

tff(c_324,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_319])).

tff(c_438,plain,(
    ! [A_66,B_67,C_68] :
      ( m1_subset_1('#skF_1'(A_66,B_67,C_68),k1_zfmisc_1(A_66))
      | k7_setfam_1(A_66,B_67) = C_68
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k1_zfmisc_1(A_66)))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1(A_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = k3_subset_1(A_4,B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3153,plain,(
    ! [A_153,B_154,C_155] :
      ( k4_xboole_0(A_153,'#skF_1'(A_153,B_154,C_155)) = k3_subset_1(A_153,'#skF_1'(A_153,B_154,C_155))
      | k7_setfam_1(A_153,B_154) = C_155
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k1_zfmisc_1(A_153)))
      | ~ m1_subset_1(B_154,k1_zfmisc_1(k1_zfmisc_1(A_153))) ) ),
    inference(resolution,[status(thm)],[c_438,c_8])).

tff(c_3300,plain,(
    ! [B_157] :
      ( k4_xboole_0('#skF_2','#skF_1'('#skF_2',B_157,'#skF_3')) = k3_subset_1('#skF_2','#skF_1'('#skF_2',B_157,'#skF_3'))
      | k7_setfam_1('#skF_2',B_157) = '#skF_3'
      | ~ m1_subset_1(B_157,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_3153])).

tff(c_3377,plain,
    ( k4_xboole_0('#skF_2','#skF_1'('#skF_2',k1_xboole_0,'#skF_3')) = k3_subset_1('#skF_2','#skF_1'('#skF_2',k1_xboole_0,'#skF_3'))
    | k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_324,c_3300])).

tff(c_5580,plain,(
    k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3377])).

tff(c_1046,plain,(
    ! [A_94,B_95,C_96] :
      ( r2_hidden('#skF_1'(A_94,B_95,C_96),C_96)
      | r2_hidden(k3_subset_1(A_94,'#skF_1'(A_94,B_95,C_96)),B_95)
      | k7_setfam_1(A_94,B_95) = C_96
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k1_zfmisc_1(A_94)))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(k1_zfmisc_1(A_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_7195,plain,(
    ! [A_219,C_220] :
      ( r2_hidden('#skF_1'(A_219,k1_xboole_0,C_220),C_220)
      | k7_setfam_1(A_219,k1_xboole_0) = C_220
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k1_zfmisc_1(A_219)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_219))) ) ),
    inference(resolution,[status(thm)],[c_1046,c_69])).

tff(c_7232,plain,
    ( r2_hidden('#skF_1'('#skF_2',k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k7_setfam_1('#skF_2',k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_324,c_7195])).

tff(c_7269,plain,
    ( r2_hidden('#skF_1'('#skF_2',k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_5580,c_7232])).

tff(c_7271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_69,c_7269])).

tff(c_7273,plain,(
    k7_setfam_1('#skF_2',k1_xboole_0) != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3377])).

tff(c_9744,plain,(
    ! [A_252,C_253] :
      ( r2_hidden('#skF_1'(A_252,k1_xboole_0,C_253),C_253)
      | k7_setfam_1(A_252,k1_xboole_0) = C_253
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k1_zfmisc_1(A_252)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_252))) ) ),
    inference(resolution,[status(thm)],[c_1046,c_69])).

tff(c_9806,plain,
    ( r2_hidden('#skF_1'('#skF_2',k1_xboole_0,'#skF_3'),'#skF_3')
    | k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3'
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_38,c_9744])).

tff(c_9848,plain,
    ( r2_hidden('#skF_1'('#skF_2',k1_xboole_0,'#skF_3'),'#skF_3')
    | k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_9806])).

tff(c_9849,plain,(
    r2_hidden('#skF_1'('#skF_2',k1_xboole_0,'#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_7273,c_9848])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k3_subset_1(A_8,k3_subset_1(A_8,B_9)) = B_9
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_3491,plain,(
    ! [A_159,B_160,C_161] :
      ( k3_subset_1(A_159,k3_subset_1(A_159,'#skF_1'(A_159,B_160,C_161))) = '#skF_1'(A_159,B_160,C_161)
      | k7_setfam_1(A_159,B_160) = C_161
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k1_zfmisc_1(A_159)))
      | ~ m1_subset_1(B_160,k1_zfmisc_1(k1_zfmisc_1(A_159))) ) ),
    inference(resolution,[status(thm)],[c_438,c_12])).

tff(c_3976,plain,(
    ! [B_166] :
      ( k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_1'('#skF_2',B_166,'#skF_3'))) = '#skF_1'('#skF_2',B_166,'#skF_3')
      | k7_setfam_1('#skF_2',B_166) = '#skF_3'
      | ~ m1_subset_1(B_166,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_38,c_3491])).

tff(c_4049,plain,
    ( k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_1'('#skF_2',k1_xboole_0,'#skF_3'))) = '#skF_1'('#skF_2',k1_xboole_0,'#skF_3')
    | k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_324,c_3976])).

tff(c_7323,plain,(
    k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_1'('#skF_2',k1_xboole_0,'#skF_3'))) = '#skF_1'('#skF_2',k1_xboole_0,'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_7273,c_4049])).

tff(c_7272,plain,(
    k4_xboole_0('#skF_2','#skF_1'('#skF_2',k1_xboole_0,'#skF_3')) = k3_subset_1('#skF_2','#skF_1'('#skF_2',k1_xboole_0,'#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3377])).

tff(c_14,plain,(
    ! [A_10,B_11] : k6_subset_1(A_10,B_11) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    ! [A_6,B_7] : m1_subset_1(k6_subset_1(A_6,B_7),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_39,plain,(
    ! [A_6,B_7] : m1_subset_1(k4_xboole_0(A_6,B_7),k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_10])).

tff(c_106,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = k3_subset_1(A_40,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_122,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k4_xboole_0(A_6,B_7)) = k3_subset_1(A_6,k4_xboole_0(A_6,B_7)) ),
    inference(resolution,[status(thm)],[c_39,c_106])).

tff(c_495,plain,(
    ! [A_71,B_72] : k4_xboole_0(A_71,k4_xboole_0(A_71,B_72)) = k3_subset_1(A_71,k4_xboole_0(A_71,B_72)) ),
    inference(resolution,[status(thm)],[c_39,c_106])).

tff(c_510,plain,(
    ! [A_71,B_72] : m1_subset_1(k3_subset_1(A_71,k4_xboole_0(A_71,B_72)),k1_zfmisc_1(A_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_495,c_39])).

tff(c_139,plain,(
    ! [A_42,B_43] :
      ( k3_subset_1(A_42,k3_subset_1(A_42,B_43)) = B_43
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_154,plain,(
    ! [A_6,B_7] : k3_subset_1(A_6,k3_subset_1(A_6,k4_xboole_0(A_6,B_7))) = k4_xboole_0(A_6,B_7) ),
    inference(resolution,[status(thm)],[c_39,c_139])).

tff(c_767,plain,(
    ! [D_81,A_82,B_83] :
      ( r2_hidden(D_81,k7_setfam_1(A_82,B_83))
      | ~ r2_hidden(k3_subset_1(A_82,D_81),B_83)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(A_82))
      | ~ m1_subset_1(k7_setfam_1(A_82,B_83),k1_zfmisc_1(k1_zfmisc_1(A_82)))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k1_zfmisc_1(A_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_769,plain,(
    ! [A_6,B_7,B_83] :
      ( r2_hidden(k3_subset_1(A_6,k4_xboole_0(A_6,B_7)),k7_setfam_1(A_6,B_83))
      | ~ r2_hidden(k4_xboole_0(A_6,B_7),B_83)
      | ~ m1_subset_1(k3_subset_1(A_6,k4_xboole_0(A_6,B_7)),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(k7_setfam_1(A_6,B_83),k1_zfmisc_1(k1_zfmisc_1(A_6)))
      | ~ m1_subset_1(B_83,k1_zfmisc_1(k1_zfmisc_1(A_6))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_767])).

tff(c_15239,plain,(
    ! [A_328,B_329,B_330] :
      ( r2_hidden(k3_subset_1(A_328,k4_xboole_0(A_328,B_329)),k7_setfam_1(A_328,B_330))
      | ~ r2_hidden(k4_xboole_0(A_328,B_329),B_330)
      | ~ m1_subset_1(k7_setfam_1(A_328,B_330),k1_zfmisc_1(k1_zfmisc_1(A_328)))
      | ~ m1_subset_1(B_330,k1_zfmisc_1(k1_zfmisc_1(A_328))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_769])).

tff(c_15372,plain,(
    ! [B_329] :
      ( r2_hidden(k3_subset_1('#skF_2',k4_xboole_0('#skF_2',B_329)),k1_xboole_0)
      | ~ r2_hidden(k4_xboole_0('#skF_2',B_329),'#skF_3')
      | ~ m1_subset_1(k7_setfam_1('#skF_2','#skF_3'),k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_15239])).

tff(c_15408,plain,(
    ! [B_329] :
      ( r2_hidden(k3_subset_1('#skF_2',k4_xboole_0('#skF_2',B_329)),k1_xboole_0)
      | ~ r2_hidden(k4_xboole_0('#skF_2',B_329),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_324,c_34,c_15372])).

tff(c_15411,plain,(
    ! [B_331] : ~ r2_hidden(k4_xboole_0('#skF_2',B_331),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_15408])).

tff(c_15677,plain,(
    ! [B_332] : ~ r2_hidden(k3_subset_1('#skF_2',k4_xboole_0('#skF_2',B_332)),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_15411])).

tff(c_15712,plain,(
    ~ r2_hidden(k3_subset_1('#skF_2',k3_subset_1('#skF_2','#skF_1'('#skF_2',k1_xboole_0,'#skF_3'))),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_7272,c_15677])).

tff(c_15841,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9849,c_7323,c_15712])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.19/3.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.19/3.65  
% 10.19/3.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.19/3.66  %$ r2_hidden > m1_subset_1 > k7_setfam_1 > k6_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 10.19/3.66  
% 10.19/3.66  %Foreground sorts:
% 10.19/3.66  
% 10.19/3.66  
% 10.19/3.66  %Background operators:
% 10.19/3.66  
% 10.19/3.66  
% 10.19/3.66  %Foreground operators:
% 10.19/3.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.19/3.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.19/3.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.19/3.66  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.19/3.66  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.19/3.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.19/3.66  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 10.19/3.66  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.19/3.66  tff('#skF_2', type, '#skF_2': $i).
% 10.19/3.66  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 10.19/3.66  tff('#skF_3', type, '#skF_3': $i).
% 10.19/3.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.19/3.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.19/3.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.19/3.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.19/3.66  
% 10.19/3.67  tff(f_77, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 10.19/3.67  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 10.19/3.67  tff(f_32, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 10.19/3.67  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 10.19/3.67  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_setfam_1)).
% 10.19/3.67  tff(f_36, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 10.19/3.67  tff(f_42, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 10.19/3.67  tff(f_44, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 10.19/3.67  tff(f_38, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 10.19/3.67  tff(c_36, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.19/3.67  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.19/3.67  tff(c_64, plain, (![B_33, A_34]: (~r2_hidden(B_33, A_34) | k4_xboole_0(A_34, k1_tarski(B_33))!=A_34)), inference(cnfTransformation, [status(thm)], [f_32])).
% 10.19/3.67  tff(c_69, plain, (![B_33]: (~r2_hidden(B_33, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_64])).
% 10.19/3.67  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.19/3.67  tff(c_34, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 10.19/3.67  tff(c_309, plain, (![A_60, B_61]: (m1_subset_1(k7_setfam_1(A_60, B_61), k1_zfmisc_1(k1_zfmisc_1(A_60))) | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(A_60))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 10.19/3.67  tff(c_319, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_34, c_309])).
% 10.19/3.67  tff(c_324, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_319])).
% 10.19/3.67  tff(c_438, plain, (![A_66, B_67, C_68]: (m1_subset_1('#skF_1'(A_66, B_67, C_68), k1_zfmisc_1(A_66)) | k7_setfam_1(A_66, B_67)=C_68 | ~m1_subset_1(C_68, k1_zfmisc_1(k1_zfmisc_1(A_66))) | ~m1_subset_1(B_67, k1_zfmisc_1(k1_zfmisc_1(A_66))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.19/3.67  tff(c_8, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)=k3_subset_1(A_4, B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.19/3.67  tff(c_3153, plain, (![A_153, B_154, C_155]: (k4_xboole_0(A_153, '#skF_1'(A_153, B_154, C_155))=k3_subset_1(A_153, '#skF_1'(A_153, B_154, C_155)) | k7_setfam_1(A_153, B_154)=C_155 | ~m1_subset_1(C_155, k1_zfmisc_1(k1_zfmisc_1(A_153))) | ~m1_subset_1(B_154, k1_zfmisc_1(k1_zfmisc_1(A_153))))), inference(resolution, [status(thm)], [c_438, c_8])).
% 10.19/3.67  tff(c_3300, plain, (![B_157]: (k4_xboole_0('#skF_2', '#skF_1'('#skF_2', B_157, '#skF_3'))=k3_subset_1('#skF_2', '#skF_1'('#skF_2', B_157, '#skF_3')) | k7_setfam_1('#skF_2', B_157)='#skF_3' | ~m1_subset_1(B_157, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(resolution, [status(thm)], [c_38, c_3153])).
% 10.19/3.67  tff(c_3377, plain, (k4_xboole_0('#skF_2', '#skF_1'('#skF_2', k1_xboole_0, '#skF_3'))=k3_subset_1('#skF_2', '#skF_1'('#skF_2', k1_xboole_0, '#skF_3')) | k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3'), inference(resolution, [status(thm)], [c_324, c_3300])).
% 10.19/3.67  tff(c_5580, plain, (k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3'), inference(splitLeft, [status(thm)], [c_3377])).
% 10.19/3.67  tff(c_1046, plain, (![A_94, B_95, C_96]: (r2_hidden('#skF_1'(A_94, B_95, C_96), C_96) | r2_hidden(k3_subset_1(A_94, '#skF_1'(A_94, B_95, C_96)), B_95) | k7_setfam_1(A_94, B_95)=C_96 | ~m1_subset_1(C_96, k1_zfmisc_1(k1_zfmisc_1(A_94))) | ~m1_subset_1(B_95, k1_zfmisc_1(k1_zfmisc_1(A_94))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.19/3.67  tff(c_7195, plain, (![A_219, C_220]: (r2_hidden('#skF_1'(A_219, k1_xboole_0, C_220), C_220) | k7_setfam_1(A_219, k1_xboole_0)=C_220 | ~m1_subset_1(C_220, k1_zfmisc_1(k1_zfmisc_1(A_219))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_219))))), inference(resolution, [status(thm)], [c_1046, c_69])).
% 10.19/3.67  tff(c_7232, plain, (r2_hidden('#skF_1'('#skF_2', k1_xboole_0, k1_xboole_0), k1_xboole_0) | k7_setfam_1('#skF_2', k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_324, c_7195])).
% 10.19/3.67  tff(c_7269, plain, (r2_hidden('#skF_1'('#skF_2', k1_xboole_0, k1_xboole_0), k1_xboole_0) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_324, c_5580, c_7232])).
% 10.19/3.67  tff(c_7271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_69, c_7269])).
% 10.19/3.67  tff(c_7273, plain, (k7_setfam_1('#skF_2', k1_xboole_0)!='#skF_3'), inference(splitRight, [status(thm)], [c_3377])).
% 10.19/3.67  tff(c_9744, plain, (![A_252, C_253]: (r2_hidden('#skF_1'(A_252, k1_xboole_0, C_253), C_253) | k7_setfam_1(A_252, k1_xboole_0)=C_253 | ~m1_subset_1(C_253, k1_zfmisc_1(k1_zfmisc_1(A_252))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_252))))), inference(resolution, [status(thm)], [c_1046, c_69])).
% 10.19/3.67  tff(c_9806, plain, (r2_hidden('#skF_1'('#skF_2', k1_xboole_0, '#skF_3'), '#skF_3') | k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3' | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_38, c_9744])).
% 10.19/3.67  tff(c_9848, plain, (r2_hidden('#skF_1'('#skF_2', k1_xboole_0, '#skF_3'), '#skF_3') | k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_324, c_9806])).
% 10.19/3.67  tff(c_9849, plain, (r2_hidden('#skF_1'('#skF_2', k1_xboole_0, '#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_7273, c_9848])).
% 10.19/3.67  tff(c_12, plain, (![A_8, B_9]: (k3_subset_1(A_8, k3_subset_1(A_8, B_9))=B_9 | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.19/3.67  tff(c_3491, plain, (![A_159, B_160, C_161]: (k3_subset_1(A_159, k3_subset_1(A_159, '#skF_1'(A_159, B_160, C_161)))='#skF_1'(A_159, B_160, C_161) | k7_setfam_1(A_159, B_160)=C_161 | ~m1_subset_1(C_161, k1_zfmisc_1(k1_zfmisc_1(A_159))) | ~m1_subset_1(B_160, k1_zfmisc_1(k1_zfmisc_1(A_159))))), inference(resolution, [status(thm)], [c_438, c_12])).
% 10.19/3.67  tff(c_3976, plain, (![B_166]: (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_1'('#skF_2', B_166, '#skF_3')))='#skF_1'('#skF_2', B_166, '#skF_3') | k7_setfam_1('#skF_2', B_166)='#skF_3' | ~m1_subset_1(B_166, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(resolution, [status(thm)], [c_38, c_3491])).
% 10.19/3.67  tff(c_4049, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_1'('#skF_2', k1_xboole_0, '#skF_3')))='#skF_1'('#skF_2', k1_xboole_0, '#skF_3') | k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3'), inference(resolution, [status(thm)], [c_324, c_3976])).
% 10.19/3.67  tff(c_7323, plain, (k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_1'('#skF_2', k1_xboole_0, '#skF_3')))='#skF_1'('#skF_2', k1_xboole_0, '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_7273, c_4049])).
% 10.19/3.67  tff(c_7272, plain, (k4_xboole_0('#skF_2', '#skF_1'('#skF_2', k1_xboole_0, '#skF_3'))=k3_subset_1('#skF_2', '#skF_1'('#skF_2', k1_xboole_0, '#skF_3'))), inference(splitRight, [status(thm)], [c_3377])).
% 10.19/3.67  tff(c_14, plain, (![A_10, B_11]: (k6_subset_1(A_10, B_11)=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.19/3.67  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(k6_subset_1(A_6, B_7), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.19/3.67  tff(c_39, plain, (![A_6, B_7]: (m1_subset_1(k4_xboole_0(A_6, B_7), k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_10])).
% 10.19/3.67  tff(c_106, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=k3_subset_1(A_40, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 10.19/3.67  tff(c_122, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k4_xboole_0(A_6, B_7))=k3_subset_1(A_6, k4_xboole_0(A_6, B_7)))), inference(resolution, [status(thm)], [c_39, c_106])).
% 10.19/3.67  tff(c_495, plain, (![A_71, B_72]: (k4_xboole_0(A_71, k4_xboole_0(A_71, B_72))=k3_subset_1(A_71, k4_xboole_0(A_71, B_72)))), inference(resolution, [status(thm)], [c_39, c_106])).
% 10.19/3.67  tff(c_510, plain, (![A_71, B_72]: (m1_subset_1(k3_subset_1(A_71, k4_xboole_0(A_71, B_72)), k1_zfmisc_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_495, c_39])).
% 10.19/3.67  tff(c_139, plain, (![A_42, B_43]: (k3_subset_1(A_42, k3_subset_1(A_42, B_43))=B_43 | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 10.19/3.67  tff(c_154, plain, (![A_6, B_7]: (k3_subset_1(A_6, k3_subset_1(A_6, k4_xboole_0(A_6, B_7)))=k4_xboole_0(A_6, B_7))), inference(resolution, [status(thm)], [c_39, c_139])).
% 10.19/3.67  tff(c_767, plain, (![D_81, A_82, B_83]: (r2_hidden(D_81, k7_setfam_1(A_82, B_83)) | ~r2_hidden(k3_subset_1(A_82, D_81), B_83) | ~m1_subset_1(D_81, k1_zfmisc_1(A_82)) | ~m1_subset_1(k7_setfam_1(A_82, B_83), k1_zfmisc_1(k1_zfmisc_1(A_82))) | ~m1_subset_1(B_83, k1_zfmisc_1(k1_zfmisc_1(A_82))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 10.19/3.67  tff(c_769, plain, (![A_6, B_7, B_83]: (r2_hidden(k3_subset_1(A_6, k4_xboole_0(A_6, B_7)), k7_setfam_1(A_6, B_83)) | ~r2_hidden(k4_xboole_0(A_6, B_7), B_83) | ~m1_subset_1(k3_subset_1(A_6, k4_xboole_0(A_6, B_7)), k1_zfmisc_1(A_6)) | ~m1_subset_1(k7_setfam_1(A_6, B_83), k1_zfmisc_1(k1_zfmisc_1(A_6))) | ~m1_subset_1(B_83, k1_zfmisc_1(k1_zfmisc_1(A_6))))), inference(superposition, [status(thm), theory('equality')], [c_154, c_767])).
% 10.19/3.67  tff(c_15239, plain, (![A_328, B_329, B_330]: (r2_hidden(k3_subset_1(A_328, k4_xboole_0(A_328, B_329)), k7_setfam_1(A_328, B_330)) | ~r2_hidden(k4_xboole_0(A_328, B_329), B_330) | ~m1_subset_1(k7_setfam_1(A_328, B_330), k1_zfmisc_1(k1_zfmisc_1(A_328))) | ~m1_subset_1(B_330, k1_zfmisc_1(k1_zfmisc_1(A_328))))), inference(demodulation, [status(thm), theory('equality')], [c_510, c_769])).
% 10.19/3.67  tff(c_15372, plain, (![B_329]: (r2_hidden(k3_subset_1('#skF_2', k4_xboole_0('#skF_2', B_329)), k1_xboole_0) | ~r2_hidden(k4_xboole_0('#skF_2', B_329), '#skF_3') | ~m1_subset_1(k7_setfam_1('#skF_2', '#skF_3'), k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_34, c_15239])).
% 10.19/3.67  tff(c_15408, plain, (![B_329]: (r2_hidden(k3_subset_1('#skF_2', k4_xboole_0('#skF_2', B_329)), k1_xboole_0) | ~r2_hidden(k4_xboole_0('#skF_2', B_329), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_324, c_34, c_15372])).
% 10.19/3.67  tff(c_15411, plain, (![B_331]: (~r2_hidden(k4_xboole_0('#skF_2', B_331), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_69, c_15408])).
% 10.19/3.67  tff(c_15677, plain, (![B_332]: (~r2_hidden(k3_subset_1('#skF_2', k4_xboole_0('#skF_2', B_332)), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_122, c_15411])).
% 10.19/3.67  tff(c_15712, plain, (~r2_hidden(k3_subset_1('#skF_2', k3_subset_1('#skF_2', '#skF_1'('#skF_2', k1_xboole_0, '#skF_3'))), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_7272, c_15677])).
% 10.19/3.67  tff(c_15841, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9849, c_7323, c_15712])).
% 10.19/3.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.19/3.67  
% 10.19/3.67  Inference rules
% 10.19/3.67  ----------------------
% 10.19/3.67  #Ref     : 0
% 10.19/3.67  #Sup     : 3765
% 10.19/3.67  #Fact    : 8
% 10.19/3.67  #Define  : 0
% 10.19/3.67  #Split   : 23
% 10.19/3.67  #Chain   : 0
% 10.19/3.67  #Close   : 0
% 10.19/3.67  
% 10.19/3.67  Ordering : KBO
% 10.19/3.67  
% 10.19/3.67  Simplification rules
% 10.19/3.67  ----------------------
% 10.19/3.67  #Subsume      : 606
% 10.19/3.67  #Demod        : 1440
% 10.19/3.67  #Tautology    : 780
% 10.19/3.67  #SimpNegUnit  : 107
% 10.19/3.67  #BackRed      : 43
% 10.19/3.67  
% 10.19/3.67  #Partial instantiations: 0
% 10.19/3.67  #Strategies tried      : 1
% 10.19/3.67  
% 10.19/3.67  Timing (in seconds)
% 10.19/3.67  ----------------------
% 10.19/3.68  Preprocessing        : 0.32
% 10.19/3.68  Parsing              : 0.17
% 10.19/3.68  CNF conversion       : 0.02
% 10.19/3.68  Main loop            : 2.57
% 10.19/3.68  Inferencing          : 0.68
% 10.19/3.68  Reduction            : 0.89
% 10.19/3.68  Demodulation         : 0.66
% 10.19/3.68  BG Simplification    : 0.10
% 10.19/3.68  Subsumption          : 0.69
% 10.19/3.68  Abstraction          : 0.14
% 10.19/3.68  MUC search           : 0.00
% 10.19/3.68  Cooper               : 0.00
% 10.19/3.68  Total                : 2.93
% 10.19/3.68  Index Insertion      : 0.00
% 10.19/3.68  Index Deletion       : 0.00
% 10.19/3.68  Index Matching       : 0.00
% 10.19/3.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
