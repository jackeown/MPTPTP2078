%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1839+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:30 EST 2020

% Result     : Theorem 16.84s
% Output     : CNFRefutation 16.98s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 822 expanded)
%              Number of leaves         :   28 ( 286 expanded)
%              Depth                    :   33
%              Number of atoms          :  207 (1936 expanded)
%              Number of equality atoms :   34 ( 306 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k3_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_55,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_46,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_26,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_92,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_36,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(k3_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_9] : m1_subset_1('#skF_2'(A_9),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_143,plain,(
    ! [A_53,B_54] :
      ( k6_domain_1(A_53,B_54) = k1_tarski(B_54)
      | ~ m1_subset_1(B_54,A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_155,plain,(
    ! [A_9] :
      ( k6_domain_1(A_9,'#skF_2'(A_9)) = k1_tarski('#skF_2'(A_9))
      | v1_xboole_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_143])).

tff(c_180,plain,(
    ! [A_66,B_67] :
      ( m1_subset_1(k6_domain_1(A_66,B_67),k1_zfmisc_1(A_66))
      | ~ m1_subset_1(B_67,A_66)
      | v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_193,plain,(
    ! [A_9] :
      ( m1_subset_1(k1_tarski('#skF_2'(A_9)),k1_zfmisc_1(A_9))
      | ~ m1_subset_1('#skF_2'(A_9),A_9)
      | v1_xboole_0(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_180])).

tff(c_203,plain,(
    ! [A_68] :
      ( m1_subset_1(k1_tarski('#skF_2'(A_68)),k1_zfmisc_1(A_68))
      | v1_xboole_0(A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_193])).

tff(c_24,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | ~ m1_subset_1(A_19,k1_zfmisc_1(B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_218,plain,(
    ! [A_69] :
      ( r1_tarski(k1_tarski('#skF_2'(A_69)),A_69)
      | v1_xboole_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_203,c_24])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( r2_hidden(A_17,B_18)
      | ~ r1_tarski(k1_tarski(A_17),B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_228,plain,(
    ! [A_70] :
      ( r2_hidden('#skF_2'(A_70),A_70)
      | v1_xboole_0(A_70) ) ),
    inference(resolution,[status(thm)],[c_218,c_20])).

tff(c_26,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_131,plain,(
    ! [C_50,B_51,A_52] :
      ( ~ v1_xboole_0(C_50)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(C_50))
      | ~ r2_hidden(A_52,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_141,plain,(
    ! [B_20,A_52,A_19] :
      ( ~ v1_xboole_0(B_20)
      | ~ r2_hidden(A_52,A_19)
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(resolution,[status(thm)],[c_26,c_131])).

tff(c_270,plain,(
    ! [B_75,A_76] :
      ( ~ v1_xboole_0(B_75)
      | ~ r1_tarski(A_76,B_75)
      | v1_xboole_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_228,c_141])).

tff(c_302,plain,(
    ! [A_79,B_80] :
      ( ~ v1_xboole_0(A_79)
      | v1_xboole_0(k3_xboole_0(A_79,B_80)) ) ),
    inference(resolution,[status(thm)],[c_16,c_270])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_34,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_39,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_34])).

tff(c_312,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_302,c_39])).

tff(c_32,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_36,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_226,plain,(
    ! [A_69] :
      ( r2_hidden('#skF_2'(A_69),A_69)
      | v1_xboole_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_218,c_20])).

tff(c_6,plain,(
    ! [A_3] :
      ( k6_domain_1(A_3,'#skF_1'(A_3)) = A_3
      | ~ v1_zfmisc_1(A_3)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    ! [A_3] :
      ( m1_subset_1('#skF_1'(A_3),A_3)
      | ~ v1_zfmisc_1(A_3)
      | v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_361,plain,(
    ! [A_92] :
      ( k6_domain_1(A_92,'#skF_1'(A_92)) = k1_tarski('#skF_1'(A_92))
      | ~ v1_zfmisc_1(A_92)
      | v1_xboole_0(A_92) ) ),
    inference(resolution,[status(thm)],[c_8,c_143])).

tff(c_514,plain,(
    ! [A_103] :
      ( k1_tarski('#skF_1'(A_103)) = A_103
      | ~ v1_zfmisc_1(A_103)
      | v1_xboole_0(A_103)
      | ~ v1_zfmisc_1(A_103)
      | v1_xboole_0(A_103) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_361])).

tff(c_94,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(k1_tarski(A_41),B_42)
      | ~ r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( B_16 = A_15
      | ~ r1_tarski(k1_tarski(A_15),k1_tarski(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_103,plain,(
    ! [B_16,A_41] :
      ( B_16 = A_41
      | ~ r2_hidden(A_41,k1_tarski(B_16)) ) ),
    inference(resolution,[status(thm)],[c_94,c_18])).

tff(c_816,plain,(
    ! [A_146,A_147] :
      ( A_146 = '#skF_1'(A_147)
      | ~ r2_hidden(A_146,A_147)
      | ~ v1_zfmisc_1(A_147)
      | v1_xboole_0(A_147)
      | ~ v1_zfmisc_1(A_147)
      | v1_xboole_0(A_147) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_103])).

tff(c_842,plain,(
    ! [A_150] :
      ( '#skF_2'(A_150) = '#skF_1'(A_150)
      | ~ v1_zfmisc_1(A_150)
      | v1_xboole_0(A_150) ) ),
    inference(resolution,[status(thm)],[c_226,c_816])).

tff(c_845,plain,
    ( '#skF_2'('#skF_3') = '#skF_1'('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_842])).

tff(c_848,plain,(
    '#skF_2'('#skF_3') = '#skF_1'('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_845])).

tff(c_883,plain,
    ( k6_domain_1('#skF_3','#skF_1'('#skF_3')) = k1_tarski('#skF_2'('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_848,c_155])).

tff(c_903,plain,
    ( k6_domain_1('#skF_3','#skF_1'('#skF_3')) = k1_tarski('#skF_1'('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_848,c_883])).

tff(c_904,plain,(
    k6_domain_1('#skF_3','#skF_1'('#skF_3')) = k1_tarski('#skF_1'('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_903])).

tff(c_1130,plain,
    ( k1_tarski('#skF_1'('#skF_3')) = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_904,c_6])).

tff(c_1156,plain,
    ( k1_tarski('#skF_1'('#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1130])).

tff(c_1157,plain,(
    k1_tarski('#skF_1'('#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_1156])).

tff(c_42,plain,(
    ! [B_31,A_32] : k3_xboole_0(B_31,A_32) = k3_xboole_0(A_32,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_57,plain,(
    ! [B_31,A_32] : r1_tarski(k3_xboole_0(B_31,A_32),A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_16])).

tff(c_167,plain,(
    ! [A_61,C_62,B_63] :
      ( m1_subset_1(A_61,C_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(C_62))
      | ~ r2_hidden(A_61,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_321,plain,(
    ! [A_84,B_85,A_86] :
      ( m1_subset_1(A_84,B_85)
      | ~ r2_hidden(A_84,A_86)
      | ~ r1_tarski(A_86,B_85) ) ),
    inference(resolution,[status(thm)],[c_26,c_167])).

tff(c_324,plain,(
    ! [A_69,B_85] :
      ( m1_subset_1('#skF_2'(A_69),B_85)
      | ~ r1_tarski(A_69,B_85)
      | v1_xboole_0(A_69) ) ),
    inference(resolution,[status(thm)],[c_226,c_321])).

tff(c_325,plain,(
    ! [A_87,B_88] :
      ( m1_subset_1('#skF_2'(A_87),B_88)
      | ~ r1_tarski(A_87,B_88)
      | v1_xboole_0(A_87) ) ),
    inference(resolution,[status(thm)],[c_226,c_321])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k6_domain_1(A_11,B_12) = k1_tarski(B_12)
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2150,plain,(
    ! [B_204,A_205] :
      ( k6_domain_1(B_204,'#skF_2'(A_205)) = k1_tarski('#skF_2'(A_205))
      | v1_xboole_0(B_204)
      | ~ r1_tarski(A_205,B_204)
      | v1_xboole_0(A_205) ) ),
    inference(resolution,[status(thm)],[c_325,c_14])).

tff(c_200,plain,(
    ! [A_66,B_67] :
      ( r1_tarski(k6_domain_1(A_66,B_67),A_66)
      | ~ m1_subset_1(B_67,A_66)
      | v1_xboole_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_180,c_24])).

tff(c_22145,plain,(
    ! [A_813,B_814] :
      ( r1_tarski(k1_tarski('#skF_2'(A_813)),B_814)
      | ~ m1_subset_1('#skF_2'(A_813),B_814)
      | v1_xboole_0(B_814)
      | v1_xboole_0(B_814)
      | ~ r1_tarski(A_813,B_814)
      | v1_xboole_0(A_813) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2150,c_200])).

tff(c_1205,plain,(
    ! [A_15] :
      ( A_15 = '#skF_1'('#skF_3')
      | ~ r1_tarski(k1_tarski(A_15),'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1157,c_18])).

tff(c_22318,plain,(
    ! [A_813] :
      ( '#skF_2'(A_813) = '#skF_1'('#skF_3')
      | ~ m1_subset_1('#skF_2'(A_813),'#skF_3')
      | v1_xboole_0('#skF_3')
      | ~ r1_tarski(A_813,'#skF_3')
      | v1_xboole_0(A_813) ) ),
    inference(resolution,[status(thm)],[c_22145,c_1205])).

tff(c_22404,plain,(
    ! [A_815] :
      ( '#skF_2'(A_815) = '#skF_1'('#skF_3')
      | ~ m1_subset_1('#skF_2'(A_815),'#skF_3')
      | ~ r1_tarski(A_815,'#skF_3')
      | v1_xboole_0(A_815) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_38,c_22318])).

tff(c_22497,plain,(
    ! [A_816] :
      ( '#skF_2'(A_816) = '#skF_1'('#skF_3')
      | ~ r1_tarski(A_816,'#skF_3')
      | v1_xboole_0(A_816) ) ),
    inference(resolution,[status(thm)],[c_324,c_22404])).

tff(c_22695,plain,(
    ! [B_817] :
      ( '#skF_2'(k3_xboole_0(B_817,'#skF_3')) = '#skF_1'('#skF_3')
      | v1_xboole_0(k3_xboole_0(B_817,'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_57,c_22497])).

tff(c_22715,plain,(
    '#skF_2'(k3_xboole_0('#skF_4','#skF_3')) = '#skF_1'('#skF_3') ),
    inference(resolution,[status(thm)],[c_22695,c_39])).

tff(c_217,plain,(
    ! [A_68] :
      ( r1_tarski(k1_tarski('#skF_2'(A_68)),A_68)
      | v1_xboole_0(A_68) ) ),
    inference(resolution,[status(thm)],[c_203,c_24])).

tff(c_23187,plain,
    ( r1_tarski(k1_tarski('#skF_1'('#skF_3')),k3_xboole_0('#skF_4','#skF_3'))
    | v1_xboole_0(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_22715,c_217])).

tff(c_23317,plain,
    ( r1_tarski('#skF_3',k3_xboole_0('#skF_4','#skF_3'))
    | v1_xboole_0(k3_xboole_0('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1157,c_23187])).

tff(c_23318,plain,(
    r1_tarski('#skF_3',k3_xboole_0('#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_23317])).

tff(c_2877,plain,(
    ! [A_253,B_254] :
      ( r2_hidden('#skF_1'(A_253),B_254)
      | ~ r1_tarski(A_253,B_254)
      | ~ v1_zfmisc_1(A_253)
      | v1_xboole_0(A_253)
      | ~ v1_zfmisc_1(A_253)
      | v1_xboole_0(A_253) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_20])).

tff(c_177,plain,(
    ! [A_61,B_20,A_19] :
      ( m1_subset_1(A_61,B_20)
      | ~ r2_hidden(A_61,A_19)
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(resolution,[status(thm)],[c_26,c_167])).

tff(c_3548,plain,(
    ! [A_282,B_283,B_284] :
      ( m1_subset_1('#skF_1'(A_282),B_283)
      | ~ r1_tarski(B_284,B_283)
      | ~ r1_tarski(A_282,B_284)
      | ~ v1_zfmisc_1(A_282)
      | v1_xboole_0(A_282) ) ),
    inference(resolution,[status(thm)],[c_2877,c_177])).

tff(c_3590,plain,(
    ! [A_282,A_13,B_14] :
      ( m1_subset_1('#skF_1'(A_282),A_13)
      | ~ r1_tarski(A_282,k3_xboole_0(A_13,B_14))
      | ~ v1_zfmisc_1(A_282)
      | v1_xboole_0(A_282) ) ),
    inference(resolution,[status(thm)],[c_16,c_3548])).

tff(c_23336,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),'#skF_4')
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_23318,c_3590])).

tff(c_23392,plain,
    ( m1_subset_1('#skF_1'('#skF_3'),'#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_23336])).

tff(c_23393,plain,(
    m1_subset_1('#skF_1'('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_23392])).

tff(c_23433,plain,
    ( k6_domain_1('#skF_4','#skF_1'('#skF_3')) = k1_tarski('#skF_1'('#skF_3'))
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_23393,c_14])).

tff(c_23438,plain,
    ( k6_domain_1('#skF_4','#skF_1'('#skF_3')) = '#skF_3'
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1157,c_23433])).

tff(c_23439,plain,(
    k6_domain_1('#skF_4','#skF_1'('#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_312,c_23438])).

tff(c_23508,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_3'),'#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_23439,c_200])).

tff(c_23571,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23393,c_23508])).

tff(c_23573,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_312,c_32,c_23571])).

%------------------------------------------------------------------------------
