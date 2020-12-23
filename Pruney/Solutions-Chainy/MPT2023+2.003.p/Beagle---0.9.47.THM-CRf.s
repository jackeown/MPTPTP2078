%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:12 EST 2020

% Result     : Theorem 27.32s
% Output     : CNFRefutation 27.37s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 689 expanded)
%              Number of leaves         :   43 ( 271 expanded)
%              Depth                    :   18
%              Number of atoms          :  363 (2542 expanded)
%              Number of equality atoms :   11 (  15 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k9_yellow_6 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k9_yellow_6,type,(
    k9_yellow_6: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_167,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(k9_yellow_6(A,B)))
                   => m1_subset_1(k3_xboole_0(C,D),u1_struct_0(k9_yellow_6(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_waybel_9)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_148,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
             => m1_connsp_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).

tff(f_114,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_133,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r2_hidden(C,u1_struct_0(k9_yellow_6(A,B)))
              <=> ( r2_hidden(B,C)
                  & v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_100,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_tops_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_66,plain,(
    m1_subset_1('#skF_8',u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_108,plain,(
    ! [B_79,A_80] :
      ( v1_xboole_0(B_79)
      | ~ m1_subset_1(B_79,A_80)
      | ~ v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_123,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_66,c_108])).

tff(c_131,plain,(
    ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_124,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_70,c_108])).

tff(c_125,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_36,plain,(
    ! [B_21,A_20] :
      ( r2_hidden(B_21,A_20)
      | ~ m1_subset_1(B_21,A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_185,plain,(
    ! [D_95,B_96,A_97] :
      ( r2_hidden(D_95,B_96)
      | ~ r2_hidden(D_95,k3_xboole_0(A_97,B_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_77085,plain,(
    ! [A_2887,B_2888,B_2889] :
      ( r2_hidden('#skF_2'(k3_xboole_0(A_2887,B_2888),B_2889),B_2888)
      | r1_tarski(k3_xboole_0(A_2887,B_2888),B_2889) ) ),
    inference(resolution,[status(thm)],[c_10,c_185])).

tff(c_74,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_72,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_68,plain,(
    m1_subset_1('#skF_7',u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1184,plain,(
    ! [C_222,A_223,B_224] :
      ( m1_connsp_2(C_222,A_223,B_224)
      | ~ m1_subset_1(C_222,u1_struct_0(k9_yellow_6(A_223,B_224)))
      | ~ m1_subset_1(B_224,u1_struct_0(A_223))
      | ~ l1_pre_topc(A_223)
      | ~ v2_pre_topc(A_223)
      | v2_struct_0(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_148])).

tff(c_1215,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_1184])).

tff(c_1228,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_1215])).

tff(c_1229,plain,(
    m1_connsp_2('#skF_7','#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1228])).

tff(c_54,plain,(
    ! [C_41,A_38,B_39] :
      ( m1_subset_1(C_41,k1_zfmisc_1(u1_struct_0(A_38)))
      | ~ m1_connsp_2(C_41,A_38,B_39)
      | ~ m1_subset_1(B_39,u1_struct_0(A_38))
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38)
      | v2_struct_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_1235,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1229,c_54])).

tff(c_1238,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_1235])).

tff(c_1239,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1238])).

tff(c_50,plain,(
    ! [A_32,C_34,B_33] :
      ( m1_subset_1(A_32,C_34)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(C_34))
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1273,plain,(
    ! [A_225] :
      ( m1_subset_1(A_225,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_225,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1239,c_50])).

tff(c_160,plain,(
    ! [A_91,B_92] :
      ( ~ r2_hidden('#skF_2'(A_91,B_92),B_92)
      | r1_tarski(A_91,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_169,plain,(
    ! [A_91,A_20] :
      ( r1_tarski(A_91,A_20)
      | ~ m1_subset_1('#skF_2'(A_91,A_20),A_20)
      | v1_xboole_0(A_20) ) ),
    inference(resolution,[status(thm)],[c_36,c_160])).

tff(c_1277,plain,(
    ! [A_91] :
      ( r1_tarski(A_91,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(A_91,u1_struct_0('#skF_5')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1273,c_169])).

tff(c_1283,plain,(
    ! [A_91] :
      ( r1_tarski(A_91,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(A_91,u1_struct_0('#skF_5')),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_1277])).

tff(c_77158,plain,(
    ! [A_2887] : r1_tarski(k3_xboole_0(A_2887,'#skF_7'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_77085,c_1283])).

tff(c_577,plain,(
    ! [D_147,A_148,B_149] :
      ( r2_hidden(D_147,k3_xboole_0(A_148,B_149))
      | ~ r2_hidden(D_147,B_149)
      | ~ r2_hidden(D_147,A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_78721,plain,(
    ! [D_2984,B_2985,A_2986,B_2987] :
      ( r2_hidden(D_2984,B_2985)
      | ~ r1_tarski(k3_xboole_0(A_2986,B_2987),B_2985)
      | ~ r2_hidden(D_2984,B_2987)
      | ~ r2_hidden(D_2984,A_2986) ) ),
    inference(resolution,[status(thm)],[c_577,c_6])).

tff(c_78985,plain,(
    ! [D_2994,A_2995] :
      ( r2_hidden(D_2994,u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_2994,'#skF_7')
      | ~ r2_hidden(D_2994,A_2995) ) ),
    inference(resolution,[status(thm)],[c_77158,c_78721])).

tff(c_84024,plain,(
    ! [B_3198,A_3199] :
      ( r2_hidden(B_3198,u1_struct_0('#skF_5'))
      | ~ r2_hidden(B_3198,'#skF_7')
      | ~ m1_subset_1(B_3198,A_3199)
      | v1_xboole_0(A_3199) ) ),
    inference(resolution,[status(thm)],[c_36,c_78985])).

tff(c_84122,plain,
    ( r2_hidden('#skF_6',u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_6','#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_70,c_84024])).

tff(c_84215,plain,
    ( r2_hidden('#skF_6',u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_84122])).

tff(c_84216,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_84215])).

tff(c_2091,plain,(
    ! [B_273,C_274,A_275] :
      ( r2_hidden(B_273,C_274)
      | ~ r2_hidden(C_274,u1_struct_0(k9_yellow_6(A_275,B_273)))
      | ~ m1_subset_1(C_274,k1_zfmisc_1(u1_struct_0(A_275)))
      | ~ m1_subset_1(B_273,u1_struct_0(A_275))
      | ~ l1_pre_topc(A_275)
      | ~ v2_pre_topc(A_275)
      | v2_struct_0(A_275) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_97388,plain,(
    ! [B_3640,B_3641,A_3642] :
      ( r2_hidden(B_3640,B_3641)
      | ~ m1_subset_1(B_3641,k1_zfmisc_1(u1_struct_0(A_3642)))
      | ~ m1_subset_1(B_3640,u1_struct_0(A_3642))
      | ~ l1_pre_topc(A_3642)
      | ~ v2_pre_topc(A_3642)
      | v2_struct_0(A_3642)
      | ~ m1_subset_1(B_3641,u1_struct_0(k9_yellow_6(A_3642,B_3640)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_3642,B_3640))) ) ),
    inference(resolution,[status(thm)],[c_36,c_2091])).

tff(c_97470,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_68,c_97388])).

tff(c_97496,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_1239,c_97470])).

tff(c_97498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_76,c_84216,c_97496])).

tff(c_97500,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_84215])).

tff(c_12,plain,(
    ! [D_15,A_10,B_11] :
      ( r2_hidden(D_15,k3_xboole_0(A_10,B_11))
      | ~ r2_hidden(D_15,B_11)
      | ~ r2_hidden(D_15,A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1218,plain,
    ( m1_connsp_2('#skF_8','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_1184])).

tff(c_1232,plain,
    ( m1_connsp_2('#skF_8','#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_1218])).

tff(c_1233,plain,(
    m1_connsp_2('#skF_8','#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1232])).

tff(c_1241,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1233,c_54])).

tff(c_1244,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_1241])).

tff(c_1245,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_1244])).

tff(c_44,plain,(
    ! [A_25,B_26,C_27] :
      ( k9_subset_1(A_25,B_26,C_27) = k3_xboole_0(B_26,C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1328,plain,(
    ! [B_233] : k9_subset_1(u1_struct_0('#skF_5'),B_233,'#skF_8') = k3_xboole_0(B_233,'#skF_8') ),
    inference(resolution,[status(thm)],[c_1245,c_44])).

tff(c_42,plain,(
    ! [A_22,B_23,C_24] :
      ( m1_subset_1(k9_subset_1(A_22,B_23,C_24),k1_zfmisc_1(A_22))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1337,plain,(
    ! [B_233] :
      ( m1_subset_1(k3_xboole_0(B_233,'#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1328,c_42])).

tff(c_1343,plain,(
    ! [B_233] : m1_subset_1(k3_xboole_0(B_233,'#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1245,c_1337])).

tff(c_2656,plain,(
    ! [B_295,C_296,A_297] :
      ( v3_pre_topc(k3_xboole_0(B_295,C_296),A_297)
      | ~ m1_subset_1(C_296,k1_zfmisc_1(u1_struct_0(A_297)))
      | ~ v3_pre_topc(C_296,A_297)
      | ~ m1_subset_1(B_295,k1_zfmisc_1(u1_struct_0(A_297)))
      | ~ v3_pre_topc(B_295,A_297)
      | ~ l1_pre_topc(A_297)
      | ~ v2_pre_topc(A_297) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2668,plain,(
    ! [B_295] :
      ( v3_pre_topc(k3_xboole_0(B_295,'#skF_7'),'#skF_5')
      | ~ v3_pre_topc('#skF_7','#skF_5')
      | ~ m1_subset_1(B_295,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_295,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1239,c_2656])).

tff(c_2710,plain,(
    ! [B_295] :
      ( v3_pre_topc(k3_xboole_0(B_295,'#skF_7'),'#skF_5')
      | ~ v3_pre_topc('#skF_7','#skF_5')
      | ~ m1_subset_1(B_295,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_295,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_2668])).

tff(c_45999,plain,(
    ~ v3_pre_topc('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2710])).

tff(c_2413,plain,(
    ! [C_281,A_282,B_283] :
      ( v3_pre_topc(C_281,A_282)
      | ~ r2_hidden(C_281,u1_struct_0(k9_yellow_6(A_282,B_283)))
      | ~ m1_subset_1(C_281,k1_zfmisc_1(u1_struct_0(A_282)))
      | ~ m1_subset_1(B_283,u1_struct_0(A_282))
      | ~ l1_pre_topc(A_282)
      | ~ v2_pre_topc(A_282)
      | v2_struct_0(A_282) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_76925,plain,(
    ! [B_2881,A_2882,B_2883] :
      ( v3_pre_topc(B_2881,A_2882)
      | ~ m1_subset_1(B_2881,k1_zfmisc_1(u1_struct_0(A_2882)))
      | ~ m1_subset_1(B_2883,u1_struct_0(A_2882))
      | ~ l1_pre_topc(A_2882)
      | ~ v2_pre_topc(A_2882)
      | v2_struct_0(A_2882)
      | ~ m1_subset_1(B_2881,u1_struct_0(k9_yellow_6(A_2882,B_2883)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_2882,B_2883))) ) ),
    inference(resolution,[status(thm)],[c_36,c_2413])).

tff(c_77007,plain,
    ( v3_pre_topc('#skF_7','#skF_5')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_68,c_76925])).

tff(c_77033,plain,
    ( v3_pre_topc('#skF_7','#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_1239,c_77007])).

tff(c_77035,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_76,c_45999,c_77033])).

tff(c_77037,plain,(
    v3_pre_topc('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_2710])).

tff(c_2666,plain,(
    ! [B_295] :
      ( v3_pre_topc(k3_xboole_0(B_295,'#skF_8'),'#skF_5')
      | ~ v3_pre_topc('#skF_8','#skF_5')
      | ~ m1_subset_1(B_295,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_295,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1245,c_2656])).

tff(c_2707,plain,(
    ! [B_295] :
      ( v3_pre_topc(k3_xboole_0(B_295,'#skF_8'),'#skF_5')
      | ~ v3_pre_topc('#skF_8','#skF_5')
      | ~ m1_subset_1(B_295,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_295,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_2666])).

tff(c_2800,plain,(
    ~ v3_pre_topc('#skF_8','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2707])).

tff(c_45869,plain,(
    ! [B_1742,A_1743,B_1744] :
      ( v3_pre_topc(B_1742,A_1743)
      | ~ m1_subset_1(B_1742,k1_zfmisc_1(u1_struct_0(A_1743)))
      | ~ m1_subset_1(B_1744,u1_struct_0(A_1743))
      | ~ l1_pre_topc(A_1743)
      | ~ v2_pre_topc(A_1743)
      | v2_struct_0(A_1743)
      | ~ m1_subset_1(B_1742,u1_struct_0(k9_yellow_6(A_1743,B_1744)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1743,B_1744))) ) ),
    inference(resolution,[status(thm)],[c_36,c_2413])).

tff(c_45954,plain,
    ( v3_pre_topc('#skF_8','#skF_5')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_66,c_45869])).

tff(c_45981,plain,
    ( v3_pre_topc('#skF_8','#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_1245,c_45954])).

tff(c_45983,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_76,c_2800,c_45981])).

tff(c_77962,plain,(
    ! [B_2932] :
      ( v3_pre_topc(k3_xboole_0(B_2932,'#skF_8'),'#skF_5')
      | ~ m1_subset_1(B_2932,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_2932,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_2707])).

tff(c_77980,plain,
    ( v3_pre_topc(k3_xboole_0('#skF_7','#skF_8'),'#skF_5')
    | ~ v3_pre_topc('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_1239,c_77962])).

tff(c_78022,plain,(
    v3_pre_topc(k3_xboole_0('#skF_7','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_77037,c_77980])).

tff(c_77295,plain,(
    ! [C_2896,A_2897,B_2898] :
      ( r2_hidden(C_2896,u1_struct_0(k9_yellow_6(A_2897,B_2898)))
      | ~ v3_pre_topc(C_2896,A_2897)
      | ~ r2_hidden(B_2898,C_2896)
      | ~ m1_subset_1(C_2896,k1_zfmisc_1(u1_struct_0(A_2897)))
      | ~ m1_subset_1(B_2898,u1_struct_0(A_2897))
      | ~ l1_pre_topc(A_2897)
      | ~ v2_pre_topc(A_2897)
      | v2_struct_0(A_2897) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_48,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(A_30,B_31)
      | ~ r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_111508,plain,(
    ! [C_3926,A_3927,B_3928] :
      ( m1_subset_1(C_3926,u1_struct_0(k9_yellow_6(A_3927,B_3928)))
      | ~ v3_pre_topc(C_3926,A_3927)
      | ~ r2_hidden(B_3928,C_3926)
      | ~ m1_subset_1(C_3926,k1_zfmisc_1(u1_struct_0(A_3927)))
      | ~ m1_subset_1(B_3928,u1_struct_0(A_3927))
      | ~ l1_pre_topc(A_3927)
      | ~ v2_pre_topc(A_3927)
      | v2_struct_0(A_3927) ) ),
    inference(resolution,[status(thm)],[c_77295,c_48])).

tff(c_64,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_7','#skF_8'),u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_111526,plain,
    ( ~ v3_pre_topc(k3_xboole_0('#skF_7','#skF_8'),'#skF_5')
    | ~ r2_hidden('#skF_6',k3_xboole_0('#skF_7','#skF_8'))
    | ~ m1_subset_1(k3_xboole_0('#skF_7','#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_111508,c_64])).

tff(c_111538,plain,
    ( ~ r2_hidden('#skF_6',k3_xboole_0('#skF_7','#skF_8'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_1343,c_78022,c_111526])).

tff(c_111539,plain,(
    ~ r2_hidden('#skF_6',k3_xboole_0('#skF_7','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_111538])).

tff(c_111549,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_111539])).

tff(c_111557,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97500,c_111549])).

tff(c_111881,plain,(
    ! [B_3940,B_3941,A_3942] :
      ( r2_hidden(B_3940,B_3941)
      | ~ m1_subset_1(B_3941,k1_zfmisc_1(u1_struct_0(A_3942)))
      | ~ m1_subset_1(B_3940,u1_struct_0(A_3942))
      | ~ l1_pre_topc(A_3942)
      | ~ v2_pre_topc(A_3942)
      | v2_struct_0(A_3942)
      | ~ m1_subset_1(B_3941,u1_struct_0(k9_yellow_6(A_3942,B_3940)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_3942,B_3940))) ) ),
    inference(resolution,[status(thm)],[c_36,c_2091])).

tff(c_111966,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_66,c_111881])).

tff(c_111993,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_1245,c_111966])).

tff(c_111995,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_76,c_111557,c_111993])).

tff(c_111997,plain,(
    v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_122,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_68,c_108])).

tff(c_111999,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111997,c_122])).

tff(c_32,plain,(
    ! [A_18,B_19] : k2_xboole_0(A_18,k3_xboole_0(A_18,B_19)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_112007,plain,(
    ! [A_3945,B_3946] :
      ( r2_hidden('#skF_2'(A_3945,B_3946),A_3945)
      | r1_tarski(A_3945,B_3946) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_112049,plain,(
    ! [A_3951,B_3952] :
      ( ~ v1_xboole_0(A_3951)
      | r1_tarski(A_3951,B_3952) ) ),
    inference(resolution,[status(thm)],[c_112007,c_2])).

tff(c_30,plain,(
    ! [A_16,B_17] :
      ( k2_xboole_0(A_16,B_17) = B_17
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_112054,plain,(
    ! [A_3953,B_3954] :
      ( k2_xboole_0(A_3953,B_3954) = B_3954
      | ~ v1_xboole_0(A_3953) ) ),
    inference(resolution,[status(thm)],[c_112049,c_30])).

tff(c_112064,plain,(
    ! [B_3955] : k2_xboole_0('#skF_7',B_3955) = B_3955 ),
    inference(resolution,[status(thm)],[c_111999,c_112054])).

tff(c_112086,plain,(
    ! [B_19] : k3_xboole_0('#skF_7',B_19) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_112064])).

tff(c_38,plain,(
    ! [B_21,A_20] :
      ( m1_subset_1(B_21,A_20)
      | ~ v1_xboole_0(B_21)
      | ~ v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_112002,plain,
    ( ~ v1_xboole_0(k3_xboole_0('#skF_7','#skF_8'))
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_38,c_64])).

tff(c_112005,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111997,c_112002])).

tff(c_112118,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112086,c_112005])).

tff(c_112122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_111999,c_112118])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 27.32/17.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.37/17.49  
% 27.37/17.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.37/17.49  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_subset_1 > k9_yellow_6 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2
% 27.37/17.49  
% 27.37/17.49  %Foreground sorts:
% 27.37/17.49  
% 27.37/17.49  
% 27.37/17.49  %Background operators:
% 27.37/17.49  
% 27.37/17.49  
% 27.37/17.49  %Foreground operators:
% 27.37/17.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 27.37/17.49  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 27.37/17.49  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 27.37/17.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 27.37/17.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 27.37/17.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 27.37/17.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 27.37/17.49  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 27.37/17.49  tff('#skF_7', type, '#skF_7': $i).
% 27.37/17.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 27.37/17.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 27.37/17.49  tff('#skF_5', type, '#skF_5': $i).
% 27.37/17.49  tff('#skF_6', type, '#skF_6': $i).
% 27.37/17.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 27.37/17.49  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 27.37/17.49  tff('#skF_8', type, '#skF_8': $i).
% 27.37/17.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 27.37/17.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 27.37/17.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 27.37/17.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 27.37/17.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 27.37/17.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 27.37/17.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 27.37/17.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 27.37/17.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 27.37/17.49  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 27.37/17.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 27.37/17.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 27.37/17.49  
% 27.37/17.51  tff(f_167, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k3_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_waybel_9)).
% 27.37/17.51  tff(f_66, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 27.37/17.51  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 27.37/17.51  tff(f_47, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 27.37/17.51  tff(f_148, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => m1_connsp_2(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_waybel_9)).
% 27.37/17.51  tff(f_114, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 27.37/17.51  tff(f_86, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 27.37/17.51  tff(f_133, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_yellow_6)).
% 27.37/17.51  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 27.37/17.51  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 27.37/17.51  tff(f_100, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_tops_1)).
% 27.37/17.51  tff(f_80, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 27.37/17.51  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 27.37/17.51  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 27.37/17.51  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 27.37/17.51  tff(c_66, plain, (m1_subset_1('#skF_8', u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 27.37/17.51  tff(c_108, plain, (![B_79, A_80]: (v1_xboole_0(B_79) | ~m1_subset_1(B_79, A_80) | ~v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.37/17.51  tff(c_123, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_66, c_108])).
% 27.37/17.51  tff(c_131, plain, (~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_123])).
% 27.37/17.51  tff(c_76, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 27.37/17.51  tff(c_70, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 27.37/17.51  tff(c_124, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_108])).
% 27.37/17.51  tff(c_125, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_124])).
% 27.37/17.51  tff(c_36, plain, (![B_21, A_20]: (r2_hidden(B_21, A_20) | ~m1_subset_1(B_21, A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.37/17.51  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.37/17.51  tff(c_185, plain, (![D_95, B_96, A_97]: (r2_hidden(D_95, B_96) | ~r2_hidden(D_95, k3_xboole_0(A_97, B_96)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 27.37/17.51  tff(c_77085, plain, (![A_2887, B_2888, B_2889]: (r2_hidden('#skF_2'(k3_xboole_0(A_2887, B_2888), B_2889), B_2888) | r1_tarski(k3_xboole_0(A_2887, B_2888), B_2889))), inference(resolution, [status(thm)], [c_10, c_185])).
% 27.37/17.51  tff(c_74, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 27.37/17.51  tff(c_72, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 27.37/17.51  tff(c_68, plain, (m1_subset_1('#skF_7', u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 27.37/17.51  tff(c_1184, plain, (![C_222, A_223, B_224]: (m1_connsp_2(C_222, A_223, B_224) | ~m1_subset_1(C_222, u1_struct_0(k9_yellow_6(A_223, B_224))) | ~m1_subset_1(B_224, u1_struct_0(A_223)) | ~l1_pre_topc(A_223) | ~v2_pre_topc(A_223) | v2_struct_0(A_223))), inference(cnfTransformation, [status(thm)], [f_148])).
% 27.37/17.51  tff(c_1215, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_68, c_1184])).
% 27.37/17.51  tff(c_1228, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_1215])).
% 27.37/17.51  tff(c_1229, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_76, c_1228])).
% 27.37/17.51  tff(c_54, plain, (![C_41, A_38, B_39]: (m1_subset_1(C_41, k1_zfmisc_1(u1_struct_0(A_38))) | ~m1_connsp_2(C_41, A_38, B_39) | ~m1_subset_1(B_39, u1_struct_0(A_38)) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38) | v2_struct_0(A_38))), inference(cnfTransformation, [status(thm)], [f_114])).
% 27.37/17.51  tff(c_1235, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1229, c_54])).
% 27.37/17.51  tff(c_1238, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_1235])).
% 27.37/17.51  tff(c_1239, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_76, c_1238])).
% 27.37/17.51  tff(c_50, plain, (![A_32, C_34, B_33]: (m1_subset_1(A_32, C_34) | ~m1_subset_1(B_33, k1_zfmisc_1(C_34)) | ~r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_86])).
% 27.37/17.51  tff(c_1273, plain, (![A_225]: (m1_subset_1(A_225, u1_struct_0('#skF_5')) | ~r2_hidden(A_225, '#skF_7'))), inference(resolution, [status(thm)], [c_1239, c_50])).
% 27.37/17.51  tff(c_160, plain, (![A_91, B_92]: (~r2_hidden('#skF_2'(A_91, B_92), B_92) | r1_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.37/17.51  tff(c_169, plain, (![A_91, A_20]: (r1_tarski(A_91, A_20) | ~m1_subset_1('#skF_2'(A_91, A_20), A_20) | v1_xboole_0(A_20))), inference(resolution, [status(thm)], [c_36, c_160])).
% 27.37/17.51  tff(c_1277, plain, (![A_91]: (r1_tarski(A_91, u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(A_91, u1_struct_0('#skF_5')), '#skF_7'))), inference(resolution, [status(thm)], [c_1273, c_169])).
% 27.37/17.51  tff(c_1283, plain, (![A_91]: (r1_tarski(A_91, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(A_91, u1_struct_0('#skF_5')), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_125, c_1277])).
% 27.37/17.51  tff(c_77158, plain, (![A_2887]: (r1_tarski(k3_xboole_0(A_2887, '#skF_7'), u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_77085, c_1283])).
% 27.37/17.51  tff(c_577, plain, (![D_147, A_148, B_149]: (r2_hidden(D_147, k3_xboole_0(A_148, B_149)) | ~r2_hidden(D_147, B_149) | ~r2_hidden(D_147, A_148))), inference(cnfTransformation, [status(thm)], [f_47])).
% 27.37/17.51  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.37/17.51  tff(c_78721, plain, (![D_2984, B_2985, A_2986, B_2987]: (r2_hidden(D_2984, B_2985) | ~r1_tarski(k3_xboole_0(A_2986, B_2987), B_2985) | ~r2_hidden(D_2984, B_2987) | ~r2_hidden(D_2984, A_2986))), inference(resolution, [status(thm)], [c_577, c_6])).
% 27.37/17.51  tff(c_78985, plain, (![D_2994, A_2995]: (r2_hidden(D_2994, u1_struct_0('#skF_5')) | ~r2_hidden(D_2994, '#skF_7') | ~r2_hidden(D_2994, A_2995))), inference(resolution, [status(thm)], [c_77158, c_78721])).
% 27.37/17.51  tff(c_84024, plain, (![B_3198, A_3199]: (r2_hidden(B_3198, u1_struct_0('#skF_5')) | ~r2_hidden(B_3198, '#skF_7') | ~m1_subset_1(B_3198, A_3199) | v1_xboole_0(A_3199))), inference(resolution, [status(thm)], [c_36, c_78985])).
% 27.37/17.51  tff(c_84122, plain, (r2_hidden('#skF_6', u1_struct_0('#skF_5')) | ~r2_hidden('#skF_6', '#skF_7') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_84024])).
% 27.37/17.51  tff(c_84215, plain, (r2_hidden('#skF_6', u1_struct_0('#skF_5')) | ~r2_hidden('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_125, c_84122])).
% 27.37/17.51  tff(c_84216, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_84215])).
% 27.37/17.51  tff(c_2091, plain, (![B_273, C_274, A_275]: (r2_hidden(B_273, C_274) | ~r2_hidden(C_274, u1_struct_0(k9_yellow_6(A_275, B_273))) | ~m1_subset_1(C_274, k1_zfmisc_1(u1_struct_0(A_275))) | ~m1_subset_1(B_273, u1_struct_0(A_275)) | ~l1_pre_topc(A_275) | ~v2_pre_topc(A_275) | v2_struct_0(A_275))), inference(cnfTransformation, [status(thm)], [f_133])).
% 27.37/17.51  tff(c_97388, plain, (![B_3640, B_3641, A_3642]: (r2_hidden(B_3640, B_3641) | ~m1_subset_1(B_3641, k1_zfmisc_1(u1_struct_0(A_3642))) | ~m1_subset_1(B_3640, u1_struct_0(A_3642)) | ~l1_pre_topc(A_3642) | ~v2_pre_topc(A_3642) | v2_struct_0(A_3642) | ~m1_subset_1(B_3641, u1_struct_0(k9_yellow_6(A_3642, B_3640))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_3642, B_3640))))), inference(resolution, [status(thm)], [c_36, c_2091])).
% 27.37/17.51  tff(c_97470, plain, (r2_hidden('#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_68, c_97388])).
% 27.37/17.51  tff(c_97496, plain, (r2_hidden('#skF_6', '#skF_7') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_1239, c_97470])).
% 27.37/17.51  tff(c_97498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_76, c_84216, c_97496])).
% 27.37/17.51  tff(c_97500, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_84215])).
% 27.37/17.51  tff(c_12, plain, (![D_15, A_10, B_11]: (r2_hidden(D_15, k3_xboole_0(A_10, B_11)) | ~r2_hidden(D_15, B_11) | ~r2_hidden(D_15, A_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 27.37/17.51  tff(c_1218, plain, (m1_connsp_2('#skF_8', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_1184])).
% 27.37/17.51  tff(c_1232, plain, (m1_connsp_2('#skF_8', '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_1218])).
% 27.37/17.51  tff(c_1233, plain, (m1_connsp_2('#skF_8', '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_76, c_1232])).
% 27.37/17.51  tff(c_1241, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1233, c_54])).
% 27.37/17.51  tff(c_1244, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_1241])).
% 27.37/17.51  tff(c_1245, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_76, c_1244])).
% 27.37/17.51  tff(c_44, plain, (![A_25, B_26, C_27]: (k9_subset_1(A_25, B_26, C_27)=k3_xboole_0(B_26, C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 27.37/17.51  tff(c_1328, plain, (![B_233]: (k9_subset_1(u1_struct_0('#skF_5'), B_233, '#skF_8')=k3_xboole_0(B_233, '#skF_8'))), inference(resolution, [status(thm)], [c_1245, c_44])).
% 27.37/17.51  tff(c_42, plain, (![A_22, B_23, C_24]: (m1_subset_1(k9_subset_1(A_22, B_23, C_24), k1_zfmisc_1(A_22)) | ~m1_subset_1(C_24, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 27.37/17.51  tff(c_1337, plain, (![B_233]: (m1_subset_1(k3_xboole_0(B_233, '#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_1328, c_42])).
% 27.37/17.51  tff(c_1343, plain, (![B_233]: (m1_subset_1(k3_xboole_0(B_233, '#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_1245, c_1337])).
% 27.37/17.51  tff(c_2656, plain, (![B_295, C_296, A_297]: (v3_pre_topc(k3_xboole_0(B_295, C_296), A_297) | ~m1_subset_1(C_296, k1_zfmisc_1(u1_struct_0(A_297))) | ~v3_pre_topc(C_296, A_297) | ~m1_subset_1(B_295, k1_zfmisc_1(u1_struct_0(A_297))) | ~v3_pre_topc(B_295, A_297) | ~l1_pre_topc(A_297) | ~v2_pre_topc(A_297))), inference(cnfTransformation, [status(thm)], [f_100])).
% 27.37/17.51  tff(c_2668, plain, (![B_295]: (v3_pre_topc(k3_xboole_0(B_295, '#skF_7'), '#skF_5') | ~v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1(B_295, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_295, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_1239, c_2656])).
% 27.37/17.51  tff(c_2710, plain, (![B_295]: (v3_pre_topc(k3_xboole_0(B_295, '#skF_7'), '#skF_5') | ~v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1(B_295, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_295, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_2668])).
% 27.37/17.51  tff(c_45999, plain, (~v3_pre_topc('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_2710])).
% 27.37/17.51  tff(c_2413, plain, (![C_281, A_282, B_283]: (v3_pre_topc(C_281, A_282) | ~r2_hidden(C_281, u1_struct_0(k9_yellow_6(A_282, B_283))) | ~m1_subset_1(C_281, k1_zfmisc_1(u1_struct_0(A_282))) | ~m1_subset_1(B_283, u1_struct_0(A_282)) | ~l1_pre_topc(A_282) | ~v2_pre_topc(A_282) | v2_struct_0(A_282))), inference(cnfTransformation, [status(thm)], [f_133])).
% 27.37/17.51  tff(c_76925, plain, (![B_2881, A_2882, B_2883]: (v3_pre_topc(B_2881, A_2882) | ~m1_subset_1(B_2881, k1_zfmisc_1(u1_struct_0(A_2882))) | ~m1_subset_1(B_2883, u1_struct_0(A_2882)) | ~l1_pre_topc(A_2882) | ~v2_pre_topc(A_2882) | v2_struct_0(A_2882) | ~m1_subset_1(B_2881, u1_struct_0(k9_yellow_6(A_2882, B_2883))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_2882, B_2883))))), inference(resolution, [status(thm)], [c_36, c_2413])).
% 27.37/17.51  tff(c_77007, plain, (v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_68, c_76925])).
% 27.37/17.51  tff(c_77033, plain, (v3_pre_topc('#skF_7', '#skF_5') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_1239, c_77007])).
% 27.37/17.51  tff(c_77035, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_76, c_45999, c_77033])).
% 27.37/17.51  tff(c_77037, plain, (v3_pre_topc('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_2710])).
% 27.37/17.51  tff(c_2666, plain, (![B_295]: (v3_pre_topc(k3_xboole_0(B_295, '#skF_8'), '#skF_5') | ~v3_pre_topc('#skF_8', '#skF_5') | ~m1_subset_1(B_295, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_295, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_1245, c_2656])).
% 27.37/17.51  tff(c_2707, plain, (![B_295]: (v3_pre_topc(k3_xboole_0(B_295, '#skF_8'), '#skF_5') | ~v3_pre_topc('#skF_8', '#skF_5') | ~m1_subset_1(B_295, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_295, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_2666])).
% 27.37/17.51  tff(c_2800, plain, (~v3_pre_topc('#skF_8', '#skF_5')), inference(splitLeft, [status(thm)], [c_2707])).
% 27.37/17.51  tff(c_45869, plain, (![B_1742, A_1743, B_1744]: (v3_pre_topc(B_1742, A_1743) | ~m1_subset_1(B_1742, k1_zfmisc_1(u1_struct_0(A_1743))) | ~m1_subset_1(B_1744, u1_struct_0(A_1743)) | ~l1_pre_topc(A_1743) | ~v2_pre_topc(A_1743) | v2_struct_0(A_1743) | ~m1_subset_1(B_1742, u1_struct_0(k9_yellow_6(A_1743, B_1744))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_1743, B_1744))))), inference(resolution, [status(thm)], [c_36, c_2413])).
% 27.37/17.51  tff(c_45954, plain, (v3_pre_topc('#skF_8', '#skF_5') | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_66, c_45869])).
% 27.37/17.51  tff(c_45981, plain, (v3_pre_topc('#skF_8', '#skF_5') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_1245, c_45954])).
% 27.37/17.51  tff(c_45983, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_76, c_2800, c_45981])).
% 27.37/17.51  tff(c_77962, plain, (![B_2932]: (v3_pre_topc(k3_xboole_0(B_2932, '#skF_8'), '#skF_5') | ~m1_subset_1(B_2932, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_2932, '#skF_5'))), inference(splitRight, [status(thm)], [c_2707])).
% 27.37/17.51  tff(c_77980, plain, (v3_pre_topc(k3_xboole_0('#skF_7', '#skF_8'), '#skF_5') | ~v3_pre_topc('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_1239, c_77962])).
% 27.37/17.51  tff(c_78022, plain, (v3_pre_topc(k3_xboole_0('#skF_7', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_77037, c_77980])).
% 27.37/17.51  tff(c_77295, plain, (![C_2896, A_2897, B_2898]: (r2_hidden(C_2896, u1_struct_0(k9_yellow_6(A_2897, B_2898))) | ~v3_pre_topc(C_2896, A_2897) | ~r2_hidden(B_2898, C_2896) | ~m1_subset_1(C_2896, k1_zfmisc_1(u1_struct_0(A_2897))) | ~m1_subset_1(B_2898, u1_struct_0(A_2897)) | ~l1_pre_topc(A_2897) | ~v2_pre_topc(A_2897) | v2_struct_0(A_2897))), inference(cnfTransformation, [status(thm)], [f_133])).
% 27.37/17.51  tff(c_48, plain, (![A_30, B_31]: (m1_subset_1(A_30, B_31) | ~r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_80])).
% 27.37/17.51  tff(c_111508, plain, (![C_3926, A_3927, B_3928]: (m1_subset_1(C_3926, u1_struct_0(k9_yellow_6(A_3927, B_3928))) | ~v3_pre_topc(C_3926, A_3927) | ~r2_hidden(B_3928, C_3926) | ~m1_subset_1(C_3926, k1_zfmisc_1(u1_struct_0(A_3927))) | ~m1_subset_1(B_3928, u1_struct_0(A_3927)) | ~l1_pre_topc(A_3927) | ~v2_pre_topc(A_3927) | v2_struct_0(A_3927))), inference(resolution, [status(thm)], [c_77295, c_48])).
% 27.37/17.51  tff(c_64, plain, (~m1_subset_1(k3_xboole_0('#skF_7', '#skF_8'), u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 27.37/17.51  tff(c_111526, plain, (~v3_pre_topc(k3_xboole_0('#skF_7', '#skF_8'), '#skF_5') | ~r2_hidden('#skF_6', k3_xboole_0('#skF_7', '#skF_8')) | ~m1_subset_1(k3_xboole_0('#skF_7', '#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_111508, c_64])).
% 27.37/17.51  tff(c_111538, plain, (~r2_hidden('#skF_6', k3_xboole_0('#skF_7', '#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_1343, c_78022, c_111526])).
% 27.37/17.51  tff(c_111539, plain, (~r2_hidden('#skF_6', k3_xboole_0('#skF_7', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_76, c_111538])).
% 27.37/17.51  tff(c_111549, plain, (~r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_12, c_111539])).
% 27.37/17.51  tff(c_111557, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_97500, c_111549])).
% 27.37/17.51  tff(c_111881, plain, (![B_3940, B_3941, A_3942]: (r2_hidden(B_3940, B_3941) | ~m1_subset_1(B_3941, k1_zfmisc_1(u1_struct_0(A_3942))) | ~m1_subset_1(B_3940, u1_struct_0(A_3942)) | ~l1_pre_topc(A_3942) | ~v2_pre_topc(A_3942) | v2_struct_0(A_3942) | ~m1_subset_1(B_3941, u1_struct_0(k9_yellow_6(A_3942, B_3940))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_3942, B_3940))))), inference(resolution, [status(thm)], [c_36, c_2091])).
% 27.37/17.51  tff(c_111966, plain, (r2_hidden('#skF_6', '#skF_8') | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_66, c_111881])).
% 27.37/17.51  tff(c_111993, plain, (r2_hidden('#skF_6', '#skF_8') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_1245, c_111966])).
% 27.37/17.51  tff(c_111995, plain, $false, inference(negUnitSimplification, [status(thm)], [c_131, c_76, c_111557, c_111993])).
% 27.37/17.51  tff(c_111997, plain, (v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_123])).
% 27.37/17.51  tff(c_122, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_68, c_108])).
% 27.37/17.51  tff(c_111999, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_111997, c_122])).
% 27.37/17.51  tff(c_32, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k3_xboole_0(A_18, B_19))=A_18)), inference(cnfTransformation, [status(thm)], [f_53])).
% 27.37/17.51  tff(c_112007, plain, (![A_3945, B_3946]: (r2_hidden('#skF_2'(A_3945, B_3946), A_3945) | r1_tarski(A_3945, B_3946))), inference(cnfTransformation, [status(thm)], [f_38])).
% 27.37/17.51  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 27.37/17.51  tff(c_112049, plain, (![A_3951, B_3952]: (~v1_xboole_0(A_3951) | r1_tarski(A_3951, B_3952))), inference(resolution, [status(thm)], [c_112007, c_2])).
% 27.37/17.51  tff(c_30, plain, (![A_16, B_17]: (k2_xboole_0(A_16, B_17)=B_17 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 27.37/17.51  tff(c_112054, plain, (![A_3953, B_3954]: (k2_xboole_0(A_3953, B_3954)=B_3954 | ~v1_xboole_0(A_3953))), inference(resolution, [status(thm)], [c_112049, c_30])).
% 27.37/17.51  tff(c_112064, plain, (![B_3955]: (k2_xboole_0('#skF_7', B_3955)=B_3955)), inference(resolution, [status(thm)], [c_111999, c_112054])).
% 27.37/17.51  tff(c_112086, plain, (![B_19]: (k3_xboole_0('#skF_7', B_19)='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_32, c_112064])).
% 27.37/17.51  tff(c_38, plain, (![B_21, A_20]: (m1_subset_1(B_21, A_20) | ~v1_xboole_0(B_21) | ~v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_66])).
% 27.37/17.51  tff(c_112002, plain, (~v1_xboole_0(k3_xboole_0('#skF_7', '#skF_8')) | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_38, c_64])).
% 27.37/17.51  tff(c_112005, plain, (~v1_xboole_0(k3_xboole_0('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_111997, c_112002])).
% 27.37/17.51  tff(c_112118, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_112086, c_112005])).
% 27.37/17.51  tff(c_112122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_111999, c_112118])).
% 27.37/17.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.37/17.51  
% 27.37/17.51  Inference rules
% 27.37/17.51  ----------------------
% 27.37/17.51  #Ref     : 0
% 27.37/17.51  #Sup     : 28546
% 27.37/17.51  #Fact    : 0
% 27.37/17.51  #Define  : 0
% 27.37/17.51  #Split   : 97
% 27.37/17.51  #Chain   : 0
% 27.37/17.51  #Close   : 0
% 27.37/17.51  
% 27.37/17.51  Ordering : KBO
% 27.37/17.51  
% 27.37/17.51  Simplification rules
% 27.37/17.51  ----------------------
% 27.37/17.51  #Subsume      : 11529
% 27.37/17.51  #Demod        : 2886
% 27.37/17.51  #Tautology    : 3351
% 27.37/17.51  #SimpNegUnit  : 597
% 27.37/17.51  #BackRed      : 13
% 27.37/17.51  
% 27.37/17.51  #Partial instantiations: 0
% 27.37/17.51  #Strategies tried      : 1
% 27.37/17.51  
% 27.37/17.51  Timing (in seconds)
% 27.37/17.51  ----------------------
% 27.37/17.52  Preprocessing        : 0.35
% 27.37/17.52  Parsing              : 0.18
% 27.37/17.52  CNF conversion       : 0.03
% 27.37/17.52  Main loop            : 16.29
% 27.37/17.52  Inferencing          : 2.98
% 27.37/17.52  Reduction            : 4.06
% 27.37/17.52  Demodulation         : 2.84
% 27.37/17.52  BG Simplification    : 0.30
% 27.37/17.52  Subsumption          : 7.96
% 27.37/17.52  Abstraction          : 0.50
% 27.37/17.52  MUC search           : 0.00
% 27.37/17.52  Cooper               : 0.00
% 27.37/17.52  Total                : 16.68
% 27.37/17.52  Index Insertion      : 0.00
% 27.37/17.52  Index Deletion       : 0.00
% 27.37/17.52  Index Matching       : 0.00
% 27.37/17.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
