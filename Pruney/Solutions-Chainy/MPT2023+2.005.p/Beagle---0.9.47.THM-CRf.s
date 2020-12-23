%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:12 EST 2020

% Result     : Theorem 24.97s
% Output     : CNFRefutation 24.97s
% Verified   : 
% Statistics : Number of formulae       :  186 (1464 expanded)
%              Number of leaves         :   40 ( 534 expanded)
%              Depth                    :   18
%              Number of atoms          :  444 (5069 expanded)
%              Number of equality atoms :   13 ( 107 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_yellow_6 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k9_setfam_1 > k3_yellow_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2

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

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

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

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_161,negated_conjecture,(
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

tff(f_60,axiom,(
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

tff(f_142,axiom,(
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

tff(f_106,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_125,axiom,(
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

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_tops_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_68,plain,(
    m1_subset_1('#skF_7',u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_118,plain,(
    ! [B_73,A_74] :
      ( v1_xboole_0(B_73)
      | ~ m1_subset_1(B_73,A_74)
      | ~ v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_136,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_68,c_118])).

tff(c_164,plain,(
    ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_138,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_70,c_118])).

tff(c_144,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_32,plain,(
    ! [B_17,A_16] :
      ( r2_hidden(B_17,A_16)
      | ~ m1_subset_1(B_17,A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_202,plain,(
    ! [A_89,B_90] :
      ( r2_hidden('#skF_2'(A_89,B_90),A_89)
      | r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_14,plain,(
    ! [D_15,B_11,A_10] :
      ( r2_hidden(D_15,B_11)
      | ~ r2_hidden(D_15,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2344,plain,(
    ! [A_294,B_295,B_296] :
      ( r2_hidden('#skF_2'(k3_xboole_0(A_294,B_295),B_296),B_295)
      | r1_tarski(k3_xboole_0(A_294,B_295),B_296) ) ),
    inference(resolution,[status(thm)],[c_202,c_14])).

tff(c_74,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_72,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_828,plain,(
    ! [C_181,A_182,B_183] :
      ( m1_connsp_2(C_181,A_182,B_183)
      | ~ m1_subset_1(C_181,u1_struct_0(k9_yellow_6(A_182,B_183)))
      | ~ m1_subset_1(B_183,u1_struct_0(A_182))
      | ~ l1_pre_topc(A_182)
      | ~ v2_pre_topc(A_182)
      | v2_struct_0(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_859,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_828])).

tff(c_872,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_859])).

tff(c_873,plain,(
    m1_connsp_2('#skF_7','#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_872])).

tff(c_52,plain,(
    ! [C_34,A_31,B_32] :
      ( m1_subset_1(C_34,k1_zfmisc_1(u1_struct_0(A_31)))
      | ~ m1_connsp_2(C_34,A_31,B_32)
      | ~ m1_subset_1(B_32,u1_struct_0(A_31))
      | ~ l1_pre_topc(A_31)
      | ~ v2_pre_topc(A_31)
      | v2_struct_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_879,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_873,c_52])).

tff(c_882,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_879])).

tff(c_883,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_882])).

tff(c_46,plain,(
    ! [A_24,C_26,B_25] :
      ( m1_subset_1(A_24,C_26)
      | ~ m1_subset_1(B_25,k1_zfmisc_1(C_26))
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_950,plain,(
    ! [A_187] :
      ( m1_subset_1(A_187,u1_struct_0('#skF_5'))
      | ~ r2_hidden(A_187,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_883,c_46])).

tff(c_185,plain,(
    ! [A_84,B_85] :
      ( ~ r2_hidden('#skF_2'(A_84,B_85),B_85)
      | r1_tarski(A_84,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_190,plain,(
    ! [A_84,A_16] :
      ( r1_tarski(A_84,A_16)
      | ~ m1_subset_1('#skF_2'(A_84,A_16),A_16)
      | v1_xboole_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_32,c_185])).

tff(c_954,plain,(
    ! [A_84] :
      ( r1_tarski(A_84,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(A_84,u1_struct_0('#skF_5')),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_950,c_190])).

tff(c_960,plain,(
    ! [A_84] :
      ( r1_tarski(A_84,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_2'(A_84,u1_struct_0('#skF_5')),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_954])).

tff(c_2390,plain,(
    ! [A_294] : r1_tarski(k3_xboole_0(A_294,'#skF_7'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2344,c_960])).

tff(c_372,plain,(
    ! [D_121,A_122,B_123] :
      ( r2_hidden(D_121,k3_xboole_0(A_122,B_123))
      | ~ r2_hidden(D_121,B_123)
      | ~ r2_hidden(D_121,A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_70861,plain,(
    ! [D_2734,B_2735,A_2736,B_2737] :
      ( r2_hidden(D_2734,B_2735)
      | ~ r1_tarski(k3_xboole_0(A_2736,B_2737),B_2735)
      | ~ r2_hidden(D_2734,B_2737)
      | ~ r2_hidden(D_2734,A_2736) ) ),
    inference(resolution,[status(thm)],[c_372,c_6])).

tff(c_71015,plain,(
    ! [D_2744,A_2745] :
      ( r2_hidden(D_2744,u1_struct_0('#skF_5'))
      | ~ r2_hidden(D_2744,'#skF_7')
      | ~ r2_hidden(D_2744,A_2745) ) ),
    inference(resolution,[status(thm)],[c_2390,c_70861])).

tff(c_76419,plain,(
    ! [B_2994,A_2995] :
      ( r2_hidden(B_2994,u1_struct_0('#skF_5'))
      | ~ r2_hidden(B_2994,'#skF_7')
      | ~ m1_subset_1(B_2994,A_2995)
      | v1_xboole_0(A_2995) ) ),
    inference(resolution,[status(thm)],[c_32,c_71015])).

tff(c_76499,plain,
    ( r2_hidden('#skF_6',u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_6','#skF_7')
    | v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_70,c_76419])).

tff(c_76565,plain,
    ( r2_hidden('#skF_6',u1_struct_0('#skF_5'))
    | ~ r2_hidden('#skF_6','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_76499])).

tff(c_76566,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_76565])).

tff(c_2252,plain,(
    ! [B_289,C_290,A_291] :
      ( r2_hidden(B_289,C_290)
      | ~ r2_hidden(C_290,u1_struct_0(k9_yellow_6(A_291,B_289)))
      | ~ m1_subset_1(C_290,k1_zfmisc_1(u1_struct_0(A_291)))
      | ~ m1_subset_1(B_289,u1_struct_0(A_291))
      | ~ l1_pre_topc(A_291)
      | ~ v2_pre_topc(A_291)
      | v2_struct_0(A_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_89879,plain,(
    ! [B_3382,B_3383,A_3384] :
      ( r2_hidden(B_3382,B_3383)
      | ~ m1_subset_1(B_3383,k1_zfmisc_1(u1_struct_0(A_3384)))
      | ~ m1_subset_1(B_3382,u1_struct_0(A_3384))
      | ~ l1_pre_topc(A_3384)
      | ~ v2_pre_topc(A_3384)
      | v2_struct_0(A_3384)
      | ~ m1_subset_1(B_3383,u1_struct_0(k9_yellow_6(A_3384,B_3382)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_3384,B_3382))) ) ),
    inference(resolution,[status(thm)],[c_32,c_2252])).

tff(c_89969,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_68,c_89879])).

tff(c_89997,plain,
    ( r2_hidden('#skF_6','#skF_7')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_883,c_89969])).

tff(c_89999,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_76,c_76566,c_89997])).

tff(c_90001,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_76565])).

tff(c_12,plain,(
    ! [D_15,A_10,B_11] :
      ( r2_hidden(D_15,k3_xboole_0(A_10,B_11))
      | ~ r2_hidden(D_15,B_11)
      | ~ r2_hidden(D_15,A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [D_15,A_10,B_11] :
      ( r2_hidden(D_15,A_10)
      | ~ r2_hidden(D_15,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_70628,plain,(
    ! [A_2718,B_2719,B_2720] :
      ( r2_hidden('#skF_2'(k3_xboole_0(A_2718,B_2719),B_2720),A_2718)
      | r1_tarski(k3_xboole_0(A_2718,B_2719),B_2720) ) ),
    inference(resolution,[status(thm)],[c_202,c_16])).

tff(c_70674,plain,(
    ! [B_2719] : r1_tarski(k3_xboole_0('#skF_7',B_2719),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_70628,c_960])).

tff(c_44,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(A_22,k1_zfmisc_1(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2529,plain,(
    ! [B_307,C_308,A_309] :
      ( v3_pre_topc(k3_xboole_0(B_307,C_308),A_309)
      | ~ m1_subset_1(C_308,k1_zfmisc_1(u1_struct_0(A_309)))
      | ~ v3_pre_topc(C_308,A_309)
      | ~ m1_subset_1(B_307,k1_zfmisc_1(u1_struct_0(A_309)))
      | ~ v3_pre_topc(B_307,A_309)
      | ~ l1_pre_topc(A_309)
      | ~ v2_pre_topc(A_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_2533,plain,(
    ! [B_307] :
      ( v3_pre_topc(k3_xboole_0(B_307,'#skF_7'),'#skF_5')
      | ~ v3_pre_topc('#skF_7','#skF_5')
      | ~ m1_subset_1(B_307,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_307,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_883,c_2529])).

tff(c_2565,plain,(
    ! [B_307] :
      ( v3_pre_topc(k3_xboole_0(B_307,'#skF_7'),'#skF_5')
      | ~ v3_pre_topc('#skF_7','#skF_5')
      | ~ m1_subset_1(B_307,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_307,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_2533])).

tff(c_53130,plain,(
    ~ v3_pre_topc('#skF_7','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2565])).

tff(c_2091,plain,(
    ! [C_276,A_277,B_278] :
      ( v3_pre_topc(C_276,A_277)
      | ~ r2_hidden(C_276,u1_struct_0(k9_yellow_6(A_277,B_278)))
      | ~ m1_subset_1(C_276,k1_zfmisc_1(u1_struct_0(A_277)))
      | ~ m1_subset_1(B_278,u1_struct_0(A_277))
      | ~ l1_pre_topc(A_277)
      | ~ v2_pre_topc(A_277)
      | v2_struct_0(A_277) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_70155,plain,(
    ! [B_2671,A_2672,B_2673] :
      ( v3_pre_topc(B_2671,A_2672)
      | ~ m1_subset_1(B_2671,k1_zfmisc_1(u1_struct_0(A_2672)))
      | ~ m1_subset_1(B_2673,u1_struct_0(A_2672))
      | ~ l1_pre_topc(A_2672)
      | ~ v2_pre_topc(A_2672)
      | v2_struct_0(A_2672)
      | ~ m1_subset_1(B_2671,u1_struct_0(k9_yellow_6(A_2672,B_2673)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_2672,B_2673))) ) ),
    inference(resolution,[status(thm)],[c_32,c_2091])).

tff(c_70241,plain,
    ( v3_pre_topc('#skF_7','#skF_5')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_68,c_70155])).

tff(c_70268,plain,
    ( v3_pre_topc('#skF_7','#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_883,c_70241])).

tff(c_70270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_76,c_53130,c_70268])).

tff(c_70272,plain,(
    v3_pre_topc('#skF_7','#skF_5') ),
    inference(splitRight,[status(thm)],[c_2565])).

tff(c_66,plain,(
    m1_subset_1('#skF_8',u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_862,plain,
    ( m1_connsp_2('#skF_8','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_828])).

tff(c_876,plain,
    ( m1_connsp_2('#skF_8','#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_862])).

tff(c_877,plain,(
    m1_connsp_2('#skF_8','#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_876])).

tff(c_885,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_877,c_52])).

tff(c_888,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_885])).

tff(c_889,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_888])).

tff(c_2531,plain,(
    ! [B_307] :
      ( v3_pre_topc(k3_xboole_0(B_307,'#skF_8'),'#skF_5')
      | ~ v3_pre_topc('#skF_8','#skF_5')
      | ~ m1_subset_1(B_307,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_307,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_889,c_2529])).

tff(c_2562,plain,(
    ! [B_307] :
      ( v3_pre_topc(k3_xboole_0(B_307,'#skF_8'),'#skF_5')
      | ~ v3_pre_topc('#skF_8','#skF_5')
      | ~ m1_subset_1(B_307,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_307,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_2531])).

tff(c_2614,plain,(
    ~ v3_pre_topc('#skF_8','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2562])).

tff(c_52925,plain,(
    ! [B_2178,A_2179,B_2180] :
      ( v3_pre_topc(B_2178,A_2179)
      | ~ m1_subset_1(B_2178,k1_zfmisc_1(u1_struct_0(A_2179)))
      | ~ m1_subset_1(B_2180,u1_struct_0(A_2179))
      | ~ l1_pre_topc(A_2179)
      | ~ v2_pre_topc(A_2179)
      | v2_struct_0(A_2179)
      | ~ m1_subset_1(B_2178,u1_struct_0(k9_yellow_6(A_2179,B_2180)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_2179,B_2180))) ) ),
    inference(resolution,[status(thm)],[c_32,c_2091])).

tff(c_53010,plain,
    ( v3_pre_topc('#skF_8','#skF_5')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_66,c_52925])).

tff(c_53037,plain,
    ( v3_pre_topc('#skF_8','#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_889,c_53010])).

tff(c_53039,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_76,c_2614,c_53037])).

tff(c_70299,plain,(
    ! [B_2681] :
      ( v3_pre_topc(k3_xboole_0(B_2681,'#skF_8'),'#skF_5')
      | ~ m1_subset_1(B_2681,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ v3_pre_topc(B_2681,'#skF_5') ) ),
    inference(splitRight,[status(thm)],[c_2562])).

tff(c_70305,plain,
    ( v3_pre_topc(k3_xboole_0('#skF_7','#skF_8'),'#skF_5')
    | ~ v3_pre_topc('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_883,c_70299])).

tff(c_70343,plain,(
    v3_pre_topc(k3_xboole_0('#skF_7','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70272,c_70305])).

tff(c_70424,plain,(
    ! [C_2692,A_2693,B_2694] :
      ( r2_hidden(C_2692,u1_struct_0(k9_yellow_6(A_2693,B_2694)))
      | ~ v3_pre_topc(C_2692,A_2693)
      | ~ r2_hidden(B_2694,C_2692)
      | ~ m1_subset_1(C_2692,k1_zfmisc_1(u1_struct_0(A_2693)))
      | ~ m1_subset_1(B_2694,u1_struct_0(A_2693))
      | ~ l1_pre_topc(A_2693)
      | ~ v2_pre_topc(A_2693)
      | v2_struct_0(A_2693) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_40,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,B_21)
      | ~ r2_hidden(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_99679,plain,(
    ! [C_3563,A_3564,B_3565] :
      ( m1_subset_1(C_3563,u1_struct_0(k9_yellow_6(A_3564,B_3565)))
      | ~ v3_pre_topc(C_3563,A_3564)
      | ~ r2_hidden(B_3565,C_3563)
      | ~ m1_subset_1(C_3563,k1_zfmisc_1(u1_struct_0(A_3564)))
      | ~ m1_subset_1(B_3565,u1_struct_0(A_3564))
      | ~ l1_pre_topc(A_3564)
      | ~ v2_pre_topc(A_3564)
      | v2_struct_0(A_3564) ) ),
    inference(resolution,[status(thm)],[c_70424,c_40])).

tff(c_64,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_7','#skF_8'),u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_99701,plain,
    ( ~ v3_pre_topc(k3_xboole_0('#skF_7','#skF_8'),'#skF_5')
    | ~ r2_hidden('#skF_6',k3_xboole_0('#skF_7','#skF_8'))
    | ~ m1_subset_1(k3_xboole_0('#skF_7','#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_99679,c_64])).

tff(c_99715,plain,
    ( ~ r2_hidden('#skF_6',k3_xboole_0('#skF_7','#skF_8'))
    | ~ m1_subset_1(k3_xboole_0('#skF_7','#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_70343,c_99701])).

tff(c_99716,plain,
    ( ~ r2_hidden('#skF_6',k3_xboole_0('#skF_7','#skF_8'))
    | ~ m1_subset_1(k3_xboole_0('#skF_7','#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_99715])).

tff(c_99749,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_7','#skF_8'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_99716])).

tff(c_99758,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_7','#skF_8'),u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_44,c_99749])).

tff(c_99764,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70674,c_99758])).

tff(c_99765,plain,(
    ~ r2_hidden('#skF_6',k3_xboole_0('#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_99716])).

tff(c_99775,plain,
    ( ~ r2_hidden('#skF_6','#skF_8')
    | ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_99765])).

tff(c_99783,plain,(
    ~ r2_hidden('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90001,c_99775])).

tff(c_100281,plain,(
    ! [B_3571,B_3572,A_3573] :
      ( r2_hidden(B_3571,B_3572)
      | ~ m1_subset_1(B_3572,k1_zfmisc_1(u1_struct_0(A_3573)))
      | ~ m1_subset_1(B_3571,u1_struct_0(A_3573))
      | ~ l1_pre_topc(A_3573)
      | ~ v2_pre_topc(A_3573)
      | v2_struct_0(A_3573)
      | ~ m1_subset_1(B_3572,u1_struct_0(k9_yellow_6(A_3573,B_3571)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_3573,B_3571))) ) ),
    inference(resolution,[status(thm)],[c_32,c_2252])).

tff(c_100366,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_66,c_100281])).

tff(c_100393,plain,
    ( r2_hidden('#skF_6','#skF_8')
    | v2_struct_0('#skF_5')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_889,c_100366])).

tff(c_100395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_76,c_99783,c_100393])).

tff(c_100397,plain,(
    v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_137,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_66,c_118])).

tff(c_100399,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100397,c_137])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100402,plain,(
    ! [D_3574,B_3575,A_3576] :
      ( r2_hidden(D_3574,B_3575)
      | ~ r2_hidden(D_3574,k3_xboole_0(A_3576,B_3575)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_100611,plain,(
    ! [A_3615,B_3616] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_3615,B_3616)),B_3616)
      | v1_xboole_0(k3_xboole_0(A_3615,B_3616)) ) ),
    inference(resolution,[status(thm)],[c_4,c_100402])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_100636,plain,(
    ! [B_3617,A_3618] :
      ( ~ v1_xboole_0(B_3617)
      | v1_xboole_0(k3_xboole_0(A_3618,B_3617)) ) ),
    inference(resolution,[status(thm)],[c_100611,c_2])).

tff(c_34,plain,(
    ! [B_17,A_16] :
      ( m1_subset_1(B_17,A_16)
      | ~ v1_xboole_0(B_17)
      | ~ v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_163,plain,
    ( ~ v1_xboole_0(k3_xboole_0('#skF_7','#skF_8'))
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_34,c_64])).

tff(c_100401,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100397,c_163])).

tff(c_100639,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_100636,c_100401])).

tff(c_100643,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100399,c_100639])).

tff(c_100645,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_101329,plain,(
    ! [C_3723,A_3724,B_3725] :
      ( m1_connsp_2(C_3723,A_3724,B_3725)
      | ~ m1_subset_1(C_3723,u1_struct_0(k9_yellow_6(A_3724,B_3725)))
      | ~ m1_subset_1(B_3725,u1_struct_0(A_3724))
      | ~ l1_pre_topc(A_3724)
      | ~ v2_pre_topc(A_3724)
      | v2_struct_0(A_3724) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_101363,plain,
    ( m1_connsp_2('#skF_8','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_101329])).

tff(c_101377,plain,
    ( m1_connsp_2('#skF_8','#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_101363])).

tff(c_101378,plain,(
    m1_connsp_2('#skF_8','#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_101377])).

tff(c_101386,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_101378,c_52])).

tff(c_101389,plain,
    ( m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_101386])).

tff(c_101390,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_101389])).

tff(c_42,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_101411,plain,(
    r1_tarski('#skF_8',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_101390,c_42])).

tff(c_100739,plain,(
    ! [C_3638,B_3639,A_3640] :
      ( r2_hidden(C_3638,B_3639)
      | ~ r2_hidden(C_3638,A_3640)
      | ~ r1_tarski(A_3640,B_3639) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_100751,plain,(
    ! [A_3644,B_3645] :
      ( r2_hidden('#skF_1'(A_3644),B_3645)
      | ~ r1_tarski(A_3644,B_3645)
      | v1_xboole_0(A_3644) ) ),
    inference(resolution,[status(thm)],[c_4,c_100739])).

tff(c_100772,plain,(
    ! [B_3645,A_3644] :
      ( ~ v1_xboole_0(B_3645)
      | ~ r1_tarski(A_3644,B_3645)
      | v1_xboole_0(A_3644) ) ),
    inference(resolution,[status(thm)],[c_100751,c_2])).

tff(c_101467,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_5'))
    | v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_101411,c_100772])).

tff(c_101475,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100645,c_101467])).

tff(c_100644,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_101118,plain,(
    ! [A_3699,B_3700,C_3701] :
      ( r2_hidden('#skF_3'(A_3699,B_3700,C_3701),B_3700)
      | r2_hidden('#skF_4'(A_3699,B_3700,C_3701),C_3701)
      | k3_xboole_0(A_3699,B_3700) = C_3701 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_101757,plain,(
    ! [C_3753,A_3754,B_3755] :
      ( ~ v1_xboole_0(C_3753)
      | r2_hidden('#skF_3'(A_3754,B_3755,C_3753),B_3755)
      | k3_xboole_0(A_3754,B_3755) = C_3753 ) ),
    inference(resolution,[status(thm)],[c_101118,c_2])).

tff(c_101802,plain,(
    ! [B_3758,C_3759,A_3760] :
      ( ~ v1_xboole_0(B_3758)
      | ~ v1_xboole_0(C_3759)
      | k3_xboole_0(A_3760,B_3758) = C_3759 ) ),
    inference(resolution,[status(thm)],[c_101757,c_2])).

tff(c_101854,plain,(
    ! [C_3761,A_3762] :
      ( ~ v1_xboole_0(C_3761)
      | k3_xboole_0(A_3762,'#skF_6') = C_3761 ) ),
    inference(resolution,[status(thm)],[c_100644,c_101802])).

tff(c_101905,plain,(
    ! [A_3762] : k3_xboole_0(A_3762,'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_100644,c_101854])).

tff(c_101853,plain,(
    ! [C_3759,A_3760] :
      ( ~ v1_xboole_0(C_3759)
      | k3_xboole_0(A_3760,'#skF_6') = C_3759 ) ),
    inference(resolution,[status(thm)],[c_100644,c_101802])).

tff(c_101969,plain,(
    ! [C_3764] :
      ( ~ v1_xboole_0(C_3764)
      | C_3764 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101905,c_101853])).

tff(c_102030,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_101475,c_101969])).

tff(c_101360,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_101329])).

tff(c_101373,plain,
    ( m1_connsp_2('#skF_7','#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_101360])).

tff(c_101374,plain,(
    m1_connsp_2('#skF_7','#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_101373])).

tff(c_101380,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_101374,c_52])).

tff(c_101383,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5')))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_70,c_101380])).

tff(c_101384,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_101383])).

tff(c_101400,plain,(
    r1_tarski('#skF_7',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_101384,c_42])).

tff(c_101421,plain,
    ( ~ v1_xboole_0(u1_struct_0('#skF_5'))
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_101400,c_100772])).

tff(c_101429,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_100645,c_101421])).

tff(c_102031,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_101429,c_101969])).

tff(c_102120,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102030,c_102031])).

tff(c_102046,plain,(
    m1_subset_1('#skF_7',u1_struct_0(k9_yellow_6('#skF_5','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102030,c_68])).

tff(c_102153,plain,(
    m1_subset_1('#skF_8',u1_struct_0(k9_yellow_6('#skF_5','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102120,c_102046])).

tff(c_101898,plain,(
    ! [A_3762] : k3_xboole_0(A_3762,'#skF_6') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_101475,c_101854])).

tff(c_102186,plain,(
    ! [A_3762] : k3_xboole_0(A_3762,'#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102030,c_101898])).

tff(c_102044,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_7','#skF_8'),u1_struct_0(k9_yellow_6('#skF_5','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102030,c_64])).

tff(c_102503,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102153,c_102186,c_102120,c_102044])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:20:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.97/16.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.97/16.16  
% 24.97/16.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.97/16.17  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k9_yellow_6 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k9_setfam_1 > k3_yellow_1 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2
% 24.97/16.17  
% 24.97/16.17  %Foreground sorts:
% 24.97/16.17  
% 24.97/16.17  
% 24.97/16.17  %Background operators:
% 24.97/16.17  
% 24.97/16.17  
% 24.97/16.17  %Foreground operators:
% 24.97/16.17  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 24.97/16.17  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 24.97/16.17  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 24.97/16.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.97/16.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 24.97/16.17  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 24.97/16.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 24.97/16.17  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 24.97/16.17  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 24.97/16.17  tff('#skF_7', type, '#skF_7': $i).
% 24.97/16.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.97/16.17  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 24.97/16.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 24.97/16.17  tff('#skF_5', type, '#skF_5': $i).
% 24.97/16.17  tff('#skF_6', type, '#skF_6': $i).
% 24.97/16.17  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 24.97/16.17  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 24.97/16.17  tff('#skF_8', type, '#skF_8': $i).
% 24.97/16.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.97/16.17  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 24.97/16.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.97/16.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 24.97/16.17  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 24.97/16.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 24.97/16.17  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 24.97/16.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 24.97/16.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 24.97/16.17  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 24.97/16.17  
% 24.97/16.19  tff(f_161, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k3_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_waybel_9)).
% 24.97/16.19  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 24.97/16.19  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 24.97/16.19  tff(f_47, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 24.97/16.19  tff(f_142, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => m1_connsp_2(C, A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_waybel_9)).
% 24.97/16.19  tff(f_106, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 24.97/16.19  tff(f_76, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 24.97/16.19  tff(f_125, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_yellow_6)).
% 24.97/16.19  tff(f_70, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 24.97/16.19  tff(f_92, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_tops_1)).
% 24.97/16.19  tff(f_66, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 24.97/16.19  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 24.97/16.19  tff(c_68, plain, (m1_subset_1('#skF_7', u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 24.97/16.19  tff(c_118, plain, (![B_73, A_74]: (v1_xboole_0(B_73) | ~m1_subset_1(B_73, A_74) | ~v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_60])).
% 24.97/16.19  tff(c_136, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_68, c_118])).
% 24.97/16.19  tff(c_164, plain, (~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(splitLeft, [status(thm)], [c_136])).
% 24.97/16.19  tff(c_76, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_161])).
% 24.97/16.19  tff(c_70, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 24.97/16.19  tff(c_138, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_118])).
% 24.97/16.19  tff(c_144, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_138])).
% 24.97/16.19  tff(c_32, plain, (![B_17, A_16]: (r2_hidden(B_17, A_16) | ~m1_subset_1(B_17, A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 24.97/16.19  tff(c_202, plain, (![A_89, B_90]: (r2_hidden('#skF_2'(A_89, B_90), A_89) | r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_38])).
% 24.97/16.19  tff(c_14, plain, (![D_15, B_11, A_10]: (r2_hidden(D_15, B_11) | ~r2_hidden(D_15, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 24.97/16.19  tff(c_2344, plain, (![A_294, B_295, B_296]: (r2_hidden('#skF_2'(k3_xboole_0(A_294, B_295), B_296), B_295) | r1_tarski(k3_xboole_0(A_294, B_295), B_296))), inference(resolution, [status(thm)], [c_202, c_14])).
% 24.97/16.19  tff(c_74, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_161])).
% 24.97/16.19  tff(c_72, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_161])).
% 24.97/16.19  tff(c_828, plain, (![C_181, A_182, B_183]: (m1_connsp_2(C_181, A_182, B_183) | ~m1_subset_1(C_181, u1_struct_0(k9_yellow_6(A_182, B_183))) | ~m1_subset_1(B_183, u1_struct_0(A_182)) | ~l1_pre_topc(A_182) | ~v2_pre_topc(A_182) | v2_struct_0(A_182))), inference(cnfTransformation, [status(thm)], [f_142])).
% 24.97/16.19  tff(c_859, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_68, c_828])).
% 24.97/16.20  tff(c_872, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_859])).
% 24.97/16.20  tff(c_873, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_76, c_872])).
% 24.97/16.20  tff(c_52, plain, (![C_34, A_31, B_32]: (m1_subset_1(C_34, k1_zfmisc_1(u1_struct_0(A_31))) | ~m1_connsp_2(C_34, A_31, B_32) | ~m1_subset_1(B_32, u1_struct_0(A_31)) | ~l1_pre_topc(A_31) | ~v2_pre_topc(A_31) | v2_struct_0(A_31))), inference(cnfTransformation, [status(thm)], [f_106])).
% 24.97/16.20  tff(c_879, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_873, c_52])).
% 24.97/16.20  tff(c_882, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_879])).
% 24.97/16.20  tff(c_883, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_76, c_882])).
% 24.97/16.20  tff(c_46, plain, (![A_24, C_26, B_25]: (m1_subset_1(A_24, C_26) | ~m1_subset_1(B_25, k1_zfmisc_1(C_26)) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_76])).
% 24.97/16.20  tff(c_950, plain, (![A_187]: (m1_subset_1(A_187, u1_struct_0('#skF_5')) | ~r2_hidden(A_187, '#skF_7'))), inference(resolution, [status(thm)], [c_883, c_46])).
% 24.97/16.20  tff(c_185, plain, (![A_84, B_85]: (~r2_hidden('#skF_2'(A_84, B_85), B_85) | r1_tarski(A_84, B_85))), inference(cnfTransformation, [status(thm)], [f_38])).
% 24.97/16.20  tff(c_190, plain, (![A_84, A_16]: (r1_tarski(A_84, A_16) | ~m1_subset_1('#skF_2'(A_84, A_16), A_16) | v1_xboole_0(A_16))), inference(resolution, [status(thm)], [c_32, c_185])).
% 24.97/16.20  tff(c_954, plain, (![A_84]: (r1_tarski(A_84, u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(A_84, u1_struct_0('#skF_5')), '#skF_7'))), inference(resolution, [status(thm)], [c_950, c_190])).
% 24.97/16.20  tff(c_960, plain, (![A_84]: (r1_tarski(A_84, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_2'(A_84, u1_struct_0('#skF_5')), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_144, c_954])).
% 24.97/16.20  tff(c_2390, plain, (![A_294]: (r1_tarski(k3_xboole_0(A_294, '#skF_7'), u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_2344, c_960])).
% 24.97/16.20  tff(c_372, plain, (![D_121, A_122, B_123]: (r2_hidden(D_121, k3_xboole_0(A_122, B_123)) | ~r2_hidden(D_121, B_123) | ~r2_hidden(D_121, A_122))), inference(cnfTransformation, [status(thm)], [f_47])).
% 24.97/16.20  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 24.97/16.20  tff(c_70861, plain, (![D_2734, B_2735, A_2736, B_2737]: (r2_hidden(D_2734, B_2735) | ~r1_tarski(k3_xboole_0(A_2736, B_2737), B_2735) | ~r2_hidden(D_2734, B_2737) | ~r2_hidden(D_2734, A_2736))), inference(resolution, [status(thm)], [c_372, c_6])).
% 24.97/16.20  tff(c_71015, plain, (![D_2744, A_2745]: (r2_hidden(D_2744, u1_struct_0('#skF_5')) | ~r2_hidden(D_2744, '#skF_7') | ~r2_hidden(D_2744, A_2745))), inference(resolution, [status(thm)], [c_2390, c_70861])).
% 24.97/16.20  tff(c_76419, plain, (![B_2994, A_2995]: (r2_hidden(B_2994, u1_struct_0('#skF_5')) | ~r2_hidden(B_2994, '#skF_7') | ~m1_subset_1(B_2994, A_2995) | v1_xboole_0(A_2995))), inference(resolution, [status(thm)], [c_32, c_71015])).
% 24.97/16.20  tff(c_76499, plain, (r2_hidden('#skF_6', u1_struct_0('#skF_5')) | ~r2_hidden('#skF_6', '#skF_7') | v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_70, c_76419])).
% 24.97/16.20  tff(c_76565, plain, (r2_hidden('#skF_6', u1_struct_0('#skF_5')) | ~r2_hidden('#skF_6', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_144, c_76499])).
% 24.97/16.20  tff(c_76566, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(splitLeft, [status(thm)], [c_76565])).
% 24.97/16.20  tff(c_2252, plain, (![B_289, C_290, A_291]: (r2_hidden(B_289, C_290) | ~r2_hidden(C_290, u1_struct_0(k9_yellow_6(A_291, B_289))) | ~m1_subset_1(C_290, k1_zfmisc_1(u1_struct_0(A_291))) | ~m1_subset_1(B_289, u1_struct_0(A_291)) | ~l1_pre_topc(A_291) | ~v2_pre_topc(A_291) | v2_struct_0(A_291))), inference(cnfTransformation, [status(thm)], [f_125])).
% 24.97/16.20  tff(c_89879, plain, (![B_3382, B_3383, A_3384]: (r2_hidden(B_3382, B_3383) | ~m1_subset_1(B_3383, k1_zfmisc_1(u1_struct_0(A_3384))) | ~m1_subset_1(B_3382, u1_struct_0(A_3384)) | ~l1_pre_topc(A_3384) | ~v2_pre_topc(A_3384) | v2_struct_0(A_3384) | ~m1_subset_1(B_3383, u1_struct_0(k9_yellow_6(A_3384, B_3382))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_3384, B_3382))))), inference(resolution, [status(thm)], [c_32, c_2252])).
% 24.97/16.20  tff(c_89969, plain, (r2_hidden('#skF_6', '#skF_7') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_68, c_89879])).
% 24.97/16.20  tff(c_89997, plain, (r2_hidden('#skF_6', '#skF_7') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_883, c_89969])).
% 24.97/16.20  tff(c_89999, plain, $false, inference(negUnitSimplification, [status(thm)], [c_164, c_76, c_76566, c_89997])).
% 24.97/16.20  tff(c_90001, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_76565])).
% 24.97/16.20  tff(c_12, plain, (![D_15, A_10, B_11]: (r2_hidden(D_15, k3_xboole_0(A_10, B_11)) | ~r2_hidden(D_15, B_11) | ~r2_hidden(D_15, A_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 24.97/16.20  tff(c_16, plain, (![D_15, A_10, B_11]: (r2_hidden(D_15, A_10) | ~r2_hidden(D_15, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 24.97/16.20  tff(c_70628, plain, (![A_2718, B_2719, B_2720]: (r2_hidden('#skF_2'(k3_xboole_0(A_2718, B_2719), B_2720), A_2718) | r1_tarski(k3_xboole_0(A_2718, B_2719), B_2720))), inference(resolution, [status(thm)], [c_202, c_16])).
% 24.97/16.20  tff(c_70674, plain, (![B_2719]: (r1_tarski(k3_xboole_0('#skF_7', B_2719), u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_70628, c_960])).
% 24.97/16.20  tff(c_44, plain, (![A_22, B_23]: (m1_subset_1(A_22, k1_zfmisc_1(B_23)) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_70])).
% 24.97/16.20  tff(c_2529, plain, (![B_307, C_308, A_309]: (v3_pre_topc(k3_xboole_0(B_307, C_308), A_309) | ~m1_subset_1(C_308, k1_zfmisc_1(u1_struct_0(A_309))) | ~v3_pre_topc(C_308, A_309) | ~m1_subset_1(B_307, k1_zfmisc_1(u1_struct_0(A_309))) | ~v3_pre_topc(B_307, A_309) | ~l1_pre_topc(A_309) | ~v2_pre_topc(A_309))), inference(cnfTransformation, [status(thm)], [f_92])).
% 24.97/16.20  tff(c_2533, plain, (![B_307]: (v3_pre_topc(k3_xboole_0(B_307, '#skF_7'), '#skF_5') | ~v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1(B_307, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_307, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_883, c_2529])).
% 24.97/16.20  tff(c_2565, plain, (![B_307]: (v3_pre_topc(k3_xboole_0(B_307, '#skF_7'), '#skF_5') | ~v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1(B_307, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_307, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_2533])).
% 24.97/16.20  tff(c_53130, plain, (~v3_pre_topc('#skF_7', '#skF_5')), inference(splitLeft, [status(thm)], [c_2565])).
% 24.97/16.20  tff(c_2091, plain, (![C_276, A_277, B_278]: (v3_pre_topc(C_276, A_277) | ~r2_hidden(C_276, u1_struct_0(k9_yellow_6(A_277, B_278))) | ~m1_subset_1(C_276, k1_zfmisc_1(u1_struct_0(A_277))) | ~m1_subset_1(B_278, u1_struct_0(A_277)) | ~l1_pre_topc(A_277) | ~v2_pre_topc(A_277) | v2_struct_0(A_277))), inference(cnfTransformation, [status(thm)], [f_125])).
% 24.97/16.20  tff(c_70155, plain, (![B_2671, A_2672, B_2673]: (v3_pre_topc(B_2671, A_2672) | ~m1_subset_1(B_2671, k1_zfmisc_1(u1_struct_0(A_2672))) | ~m1_subset_1(B_2673, u1_struct_0(A_2672)) | ~l1_pre_topc(A_2672) | ~v2_pre_topc(A_2672) | v2_struct_0(A_2672) | ~m1_subset_1(B_2671, u1_struct_0(k9_yellow_6(A_2672, B_2673))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_2672, B_2673))))), inference(resolution, [status(thm)], [c_32, c_2091])).
% 24.97/16.20  tff(c_70241, plain, (v3_pre_topc('#skF_7', '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_68, c_70155])).
% 24.97/16.20  tff(c_70268, plain, (v3_pre_topc('#skF_7', '#skF_5') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_883, c_70241])).
% 24.97/16.20  tff(c_70270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_164, c_76, c_53130, c_70268])).
% 24.97/16.20  tff(c_70272, plain, (v3_pre_topc('#skF_7', '#skF_5')), inference(splitRight, [status(thm)], [c_2565])).
% 24.97/16.20  tff(c_66, plain, (m1_subset_1('#skF_8', u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 24.97/16.20  tff(c_862, plain, (m1_connsp_2('#skF_8', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_828])).
% 24.97/16.20  tff(c_876, plain, (m1_connsp_2('#skF_8', '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_862])).
% 24.97/16.20  tff(c_877, plain, (m1_connsp_2('#skF_8', '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_76, c_876])).
% 24.97/16.20  tff(c_885, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_877, c_52])).
% 24.97/16.20  tff(c_888, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_885])).
% 24.97/16.20  tff(c_889, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_76, c_888])).
% 24.97/16.20  tff(c_2531, plain, (![B_307]: (v3_pre_topc(k3_xboole_0(B_307, '#skF_8'), '#skF_5') | ~v3_pre_topc('#skF_8', '#skF_5') | ~m1_subset_1(B_307, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_307, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_889, c_2529])).
% 24.97/16.20  tff(c_2562, plain, (![B_307]: (v3_pre_topc(k3_xboole_0(B_307, '#skF_8'), '#skF_5') | ~v3_pre_topc('#skF_8', '#skF_5') | ~m1_subset_1(B_307, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_307, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_2531])).
% 24.97/16.20  tff(c_2614, plain, (~v3_pre_topc('#skF_8', '#skF_5')), inference(splitLeft, [status(thm)], [c_2562])).
% 24.97/16.20  tff(c_52925, plain, (![B_2178, A_2179, B_2180]: (v3_pre_topc(B_2178, A_2179) | ~m1_subset_1(B_2178, k1_zfmisc_1(u1_struct_0(A_2179))) | ~m1_subset_1(B_2180, u1_struct_0(A_2179)) | ~l1_pre_topc(A_2179) | ~v2_pre_topc(A_2179) | v2_struct_0(A_2179) | ~m1_subset_1(B_2178, u1_struct_0(k9_yellow_6(A_2179, B_2180))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_2179, B_2180))))), inference(resolution, [status(thm)], [c_32, c_2091])).
% 24.97/16.20  tff(c_53010, plain, (v3_pre_topc('#skF_8', '#skF_5') | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_66, c_52925])).
% 24.97/16.20  tff(c_53037, plain, (v3_pre_topc('#skF_8', '#skF_5') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_889, c_53010])).
% 24.97/16.20  tff(c_53039, plain, $false, inference(negUnitSimplification, [status(thm)], [c_164, c_76, c_2614, c_53037])).
% 24.97/16.20  tff(c_70299, plain, (![B_2681]: (v3_pre_topc(k3_xboole_0(B_2681, '#skF_8'), '#skF_5') | ~m1_subset_1(B_2681, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~v3_pre_topc(B_2681, '#skF_5'))), inference(splitRight, [status(thm)], [c_2562])).
% 24.97/16.20  tff(c_70305, plain, (v3_pre_topc(k3_xboole_0('#skF_7', '#skF_8'), '#skF_5') | ~v3_pre_topc('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_883, c_70299])).
% 24.97/16.20  tff(c_70343, plain, (v3_pre_topc(k3_xboole_0('#skF_7', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70272, c_70305])).
% 24.97/16.20  tff(c_70424, plain, (![C_2692, A_2693, B_2694]: (r2_hidden(C_2692, u1_struct_0(k9_yellow_6(A_2693, B_2694))) | ~v3_pre_topc(C_2692, A_2693) | ~r2_hidden(B_2694, C_2692) | ~m1_subset_1(C_2692, k1_zfmisc_1(u1_struct_0(A_2693))) | ~m1_subset_1(B_2694, u1_struct_0(A_2693)) | ~l1_pre_topc(A_2693) | ~v2_pre_topc(A_2693) | v2_struct_0(A_2693))), inference(cnfTransformation, [status(thm)], [f_125])).
% 24.97/16.20  tff(c_40, plain, (![A_20, B_21]: (m1_subset_1(A_20, B_21) | ~r2_hidden(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_66])).
% 24.97/16.20  tff(c_99679, plain, (![C_3563, A_3564, B_3565]: (m1_subset_1(C_3563, u1_struct_0(k9_yellow_6(A_3564, B_3565))) | ~v3_pre_topc(C_3563, A_3564) | ~r2_hidden(B_3565, C_3563) | ~m1_subset_1(C_3563, k1_zfmisc_1(u1_struct_0(A_3564))) | ~m1_subset_1(B_3565, u1_struct_0(A_3564)) | ~l1_pre_topc(A_3564) | ~v2_pre_topc(A_3564) | v2_struct_0(A_3564))), inference(resolution, [status(thm)], [c_70424, c_40])).
% 24.97/16.20  tff(c_64, plain, (~m1_subset_1(k3_xboole_0('#skF_7', '#skF_8'), u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 24.97/16.20  tff(c_99701, plain, (~v3_pre_topc(k3_xboole_0('#skF_7', '#skF_8'), '#skF_5') | ~r2_hidden('#skF_6', k3_xboole_0('#skF_7', '#skF_8')) | ~m1_subset_1(k3_xboole_0('#skF_7', '#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_99679, c_64])).
% 24.97/16.20  tff(c_99715, plain, (~r2_hidden('#skF_6', k3_xboole_0('#skF_7', '#skF_8')) | ~m1_subset_1(k3_xboole_0('#skF_7', '#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_70343, c_99701])).
% 24.97/16.20  tff(c_99716, plain, (~r2_hidden('#skF_6', k3_xboole_0('#skF_7', '#skF_8')) | ~m1_subset_1(k3_xboole_0('#skF_7', '#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_76, c_99715])).
% 24.97/16.20  tff(c_99749, plain, (~m1_subset_1(k3_xboole_0('#skF_7', '#skF_8'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_99716])).
% 24.97/16.20  tff(c_99758, plain, (~r1_tarski(k3_xboole_0('#skF_7', '#skF_8'), u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_44, c_99749])).
% 24.97/16.20  tff(c_99764, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70674, c_99758])).
% 24.97/16.20  tff(c_99765, plain, (~r2_hidden('#skF_6', k3_xboole_0('#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_99716])).
% 24.97/16.20  tff(c_99775, plain, (~r2_hidden('#skF_6', '#skF_8') | ~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_12, c_99765])).
% 24.97/16.20  tff(c_99783, plain, (~r2_hidden('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_90001, c_99775])).
% 24.97/16.20  tff(c_100281, plain, (![B_3571, B_3572, A_3573]: (r2_hidden(B_3571, B_3572) | ~m1_subset_1(B_3572, k1_zfmisc_1(u1_struct_0(A_3573))) | ~m1_subset_1(B_3571, u1_struct_0(A_3573)) | ~l1_pre_topc(A_3573) | ~v2_pre_topc(A_3573) | v2_struct_0(A_3573) | ~m1_subset_1(B_3572, u1_struct_0(k9_yellow_6(A_3573, B_3571))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_3573, B_3571))))), inference(resolution, [status(thm)], [c_32, c_2252])).
% 24.97/16.20  tff(c_100366, plain, (r2_hidden('#skF_6', '#skF_8') | ~m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_66, c_100281])).
% 24.97/16.20  tff(c_100393, plain, (r2_hidden('#skF_6', '#skF_8') | v2_struct_0('#skF_5') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_889, c_100366])).
% 24.97/16.20  tff(c_100395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_164, c_76, c_99783, c_100393])).
% 24.97/16.20  tff(c_100397, plain, (v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(splitRight, [status(thm)], [c_136])).
% 24.97/16.20  tff(c_137, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_66, c_118])).
% 24.97/16.20  tff(c_100399, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_100397, c_137])).
% 24.97/16.20  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.97/16.20  tff(c_100402, plain, (![D_3574, B_3575, A_3576]: (r2_hidden(D_3574, B_3575) | ~r2_hidden(D_3574, k3_xboole_0(A_3576, B_3575)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 24.97/16.20  tff(c_100611, plain, (![A_3615, B_3616]: (r2_hidden('#skF_1'(k3_xboole_0(A_3615, B_3616)), B_3616) | v1_xboole_0(k3_xboole_0(A_3615, B_3616)))), inference(resolution, [status(thm)], [c_4, c_100402])).
% 24.97/16.20  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.97/16.20  tff(c_100636, plain, (![B_3617, A_3618]: (~v1_xboole_0(B_3617) | v1_xboole_0(k3_xboole_0(A_3618, B_3617)))), inference(resolution, [status(thm)], [c_100611, c_2])).
% 24.97/16.20  tff(c_34, plain, (![B_17, A_16]: (m1_subset_1(B_17, A_16) | ~v1_xboole_0(B_17) | ~v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_60])).
% 24.97/16.20  tff(c_163, plain, (~v1_xboole_0(k3_xboole_0('#skF_7', '#skF_8')) | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_34, c_64])).
% 24.97/16.20  tff(c_100401, plain, (~v1_xboole_0(k3_xboole_0('#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_100397, c_163])).
% 24.97/16.20  tff(c_100639, plain, (~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_100636, c_100401])).
% 24.97/16.20  tff(c_100643, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100399, c_100639])).
% 24.97/16.20  tff(c_100645, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_138])).
% 24.97/16.20  tff(c_101329, plain, (![C_3723, A_3724, B_3725]: (m1_connsp_2(C_3723, A_3724, B_3725) | ~m1_subset_1(C_3723, u1_struct_0(k9_yellow_6(A_3724, B_3725))) | ~m1_subset_1(B_3725, u1_struct_0(A_3724)) | ~l1_pre_topc(A_3724) | ~v2_pre_topc(A_3724) | v2_struct_0(A_3724))), inference(cnfTransformation, [status(thm)], [f_142])).
% 24.97/16.20  tff(c_101363, plain, (m1_connsp_2('#skF_8', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_66, c_101329])).
% 24.97/16.20  tff(c_101377, plain, (m1_connsp_2('#skF_8', '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_101363])).
% 24.97/16.20  tff(c_101378, plain, (m1_connsp_2('#skF_8', '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_76, c_101377])).
% 24.97/16.20  tff(c_101386, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_101378, c_52])).
% 24.97/16.20  tff(c_101389, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_101386])).
% 24.97/16.20  tff(c_101390, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_76, c_101389])).
% 24.97/16.20  tff(c_42, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 24.97/16.20  tff(c_101411, plain, (r1_tarski('#skF_8', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_101390, c_42])).
% 24.97/16.20  tff(c_100739, plain, (![C_3638, B_3639, A_3640]: (r2_hidden(C_3638, B_3639) | ~r2_hidden(C_3638, A_3640) | ~r1_tarski(A_3640, B_3639))), inference(cnfTransformation, [status(thm)], [f_38])).
% 24.97/16.20  tff(c_100751, plain, (![A_3644, B_3645]: (r2_hidden('#skF_1'(A_3644), B_3645) | ~r1_tarski(A_3644, B_3645) | v1_xboole_0(A_3644))), inference(resolution, [status(thm)], [c_4, c_100739])).
% 24.97/16.20  tff(c_100772, plain, (![B_3645, A_3644]: (~v1_xboole_0(B_3645) | ~r1_tarski(A_3644, B_3645) | v1_xboole_0(A_3644))), inference(resolution, [status(thm)], [c_100751, c_2])).
% 24.97/16.20  tff(c_101467, plain, (~v1_xboole_0(u1_struct_0('#skF_5')) | v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_101411, c_100772])).
% 24.97/16.20  tff(c_101475, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_100645, c_101467])).
% 24.97/16.20  tff(c_100644, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_138])).
% 24.97/16.20  tff(c_101118, plain, (![A_3699, B_3700, C_3701]: (r2_hidden('#skF_3'(A_3699, B_3700, C_3701), B_3700) | r2_hidden('#skF_4'(A_3699, B_3700, C_3701), C_3701) | k3_xboole_0(A_3699, B_3700)=C_3701)), inference(cnfTransformation, [status(thm)], [f_47])).
% 24.97/16.20  tff(c_101757, plain, (![C_3753, A_3754, B_3755]: (~v1_xboole_0(C_3753) | r2_hidden('#skF_3'(A_3754, B_3755, C_3753), B_3755) | k3_xboole_0(A_3754, B_3755)=C_3753)), inference(resolution, [status(thm)], [c_101118, c_2])).
% 24.97/16.20  tff(c_101802, plain, (![B_3758, C_3759, A_3760]: (~v1_xboole_0(B_3758) | ~v1_xboole_0(C_3759) | k3_xboole_0(A_3760, B_3758)=C_3759)), inference(resolution, [status(thm)], [c_101757, c_2])).
% 24.97/16.20  tff(c_101854, plain, (![C_3761, A_3762]: (~v1_xboole_0(C_3761) | k3_xboole_0(A_3762, '#skF_6')=C_3761)), inference(resolution, [status(thm)], [c_100644, c_101802])).
% 24.97/16.20  tff(c_101905, plain, (![A_3762]: (k3_xboole_0(A_3762, '#skF_6')='#skF_6')), inference(resolution, [status(thm)], [c_100644, c_101854])).
% 24.97/16.20  tff(c_101853, plain, (![C_3759, A_3760]: (~v1_xboole_0(C_3759) | k3_xboole_0(A_3760, '#skF_6')=C_3759)), inference(resolution, [status(thm)], [c_100644, c_101802])).
% 24.97/16.20  tff(c_101969, plain, (![C_3764]: (~v1_xboole_0(C_3764) | C_3764='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_101905, c_101853])).
% 24.97/16.20  tff(c_102030, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_101475, c_101969])).
% 24.97/16.20  tff(c_101360, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_68, c_101329])).
% 24.97/16.20  tff(c_101373, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_101360])).
% 24.97/16.20  tff(c_101374, plain, (m1_connsp_2('#skF_7', '#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_76, c_101373])).
% 24.97/16.20  tff(c_101380, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_101374, c_52])).
% 24.97/16.20  tff(c_101383, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_70, c_101380])).
% 24.97/16.20  tff(c_101384, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_76, c_101383])).
% 24.97/16.20  tff(c_101400, plain, (r1_tarski('#skF_7', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_101384, c_42])).
% 24.97/16.20  tff(c_101421, plain, (~v1_xboole_0(u1_struct_0('#skF_5')) | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_101400, c_100772])).
% 24.97/16.20  tff(c_101429, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_100645, c_101421])).
% 24.97/16.20  tff(c_102031, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_101429, c_101969])).
% 24.97/16.20  tff(c_102120, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_102030, c_102031])).
% 24.97/16.20  tff(c_102046, plain, (m1_subset_1('#skF_7', u1_struct_0(k9_yellow_6('#skF_5', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_102030, c_68])).
% 24.97/16.20  tff(c_102153, plain, (m1_subset_1('#skF_8', u1_struct_0(k9_yellow_6('#skF_5', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_102120, c_102046])).
% 24.97/16.20  tff(c_101898, plain, (![A_3762]: (k3_xboole_0(A_3762, '#skF_6')='#skF_8')), inference(resolution, [status(thm)], [c_101475, c_101854])).
% 24.97/16.20  tff(c_102186, plain, (![A_3762]: (k3_xboole_0(A_3762, '#skF_8')='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_102030, c_101898])).
% 24.97/16.20  tff(c_102044, plain, (~m1_subset_1(k3_xboole_0('#skF_7', '#skF_8'), u1_struct_0(k9_yellow_6('#skF_5', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_102030, c_64])).
% 24.97/16.20  tff(c_102503, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102153, c_102186, c_102120, c_102044])).
% 24.97/16.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.97/16.20  
% 24.97/16.20  Inference rules
% 24.97/16.20  ----------------------
% 24.97/16.20  #Ref     : 0
% 24.97/16.20  #Sup     : 25790
% 24.97/16.20  #Fact    : 0
% 24.97/16.20  #Define  : 0
% 24.97/16.20  #Split   : 119
% 24.97/16.20  #Chain   : 0
% 24.97/16.20  #Close   : 0
% 24.97/16.20  
% 24.97/16.20  Ordering : KBO
% 24.97/16.20  
% 24.97/16.20  Simplification rules
% 24.97/16.20  ----------------------
% 24.97/16.20  #Subsume      : 10122
% 24.97/16.20  #Demod        : 3029
% 24.97/16.20  #Tautology    : 1717
% 24.97/16.20  #SimpNegUnit  : 891
% 24.97/16.20  #BackRed      : 33
% 24.97/16.20  
% 24.97/16.20  #Partial instantiations: 0
% 24.97/16.20  #Strategies tried      : 1
% 24.97/16.20  
% 24.97/16.20  Timing (in seconds)
% 24.97/16.20  ----------------------
% 24.97/16.20  Preprocessing        : 0.33
% 24.97/16.20  Parsing              : 0.17
% 24.97/16.20  CNF conversion       : 0.03
% 24.97/16.20  Main loop            : 15.04
% 24.97/16.20  Inferencing          : 2.65
% 24.97/16.20  Reduction            : 3.56
% 24.97/16.20  Demodulation         : 2.38
% 24.97/16.20  BG Simplification    : 0.28
% 24.97/16.20  Subsumption          : 7.61
% 24.97/16.20  Abstraction          : 0.46
% 24.97/16.20  MUC search           : 0.00
% 24.97/16.20  Cooper               : 0.00
% 24.97/16.20  Total                : 15.44
% 24.97/16.20  Index Insertion      : 0.00
% 24.97/16.20  Index Deletion       : 0.00
% 24.97/16.20  Index Matching       : 0.00
% 24.97/16.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
