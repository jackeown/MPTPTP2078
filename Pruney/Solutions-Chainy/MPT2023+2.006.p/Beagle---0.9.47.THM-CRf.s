%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:12 EST 2020

% Result     : Theorem 36.79s
% Output     : CNFRefutation 36.91s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 538 expanded)
%              Number of leaves         :   37 ( 219 expanded)
%              Depth                    :   16
%              Number of atoms          :  289 (2037 expanded)
%              Number of equality atoms :    4 (   5 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k8_subset_1 > k9_yellow_6 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k8_subset_1,type,(
    k8_subset_1: ( $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k9_yellow_6,type,(
    k9_yellow_6: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_171,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_waybel_9)).

tff(f_152,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
             => m1_connsp_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_waybel_9)).

tff(f_101,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_118,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( m1_connsp_2(B,A,C)
               => r2_hidden(C,B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k8_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_subset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k8_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_tops_1)).

tff(f_137,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).

tff(f_67,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_66,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_64,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_60,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_638,plain,(
    ! [C_172,A_173,B_174] :
      ( m1_connsp_2(C_172,A_173,B_174)
      | ~ m1_subset_1(C_172,u1_struct_0(k9_yellow_6(A_173,B_174)))
      | ~ m1_subset_1(B_174,u1_struct_0(A_173))
      | ~ l1_pre_topc(A_173)
      | ~ v2_pre_topc(A_173)
      | v2_struct_0(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_665,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_638])).

tff(c_677,plain,
    ( m1_connsp_2('#skF_6','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_665])).

tff(c_678,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_677])).

tff(c_44,plain,(
    ! [C_32,A_29,B_30] :
      ( m1_subset_1(C_32,k1_zfmisc_1(u1_struct_0(A_29)))
      | ~ m1_connsp_2(C_32,A_29,B_30)
      | ~ m1_subset_1(B_30,u1_struct_0(A_29))
      | ~ l1_pre_topc(A_29)
      | ~ v2_pre_topc(A_29)
      | v2_struct_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_684,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_678,c_44])).

tff(c_687,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_684])).

tff(c_688,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_687])).

tff(c_1368,plain,(
    ! [C_216,B_217,A_218] :
      ( r2_hidden(C_216,B_217)
      | ~ m1_connsp_2(B_217,A_218,C_216)
      | ~ m1_subset_1(C_216,u1_struct_0(A_218))
      | ~ m1_subset_1(B_217,k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ l1_pre_topc(A_218)
      | ~ v2_pre_topc(A_218)
      | v2_struct_0(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1372,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_678,c_1368])).

tff(c_1379,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_688,c_62,c_1372])).

tff(c_1380,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1379])).

tff(c_58,plain,(
    m1_subset_1('#skF_7',u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_668,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_638])).

tff(c_681,plain,
    ( m1_connsp_2('#skF_7','#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_668])).

tff(c_682,plain,(
    m1_connsp_2('#skF_7','#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_681])).

tff(c_690,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_682,c_44])).

tff(c_693,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_690])).

tff(c_694,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_693])).

tff(c_1370,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_682,c_1368])).

tff(c_1375,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_694,c_62,c_1370])).

tff(c_1376,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1375])).

tff(c_6,plain,(
    ! [D_10,A_5,B_6] :
      ( r2_hidden(D_10,k3_xboole_0(A_5,B_6))
      | ~ r2_hidden(D_10,B_6)
      | ~ r2_hidden(D_10,A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_34,plain,(
    ! [A_16,B_17,C_18] :
      ( k8_subset_1(A_16,B_17,C_18) = k3_xboole_0(B_17,C_18)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_751,plain,(
    ! [C_180] : k8_subset_1(u1_struct_0('#skF_4'),'#skF_6',C_180) = k3_xboole_0('#skF_6',C_180) ),
    inference(resolution,[status(thm)],[c_688,c_34])).

tff(c_32,plain,(
    ! [A_13,B_14,C_15] :
      ( m1_subset_1(k8_subset_1(A_13,B_14,C_15),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_757,plain,(
    ! [C_180] :
      ( m1_subset_1(k3_xboole_0('#skF_6',C_180),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_751,c_32])).

tff(c_763,plain,(
    ! [C_180] : m1_subset_1(k3_xboole_0('#skF_6',C_180),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_757])).

tff(c_95,plain,(
    ! [B_75,A_76] :
      ( v1_xboole_0(B_75)
      | ~ m1_subset_1(B_75,A_76)
      | ~ v1_xboole_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_113,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_60,c_95])).

tff(c_126,plain,(
    ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_2414,plain,(
    ! [B_288,C_289,A_290] :
      ( v3_pre_topc(k3_xboole_0(B_288,C_289),A_290)
      | ~ m1_subset_1(C_289,k1_zfmisc_1(u1_struct_0(A_290)))
      | ~ v3_pre_topc(C_289,A_290)
      | ~ m1_subset_1(B_288,k1_zfmisc_1(u1_struct_0(A_290)))
      | ~ v3_pre_topc(B_288,A_290)
      | ~ l1_pre_topc(A_290)
      | ~ v2_pre_topc(A_290) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2434,plain,(
    ! [B_288] :
      ( v3_pre_topc(k3_xboole_0(B_288,'#skF_6'),'#skF_4')
      | ~ v3_pre_topc('#skF_6','#skF_4')
      | ~ m1_subset_1(B_288,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_288,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_688,c_2414])).

tff(c_2485,plain,(
    ! [B_288] :
      ( v3_pre_topc(k3_xboole_0(B_288,'#skF_6'),'#skF_4')
      | ~ v3_pre_topc('#skF_6','#skF_4')
      | ~ m1_subset_1(B_288,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_288,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_2434])).

tff(c_130902,plain,(
    ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2485])).

tff(c_26,plain,(
    ! [B_12,A_11] :
      ( r2_hidden(B_12,A_11)
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1668,plain,(
    ! [C_238,A_239,B_240] :
      ( v3_pre_topc(C_238,A_239)
      | ~ r2_hidden(C_238,u1_struct_0(k9_yellow_6(A_239,B_240)))
      | ~ m1_subset_1(C_238,k1_zfmisc_1(u1_struct_0(A_239)))
      | ~ m1_subset_1(B_240,u1_struct_0(A_239))
      | ~ l1_pre_topc(A_239)
      | ~ v2_pre_topc(A_239)
      | v2_struct_0(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_156404,plain,(
    ! [B_5129,A_5130,B_5131] :
      ( v3_pre_topc(B_5129,A_5130)
      | ~ m1_subset_1(B_5129,k1_zfmisc_1(u1_struct_0(A_5130)))
      | ~ m1_subset_1(B_5131,u1_struct_0(A_5130))
      | ~ l1_pre_topc(A_5130)
      | ~ v2_pre_topc(A_5130)
      | v2_struct_0(A_5130)
      | ~ m1_subset_1(B_5129,u1_struct_0(k9_yellow_6(A_5130,B_5131)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_5130,B_5131))) ) ),
    inference(resolution,[status(thm)],[c_26,c_1668])).

tff(c_156470,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_60,c_156404])).

tff(c_156492,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_688,c_156470])).

tff(c_156494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_68,c_130902,c_156492])).

tff(c_156496,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_2485])).

tff(c_2432,plain,(
    ! [B_288] :
      ( v3_pre_topc(k3_xboole_0(B_288,'#skF_7'),'#skF_4')
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ m1_subset_1(B_288,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_288,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_694,c_2414])).

tff(c_2482,plain,(
    ! [B_288] :
      ( v3_pre_topc(k3_xboole_0(B_288,'#skF_7'),'#skF_4')
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ m1_subset_1(B_288,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_288,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_2432])).

tff(c_2617,plain,(
    ~ v3_pre_topc('#skF_7','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2482])).

tff(c_130703,plain,(
    ! [B_4325,A_4326,B_4327] :
      ( v3_pre_topc(B_4325,A_4326)
      | ~ m1_subset_1(B_4325,k1_zfmisc_1(u1_struct_0(A_4326)))
      | ~ m1_subset_1(B_4327,u1_struct_0(A_4326))
      | ~ l1_pre_topc(A_4326)
      | ~ v2_pre_topc(A_4326)
      | v2_struct_0(A_4326)
      | ~ m1_subset_1(B_4325,u1_struct_0(k9_yellow_6(A_4326,B_4327)))
      | v1_xboole_0(u1_struct_0(k9_yellow_6(A_4326,B_4327))) ) ),
    inference(resolution,[status(thm)],[c_26,c_1668])).

tff(c_130788,plain,
    ( v3_pre_topc('#skF_7','#skF_4')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_58,c_130703])).

tff(c_130815,plain,
    ( v3_pre_topc('#skF_7','#skF_4')
    | v2_struct_0('#skF_4')
    | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_694,c_130788])).

tff(c_130817,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_68,c_2617,c_130815])).

tff(c_156579,plain,(
    ! [B_5138] :
      ( v3_pre_topc(k3_xboole_0(B_5138,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(B_5138,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_5138,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_2482])).

tff(c_156625,plain,
    ( v3_pre_topc(k3_xboole_0('#skF_6','#skF_7'),'#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_688,c_156579])).

tff(c_156671,plain,(
    v3_pre_topc(k3_xboole_0('#skF_6','#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156496,c_156625])).

tff(c_156701,plain,(
    ! [C_5149,A_5150,B_5151] :
      ( r2_hidden(C_5149,u1_struct_0(k9_yellow_6(A_5150,B_5151)))
      | ~ v3_pre_topc(C_5149,A_5150)
      | ~ r2_hidden(B_5151,C_5149)
      | ~ m1_subset_1(C_5149,k1_zfmisc_1(u1_struct_0(A_5150)))
      | ~ m1_subset_1(B_5151,u1_struct_0(A_5150))
      | ~ l1_pre_topc(A_5150)
      | ~ v2_pre_topc(A_5150)
      | v2_struct_0(A_5150) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_38,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,B_22)
      | ~ r2_hidden(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_172052,plain,(
    ! [C_5714,A_5715,B_5716] :
      ( m1_subset_1(C_5714,u1_struct_0(k9_yellow_6(A_5715,B_5716)))
      | ~ v3_pre_topc(C_5714,A_5715)
      | ~ r2_hidden(B_5716,C_5714)
      | ~ m1_subset_1(C_5714,k1_zfmisc_1(u1_struct_0(A_5715)))
      | ~ m1_subset_1(B_5716,u1_struct_0(A_5715))
      | ~ l1_pre_topc(A_5715)
      | ~ v2_pre_topc(A_5715)
      | v2_struct_0(A_5715) ) ),
    inference(resolution,[status(thm)],[c_156701,c_38])).

tff(c_56,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_172070,plain,
    ( ~ v3_pre_topc(k3_xboole_0('#skF_6','#skF_7'),'#skF_4')
    | ~ r2_hidden('#skF_5',k3_xboole_0('#skF_6','#skF_7'))
    | ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_172052,c_56])).

tff(c_172078,plain,
    ( ~ r2_hidden('#skF_5',k3_xboole_0('#skF_6','#skF_7'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_763,c_156671,c_172070])).

tff(c_172079,plain,(
    ~ r2_hidden('#skF_5',k3_xboole_0('#skF_6','#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_172078])).

tff(c_172085,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_172079])).

tff(c_172090,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1380,c_1376,c_172085])).

tff(c_172092,plain,(
    v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_114,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_58,c_95])).

tff(c_172094,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172092,c_114])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_172095,plain,(
    ! [D_5717,B_5718,A_5719] :
      ( r2_hidden(D_5717,B_5718)
      | ~ r2_hidden(D_5717,k3_xboole_0(A_5719,B_5718)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_172128,plain,(
    ! [A_5726,B_5727] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_5726,B_5727)),B_5727)
      | v1_xboole_0(k3_xboole_0(A_5726,B_5727)) ) ),
    inference(resolution,[status(thm)],[c_4,c_172095])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_172156,plain,(
    ! [B_5731,A_5732] :
      ( ~ v1_xboole_0(B_5731)
      | v1_xboole_0(k3_xboole_0(A_5732,B_5731)) ) ),
    inference(resolution,[status(thm)],[c_172128,c_2])).

tff(c_81,plain,(
    ! [B_71,A_72] :
      ( m1_subset_1(B_71,A_72)
      | ~ v1_xboole_0(B_71)
      | ~ v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_85,plain,
    ( ~ v1_xboole_0(k3_xboole_0('#skF_6','#skF_7'))
    | ~ v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_81,c_56])).

tff(c_172118,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172092,c_85])).

tff(c_172159,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_172156,c_172118])).

tff(c_172163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_172094,c_172159])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:31:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 36.79/24.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.79/24.73  
% 36.79/24.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.79/24.73  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k8_subset_1 > k9_yellow_6 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_setfam_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 36.79/24.73  
% 36.79/24.73  %Foreground sorts:
% 36.79/24.73  
% 36.79/24.73  
% 36.79/24.73  %Background operators:
% 36.79/24.73  
% 36.79/24.73  
% 36.79/24.73  %Foreground operators:
% 36.79/24.73  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 36.79/24.73  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 36.79/24.73  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 36.79/24.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 36.79/24.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 36.79/24.73  tff('#skF_1', type, '#skF_1': $i > $i).
% 36.79/24.73  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 36.79/24.73  tff('#skF_7', type, '#skF_7': $i).
% 36.79/24.73  tff(k8_subset_1, type, k8_subset_1: ($i * $i * $i) > $i).
% 36.79/24.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 36.79/24.73  tff('#skF_5', type, '#skF_5': $i).
% 36.79/24.73  tff('#skF_6', type, '#skF_6': $i).
% 36.79/24.73  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 36.79/24.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 36.79/24.73  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 36.79/24.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 36.79/24.73  tff('#skF_4', type, '#skF_4': $i).
% 36.79/24.73  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 36.79/24.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 36.79/24.73  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 36.79/24.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 36.79/24.73  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 36.79/24.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 36.79/24.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 36.79/24.73  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 36.79/24.73  
% 36.91/24.75  tff(f_171, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k3_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_waybel_9)).
% 36.91/24.75  tff(f_152, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => m1_connsp_2(C, A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_waybel_9)).
% 36.91/24.75  tff(f_101, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 36.91/24.75  tff(f_118, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (m1_connsp_2(B, A, C) => r2_hidden(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_connsp_2)).
% 36.91/24.75  tff(f_40, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 36.91/24.75  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k8_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_subset_1)).
% 36.91/24.75  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k8_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_subset_1)).
% 36.91/24.75  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 36.91/24.75  tff(f_87, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_tops_1)).
% 36.91/24.75  tff(f_137, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_yellow_6)).
% 36.91/24.75  tff(f_67, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 36.91/24.75  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 36.91/24.75  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_171])).
% 36.91/24.75  tff(c_66, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_171])).
% 36.91/24.75  tff(c_64, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_171])).
% 36.91/24.75  tff(c_62, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_171])).
% 36.91/24.75  tff(c_60, plain, (m1_subset_1('#skF_6', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 36.91/24.75  tff(c_638, plain, (![C_172, A_173, B_174]: (m1_connsp_2(C_172, A_173, B_174) | ~m1_subset_1(C_172, u1_struct_0(k9_yellow_6(A_173, B_174))) | ~m1_subset_1(B_174, u1_struct_0(A_173)) | ~l1_pre_topc(A_173) | ~v2_pre_topc(A_173) | v2_struct_0(A_173))), inference(cnfTransformation, [status(thm)], [f_152])).
% 36.91/24.75  tff(c_665, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_60, c_638])).
% 36.91/24.75  tff(c_677, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_665])).
% 36.91/24.75  tff(c_678, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_677])).
% 36.91/24.75  tff(c_44, plain, (![C_32, A_29, B_30]: (m1_subset_1(C_32, k1_zfmisc_1(u1_struct_0(A_29))) | ~m1_connsp_2(C_32, A_29, B_30) | ~m1_subset_1(B_30, u1_struct_0(A_29)) | ~l1_pre_topc(A_29) | ~v2_pre_topc(A_29) | v2_struct_0(A_29))), inference(cnfTransformation, [status(thm)], [f_101])).
% 36.91/24.75  tff(c_684, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_678, c_44])).
% 36.91/24.75  tff(c_687, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_684])).
% 36.91/24.75  tff(c_688, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_68, c_687])).
% 36.91/24.75  tff(c_1368, plain, (![C_216, B_217, A_218]: (r2_hidden(C_216, B_217) | ~m1_connsp_2(B_217, A_218, C_216) | ~m1_subset_1(C_216, u1_struct_0(A_218)) | ~m1_subset_1(B_217, k1_zfmisc_1(u1_struct_0(A_218))) | ~l1_pre_topc(A_218) | ~v2_pre_topc(A_218) | v2_struct_0(A_218))), inference(cnfTransformation, [status(thm)], [f_118])).
% 36.91/24.75  tff(c_1372, plain, (r2_hidden('#skF_5', '#skF_6') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_678, c_1368])).
% 36.91/24.75  tff(c_1379, plain, (r2_hidden('#skF_5', '#skF_6') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_688, c_62, c_1372])).
% 36.91/24.75  tff(c_1380, plain, (r2_hidden('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_68, c_1379])).
% 36.91/24.75  tff(c_58, plain, (m1_subset_1('#skF_7', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 36.91/24.75  tff(c_668, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_638])).
% 36.91/24.75  tff(c_681, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_668])).
% 36.91/24.75  tff(c_682, plain, (m1_connsp_2('#skF_7', '#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_681])).
% 36.91/24.75  tff(c_690, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_682, c_44])).
% 36.91/24.75  tff(c_693, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_690])).
% 36.91/24.75  tff(c_694, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_68, c_693])).
% 36.91/24.75  tff(c_1370, plain, (r2_hidden('#skF_5', '#skF_7') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_682, c_1368])).
% 36.91/24.75  tff(c_1375, plain, (r2_hidden('#skF_5', '#skF_7') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_694, c_62, c_1370])).
% 36.91/24.75  tff(c_1376, plain, (r2_hidden('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_68, c_1375])).
% 36.91/24.75  tff(c_6, plain, (![D_10, A_5, B_6]: (r2_hidden(D_10, k3_xboole_0(A_5, B_6)) | ~r2_hidden(D_10, B_6) | ~r2_hidden(D_10, A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 36.91/24.75  tff(c_34, plain, (![A_16, B_17, C_18]: (k8_subset_1(A_16, B_17, C_18)=k3_xboole_0(B_17, C_18) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 36.91/24.75  tff(c_751, plain, (![C_180]: (k8_subset_1(u1_struct_0('#skF_4'), '#skF_6', C_180)=k3_xboole_0('#skF_6', C_180))), inference(resolution, [status(thm)], [c_688, c_34])).
% 36.91/24.75  tff(c_32, plain, (![A_13, B_14, C_15]: (m1_subset_1(k8_subset_1(A_13, B_14, C_15), k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 36.91/24.75  tff(c_757, plain, (![C_180]: (m1_subset_1(k3_xboole_0('#skF_6', C_180), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_751, c_32])).
% 36.91/24.75  tff(c_763, plain, (![C_180]: (m1_subset_1(k3_xboole_0('#skF_6', C_180), k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_688, c_757])).
% 36.91/24.75  tff(c_95, plain, (![B_75, A_76]: (v1_xboole_0(B_75) | ~m1_subset_1(B_75, A_76) | ~v1_xboole_0(A_76))), inference(cnfTransformation, [status(thm)], [f_53])).
% 36.91/24.75  tff(c_113, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_60, c_95])).
% 36.91/24.75  tff(c_126, plain, (~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(splitLeft, [status(thm)], [c_113])).
% 36.91/24.75  tff(c_2414, plain, (![B_288, C_289, A_290]: (v3_pre_topc(k3_xboole_0(B_288, C_289), A_290) | ~m1_subset_1(C_289, k1_zfmisc_1(u1_struct_0(A_290))) | ~v3_pre_topc(C_289, A_290) | ~m1_subset_1(B_288, k1_zfmisc_1(u1_struct_0(A_290))) | ~v3_pre_topc(B_288, A_290) | ~l1_pre_topc(A_290) | ~v2_pre_topc(A_290))), inference(cnfTransformation, [status(thm)], [f_87])).
% 36.91/24.75  tff(c_2434, plain, (![B_288]: (v3_pre_topc(k3_xboole_0(B_288, '#skF_6'), '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1(B_288, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_288, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_688, c_2414])).
% 36.91/24.75  tff(c_2485, plain, (![B_288]: (v3_pre_topc(k3_xboole_0(B_288, '#skF_6'), '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1(B_288, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_288, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_2434])).
% 36.91/24.75  tff(c_130902, plain, (~v3_pre_topc('#skF_6', '#skF_4')), inference(splitLeft, [status(thm)], [c_2485])).
% 36.91/24.75  tff(c_26, plain, (![B_12, A_11]: (r2_hidden(B_12, A_11) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 36.91/24.75  tff(c_1668, plain, (![C_238, A_239, B_240]: (v3_pre_topc(C_238, A_239) | ~r2_hidden(C_238, u1_struct_0(k9_yellow_6(A_239, B_240))) | ~m1_subset_1(C_238, k1_zfmisc_1(u1_struct_0(A_239))) | ~m1_subset_1(B_240, u1_struct_0(A_239)) | ~l1_pre_topc(A_239) | ~v2_pre_topc(A_239) | v2_struct_0(A_239))), inference(cnfTransformation, [status(thm)], [f_137])).
% 36.91/24.75  tff(c_156404, plain, (![B_5129, A_5130, B_5131]: (v3_pre_topc(B_5129, A_5130) | ~m1_subset_1(B_5129, k1_zfmisc_1(u1_struct_0(A_5130))) | ~m1_subset_1(B_5131, u1_struct_0(A_5130)) | ~l1_pre_topc(A_5130) | ~v2_pre_topc(A_5130) | v2_struct_0(A_5130) | ~m1_subset_1(B_5129, u1_struct_0(k9_yellow_6(A_5130, B_5131))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_5130, B_5131))))), inference(resolution, [status(thm)], [c_26, c_1668])).
% 36.91/24.75  tff(c_156470, plain, (v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_60, c_156404])).
% 36.91/24.75  tff(c_156492, plain, (v3_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_688, c_156470])).
% 36.91/24.75  tff(c_156494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_68, c_130902, c_156492])).
% 36.91/24.75  tff(c_156496, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_2485])).
% 36.91/24.75  tff(c_2432, plain, (![B_288]: (v3_pre_topc(k3_xboole_0(B_288, '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1(B_288, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_288, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_694, c_2414])).
% 36.91/24.75  tff(c_2482, plain, (![B_288]: (v3_pre_topc(k3_xboole_0(B_288, '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1(B_288, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_288, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_2432])).
% 36.91/24.75  tff(c_2617, plain, (~v3_pre_topc('#skF_7', '#skF_4')), inference(splitLeft, [status(thm)], [c_2482])).
% 36.91/24.75  tff(c_130703, plain, (![B_4325, A_4326, B_4327]: (v3_pre_topc(B_4325, A_4326) | ~m1_subset_1(B_4325, k1_zfmisc_1(u1_struct_0(A_4326))) | ~m1_subset_1(B_4327, u1_struct_0(A_4326)) | ~l1_pre_topc(A_4326) | ~v2_pre_topc(A_4326) | v2_struct_0(A_4326) | ~m1_subset_1(B_4325, u1_struct_0(k9_yellow_6(A_4326, B_4327))) | v1_xboole_0(u1_struct_0(k9_yellow_6(A_4326, B_4327))))), inference(resolution, [status(thm)], [c_26, c_1668])).
% 36.91/24.75  tff(c_130788, plain, (v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_58, c_130703])).
% 36.91/24.75  tff(c_130815, plain, (v3_pre_topc('#skF_7', '#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_694, c_130788])).
% 36.91/24.75  tff(c_130817, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_68, c_2617, c_130815])).
% 36.91/24.75  tff(c_156579, plain, (![B_5138]: (v3_pre_topc(k3_xboole_0(B_5138, '#skF_7'), '#skF_4') | ~m1_subset_1(B_5138, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_5138, '#skF_4'))), inference(splitRight, [status(thm)], [c_2482])).
% 36.91/24.75  tff(c_156625, plain, (v3_pre_topc(k3_xboole_0('#skF_6', '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_688, c_156579])).
% 36.91/24.75  tff(c_156671, plain, (v3_pre_topc(k3_xboole_0('#skF_6', '#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_156496, c_156625])).
% 36.91/24.75  tff(c_156701, plain, (![C_5149, A_5150, B_5151]: (r2_hidden(C_5149, u1_struct_0(k9_yellow_6(A_5150, B_5151))) | ~v3_pre_topc(C_5149, A_5150) | ~r2_hidden(B_5151, C_5149) | ~m1_subset_1(C_5149, k1_zfmisc_1(u1_struct_0(A_5150))) | ~m1_subset_1(B_5151, u1_struct_0(A_5150)) | ~l1_pre_topc(A_5150) | ~v2_pre_topc(A_5150) | v2_struct_0(A_5150))), inference(cnfTransformation, [status(thm)], [f_137])).
% 36.91/24.75  tff(c_38, plain, (![A_21, B_22]: (m1_subset_1(A_21, B_22) | ~r2_hidden(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 36.91/24.75  tff(c_172052, plain, (![C_5714, A_5715, B_5716]: (m1_subset_1(C_5714, u1_struct_0(k9_yellow_6(A_5715, B_5716))) | ~v3_pre_topc(C_5714, A_5715) | ~r2_hidden(B_5716, C_5714) | ~m1_subset_1(C_5714, k1_zfmisc_1(u1_struct_0(A_5715))) | ~m1_subset_1(B_5716, u1_struct_0(A_5715)) | ~l1_pre_topc(A_5715) | ~v2_pre_topc(A_5715) | v2_struct_0(A_5715))), inference(resolution, [status(thm)], [c_156701, c_38])).
% 36.91/24.75  tff(c_56, plain, (~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_171])).
% 36.91/24.75  tff(c_172070, plain, (~v3_pre_topc(k3_xboole_0('#skF_6', '#skF_7'), '#skF_4') | ~r2_hidden('#skF_5', k3_xboole_0('#skF_6', '#skF_7')) | ~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_172052, c_56])).
% 36.91/24.75  tff(c_172078, plain, (~r2_hidden('#skF_5', k3_xboole_0('#skF_6', '#skF_7')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_763, c_156671, c_172070])).
% 36.91/24.75  tff(c_172079, plain, (~r2_hidden('#skF_5', k3_xboole_0('#skF_6', '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_68, c_172078])).
% 36.91/24.75  tff(c_172085, plain, (~r2_hidden('#skF_5', '#skF_7') | ~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_6, c_172079])).
% 36.91/24.75  tff(c_172090, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1380, c_1376, c_172085])).
% 36.91/24.75  tff(c_172092, plain, (v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(splitRight, [status(thm)], [c_113])).
% 36.91/24.75  tff(c_114, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_58, c_95])).
% 36.91/24.75  tff(c_172094, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_172092, c_114])).
% 36.91/24.75  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 36.91/24.75  tff(c_172095, plain, (![D_5717, B_5718, A_5719]: (r2_hidden(D_5717, B_5718) | ~r2_hidden(D_5717, k3_xboole_0(A_5719, B_5718)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 36.91/24.75  tff(c_172128, plain, (![A_5726, B_5727]: (r2_hidden('#skF_1'(k3_xboole_0(A_5726, B_5727)), B_5727) | v1_xboole_0(k3_xboole_0(A_5726, B_5727)))), inference(resolution, [status(thm)], [c_4, c_172095])).
% 36.91/24.75  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 36.91/24.75  tff(c_172156, plain, (![B_5731, A_5732]: (~v1_xboole_0(B_5731) | v1_xboole_0(k3_xboole_0(A_5732, B_5731)))), inference(resolution, [status(thm)], [c_172128, c_2])).
% 36.91/24.75  tff(c_81, plain, (![B_71, A_72]: (m1_subset_1(B_71, A_72) | ~v1_xboole_0(B_71) | ~v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_53])).
% 36.91/24.75  tff(c_85, plain, (~v1_xboole_0(k3_xboole_0('#skF_6', '#skF_7')) | ~v1_xboole_0(u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_81, c_56])).
% 36.91/24.75  tff(c_172118, plain, (~v1_xboole_0(k3_xboole_0('#skF_6', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_172092, c_85])).
% 36.91/24.75  tff(c_172159, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_172156, c_172118])).
% 36.91/24.75  tff(c_172163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_172094, c_172159])).
% 36.91/24.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 36.91/24.75  
% 36.91/24.75  Inference rules
% 36.91/24.75  ----------------------
% 36.91/24.75  #Ref     : 0
% 36.91/24.75  #Sup     : 39235
% 36.91/24.75  #Fact    : 0
% 36.91/24.75  #Define  : 0
% 36.91/24.75  #Split   : 54
% 36.91/24.75  #Chain   : 0
% 36.91/24.75  #Close   : 0
% 36.91/24.75  
% 36.91/24.75  Ordering : KBO
% 36.91/24.75  
% 36.91/24.75  Simplification rules
% 36.91/24.75  ----------------------
% 36.91/24.75  #Subsume      : 9466
% 36.91/24.75  #Demod        : 6263
% 36.91/24.75  #Tautology    : 4013
% 36.91/24.75  #SimpNegUnit  : 1083
% 36.91/24.75  #BackRed      : 379
% 36.91/24.75  
% 36.91/24.75  #Partial instantiations: 0
% 36.91/24.75  #Strategies tried      : 1
% 36.91/24.75  
% 36.91/24.75  Timing (in seconds)
% 36.91/24.75  ----------------------
% 36.91/24.76  Preprocessing        : 0.45
% 36.91/24.76  Parsing              : 0.26
% 36.91/24.76  CNF conversion       : 0.03
% 36.91/24.76  Main loop            : 23.47
% 36.91/24.76  Inferencing          : 4.24
% 36.91/24.76  Reduction            : 6.97
% 36.91/24.76  Demodulation         : 5.51
% 36.91/24.76  BG Simplification    : 0.58
% 36.91/24.76  Subsumption          : 9.76
% 36.91/24.76  Abstraction          : 0.85
% 36.91/24.76  MUC search           : 0.00
% 36.91/24.76  Cooper               : 0.00
% 36.91/24.76  Total                : 23.96
% 36.91/24.76  Index Insertion      : 0.00
% 36.91/24.76  Index Deletion       : 0.00
% 36.91/24.76  Index Matching       : 0.00
% 36.91/24.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
