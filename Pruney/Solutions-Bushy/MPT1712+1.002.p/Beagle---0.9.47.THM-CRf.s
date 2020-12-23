%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1712+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:38:17 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 250 expanded)
%              Number of leaves         :   32 ( 112 expanded)
%              Depth                    :   18
%              Number of atoms          :  360 (1743 expanded)
%              Number of equality atoms :    7 ( 170 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_178,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(k1_tsep_1(A,B,C)))
                   => ! [E] :
                        ( m1_subset_1(E,u1_struct_0(B))
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(C))
                           => ( ( E = D
                                & F = D )
                             => ! [G] :
                                  ( m1_connsp_2(G,B,E)
                                 => ! [H] :
                                      ( m1_connsp_2(H,C,F)
                                     => ? [I] :
                                          ( m1_connsp_2(I,k1_tsep_1(A,B,C),D)
                                          & r1_tarski(I,k2_xboole_0(G,H)) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tmap_1)).

tff(f_109,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(k1_tsep_1(A,B,C)))
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(C))
                         => ( ( E = D
                              & F = D )
                           => ! [G] :
                                ( m1_connsp_2(G,B,E)
                               => ! [H] :
                                    ( m1_connsp_2(H,C,F)
                                   => ? [I] :
                                        ( m1_subset_1(I,k1_zfmisc_1(u1_struct_0(k1_tsep_1(A,B,C))))
                                        & v3_pre_topc(I,k1_tsep_1(A,B,C))
                                        & r2_hidden(D,I)
                                        & r1_tarski(I,k2_xboole_0(G,H)) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tmap_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & m1_pre_topc(k1_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_33,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_134,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v3_pre_topc(B,A)
                  & r2_hidden(C,B) )
               => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

tff(c_28,plain,(
    m1_connsp_2('#skF_8','#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_32,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_30,plain,(
    '#skF_7' = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_54,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30])).

tff(c_26,plain,(
    m1_connsp_2('#skF_9','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_56,plain,(
    m1_connsp_2('#skF_9','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_26])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_53,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_38])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_34,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_55,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_34])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_44,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_40,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_167,plain,(
    ! [A_1074,C_1075,B_1073,F_1072,G_1071,H_1076] :
      ( r2_hidden(F_1072,'#skF_1'(G_1071,F_1072,F_1072,F_1072,B_1073,A_1074,C_1075,H_1076))
      | ~ m1_connsp_2(H_1076,C_1075,F_1072)
      | ~ m1_connsp_2(G_1071,B_1073,F_1072)
      | ~ m1_subset_1(F_1072,u1_struct_0(C_1075))
      | ~ m1_subset_1(F_1072,u1_struct_0(B_1073))
      | ~ m1_subset_1(F_1072,u1_struct_0(k1_tsep_1(A_1074,B_1073,C_1075)))
      | ~ m1_pre_topc(C_1075,A_1074)
      | v2_struct_0(C_1075)
      | ~ m1_pre_topc(B_1073,A_1074)
      | v2_struct_0(B_1073)
      | ~ l1_pre_topc(A_1074)
      | ~ v2_pre_topc(A_1074)
      | v2_struct_0(A_1074) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_169,plain,(
    ! [G_1071,H_1076] :
      ( r2_hidden('#skF_6','#skF_1'(G_1071,'#skF_6','#skF_6','#skF_6','#skF_3','#skF_2','#skF_4',H_1076))
      | ~ m1_connsp_2(H_1076,'#skF_4','#skF_6')
      | ~ m1_connsp_2(G_1071,'#skF_3','#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_53,c_167])).

tff(c_172,plain,(
    ! [G_1071,H_1076] :
      ( r2_hidden('#skF_6','#skF_1'(G_1071,'#skF_6','#skF_6','#skF_6','#skF_3','#skF_2','#skF_4',H_1076))
      | ~ m1_connsp_2(H_1076,'#skF_4','#skF_6')
      | ~ m1_connsp_2(G_1071,'#skF_3','#skF_6')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_40,c_36,c_55,c_169])).

tff(c_173,plain,(
    ! [G_1071,H_1076] :
      ( r2_hidden('#skF_6','#skF_1'(G_1071,'#skF_6','#skF_6','#skF_6','#skF_3','#skF_2','#skF_4',H_1076))
      | ~ m1_connsp_2(H_1076,'#skF_4','#skF_6')
      | ~ m1_connsp_2(G_1071,'#skF_3','#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_42,c_172])).

tff(c_12,plain,(
    ! [A_10,B_266,H_518,G_514,C_394,F_506] :
      ( r1_tarski('#skF_1'(G_514,F_506,F_506,F_506,B_266,A_10,C_394,H_518),k2_xboole_0(G_514,H_518))
      | ~ m1_connsp_2(H_518,C_394,F_506)
      | ~ m1_connsp_2(G_514,B_266,F_506)
      | ~ m1_subset_1(F_506,u1_struct_0(C_394))
      | ~ m1_subset_1(F_506,u1_struct_0(B_266))
      | ~ m1_subset_1(F_506,u1_struct_0(k1_tsep_1(A_10,B_266,C_394)))
      | ~ m1_pre_topc(C_394,A_10)
      | v2_struct_0(C_394)
      | ~ m1_pre_topc(B_266,A_10)
      | v2_struct_0(B_266)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_16,plain,(
    ! [A_10,B_266,H_518,G_514,C_394,F_506] :
      ( v3_pre_topc('#skF_1'(G_514,F_506,F_506,F_506,B_266,A_10,C_394,H_518),k1_tsep_1(A_10,B_266,C_394))
      | ~ m1_connsp_2(H_518,C_394,F_506)
      | ~ m1_connsp_2(G_514,B_266,F_506)
      | ~ m1_subset_1(F_506,u1_struct_0(C_394))
      | ~ m1_subset_1(F_506,u1_struct_0(B_266))
      | ~ m1_subset_1(F_506,u1_struct_0(k1_tsep_1(A_10,B_266,C_394)))
      | ~ m1_pre_topc(C_394,A_10)
      | v2_struct_0(C_394)
      | ~ m1_pre_topc(B_266,A_10)
      | v2_struct_0(B_266)
      | ~ l1_pre_topc(A_10)
      | ~ v2_pre_topc(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_177,plain,(
    ! [B_1093,A_1094,F_1092,G_1091,C_1095,H_1096] :
      ( m1_subset_1('#skF_1'(G_1091,F_1092,F_1092,F_1092,B_1093,A_1094,C_1095,H_1096),k1_zfmisc_1(u1_struct_0(k1_tsep_1(A_1094,B_1093,C_1095))))
      | ~ m1_connsp_2(H_1096,C_1095,F_1092)
      | ~ m1_connsp_2(G_1091,B_1093,F_1092)
      | ~ m1_subset_1(F_1092,u1_struct_0(C_1095))
      | ~ m1_subset_1(F_1092,u1_struct_0(B_1093))
      | ~ m1_subset_1(F_1092,u1_struct_0(k1_tsep_1(A_1094,B_1093,C_1095)))
      | ~ m1_pre_topc(C_1095,A_1094)
      | v2_struct_0(C_1095)
      | ~ m1_pre_topc(B_1093,A_1094)
      | v2_struct_0(B_1093)
      | ~ l1_pre_topc(A_1094)
      | ~ v2_pre_topc(A_1094)
      | v2_struct_0(A_1094) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_96,plain,(
    ! [A_1047,B_1048,C_1049] :
      ( m1_pre_topc(k1_tsep_1(A_1047,B_1048,C_1049),A_1047)
      | ~ m1_pre_topc(C_1049,A_1047)
      | v2_struct_0(C_1049)
      | ~ m1_pre_topc(B_1048,A_1047)
      | v2_struct_0(B_1048)
      | ~ l1_pre_topc(A_1047)
      | v2_struct_0(A_1047) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [B_9,A_7] :
      ( l1_pre_topc(B_9)
      | ~ m1_pre_topc(B_9,A_7)
      | ~ l1_pre_topc(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_104,plain,(
    ! [A_1047,B_1048,C_1049] :
      ( l1_pre_topc(k1_tsep_1(A_1047,B_1048,C_1049))
      | ~ m1_pre_topc(C_1049,A_1047)
      | v2_struct_0(C_1049)
      | ~ m1_pre_topc(B_1048,A_1047)
      | v2_struct_0(B_1048)
      | ~ l1_pre_topc(A_1047)
      | v2_struct_0(A_1047) ) ),
    inference(resolution,[status(thm)],[c_96,c_10])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( v2_pre_topc(B_3)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1)
      | ~ v2_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_125,plain,(
    ! [A_1058,B_1059,C_1060] :
      ( v2_pre_topc(k1_tsep_1(A_1058,B_1059,C_1060))
      | ~ v2_pre_topc(A_1058)
      | ~ m1_pre_topc(C_1060,A_1058)
      | v2_struct_0(C_1060)
      | ~ m1_pre_topc(B_1059,A_1058)
      | v2_struct_0(B_1059)
      | ~ l1_pre_topc(A_1058)
      | v2_struct_0(A_1058) ) ),
    inference(resolution,[status(thm)],[c_96,c_2])).

tff(c_105,plain,(
    ! [B_1050,A_1051,C_1052] :
      ( m1_connsp_2(B_1050,A_1051,C_1052)
      | ~ r2_hidden(C_1052,B_1050)
      | ~ v3_pre_topc(B_1050,A_1051)
      | ~ m1_subset_1(C_1052,u1_struct_0(A_1051))
      | ~ m1_subset_1(B_1050,k1_zfmisc_1(u1_struct_0(A_1051)))
      | ~ l1_pre_topc(A_1051)
      | ~ v2_pre_topc(A_1051)
      | v2_struct_0(A_1051) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_112,plain,(
    ! [B_1050] :
      ( m1_connsp_2(B_1050,k1_tsep_1('#skF_2','#skF_3','#skF_4'),'#skF_6')
      | ~ r2_hidden('#skF_6',B_1050)
      | ~ v3_pre_topc(B_1050,k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(B_1050,k1_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4'))))
      | ~ l1_pre_topc(k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | ~ v2_pre_topc(k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | v2_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_53,c_105])).

tff(c_124,plain,(
    ~ v2_pre_topc(k1_tsep_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_128,plain,
    ( ~ v2_pre_topc('#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_125,c_124])).

tff(c_131,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_40,c_50,c_128])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_42,c_131])).

tff(c_134,plain,(
    ! [B_1050] :
      ( ~ l1_pre_topc(k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | v2_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | m1_connsp_2(B_1050,k1_tsep_1('#skF_2','#skF_3','#skF_4'),'#skF_6')
      | ~ r2_hidden('#skF_6',B_1050)
      | ~ v3_pre_topc(B_1050,k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(B_1050,k1_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4')))) ) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_137,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_147,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_104,c_137])).

tff(c_150,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_40,c_147])).

tff(c_152,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_42,c_150])).

tff(c_153,plain,(
    ! [B_1050] :
      ( v2_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | m1_connsp_2(B_1050,k1_tsep_1('#skF_2','#skF_3','#skF_4'),'#skF_6')
      | ~ r2_hidden('#skF_6',B_1050)
      | ~ v3_pre_topc(B_1050,k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(B_1050,k1_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4')))) ) ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_155,plain,(
    v2_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_153])).

tff(c_8,plain,(
    ! [A_4,B_5,C_6] :
      ( ~ v2_struct_0(k1_tsep_1(A_4,B_5,C_6))
      | ~ m1_pre_topc(C_6,A_4)
      | v2_struct_0(C_6)
      | ~ m1_pre_topc(B_5,A_4)
      | v2_struct_0(B_5)
      | ~ l1_pre_topc(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_158,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_155,c_8])).

tff(c_161,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_40,c_158])).

tff(c_163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_42,c_161])).

tff(c_164,plain,(
    ! [B_1050] :
      ( m1_connsp_2(B_1050,k1_tsep_1('#skF_2','#skF_3','#skF_4'),'#skF_6')
      | ~ r2_hidden('#skF_6',B_1050)
      | ~ v3_pre_topc(B_1050,k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(B_1050,k1_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4')))) ) ),
    inference(splitRight,[status(thm)],[c_153])).

tff(c_181,plain,(
    ! [G_1091,F_1092,H_1096] :
      ( m1_connsp_2('#skF_1'(G_1091,F_1092,F_1092,F_1092,'#skF_3','#skF_2','#skF_4',H_1096),k1_tsep_1('#skF_2','#skF_3','#skF_4'),'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_1'(G_1091,F_1092,F_1092,F_1092,'#skF_3','#skF_2','#skF_4',H_1096))
      | ~ v3_pre_topc('#skF_1'(G_1091,F_1092,F_1092,F_1092,'#skF_3','#skF_2','#skF_4',H_1096),k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_connsp_2(H_1096,'#skF_4',F_1092)
      | ~ m1_connsp_2(G_1091,'#skF_3',F_1092)
      | ~ m1_subset_1(F_1092,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_1092,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_1092,u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4')))
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_177,c_164])).

tff(c_186,plain,(
    ! [G_1091,F_1092,H_1096] :
      ( m1_connsp_2('#skF_1'(G_1091,F_1092,F_1092,F_1092,'#skF_3','#skF_2','#skF_4',H_1096),k1_tsep_1('#skF_2','#skF_3','#skF_4'),'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_1'(G_1091,F_1092,F_1092,F_1092,'#skF_3','#skF_2','#skF_4',H_1096))
      | ~ v3_pre_topc('#skF_1'(G_1091,F_1092,F_1092,F_1092,'#skF_3','#skF_2','#skF_4',H_1096),k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_connsp_2(H_1096,'#skF_4',F_1092)
      | ~ m1_connsp_2(G_1091,'#skF_3',F_1092)
      | ~ m1_subset_1(F_1092,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_1092,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_1092,u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_40,c_181])).

tff(c_196,plain,(
    ! [G_1104,F_1105,H_1106] :
      ( m1_connsp_2('#skF_1'(G_1104,F_1105,F_1105,F_1105,'#skF_3','#skF_2','#skF_4',H_1106),k1_tsep_1('#skF_2','#skF_3','#skF_4'),'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_1'(G_1104,F_1105,F_1105,F_1105,'#skF_3','#skF_2','#skF_4',H_1106))
      | ~ v3_pre_topc('#skF_1'(G_1104,F_1105,F_1105,F_1105,'#skF_3','#skF_2','#skF_4',H_1106),k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_connsp_2(H_1106,'#skF_4',F_1105)
      | ~ m1_connsp_2(G_1104,'#skF_3',F_1105)
      | ~ m1_subset_1(F_1105,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_1105,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_1105,u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_42,c_186])).

tff(c_24,plain,(
    ! [I_1032] :
      ( ~ r1_tarski(I_1032,k2_xboole_0('#skF_8','#skF_9'))
      | ~ m1_connsp_2(I_1032,k1_tsep_1('#skF_2','#skF_3','#skF_4'),'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_57,plain,(
    ! [I_1032] :
      ( ~ r1_tarski(I_1032,k2_xboole_0('#skF_8','#skF_9'))
      | ~ m1_connsp_2(I_1032,k1_tsep_1('#skF_2','#skF_3','#skF_4'),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_24])).

tff(c_201,plain,(
    ! [G_1107,F_1108,H_1109] :
      ( ~ r1_tarski('#skF_1'(G_1107,F_1108,F_1108,F_1108,'#skF_3','#skF_2','#skF_4',H_1109),k2_xboole_0('#skF_8','#skF_9'))
      | ~ r2_hidden('#skF_6','#skF_1'(G_1107,F_1108,F_1108,F_1108,'#skF_3','#skF_2','#skF_4',H_1109))
      | ~ v3_pre_topc('#skF_1'(G_1107,F_1108,F_1108,F_1108,'#skF_3','#skF_2','#skF_4',H_1109),k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_connsp_2(H_1109,'#skF_4',F_1108)
      | ~ m1_connsp_2(G_1107,'#skF_3',F_1108)
      | ~ m1_subset_1(F_1108,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_1108,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_1108,u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_196,c_57])).

tff(c_205,plain,(
    ! [G_514,F_506,H_518] :
      ( ~ r1_tarski('#skF_1'(G_514,F_506,F_506,F_506,'#skF_3','#skF_2','#skF_4',H_518),k2_xboole_0('#skF_8','#skF_9'))
      | ~ r2_hidden('#skF_6','#skF_1'(G_514,F_506,F_506,F_506,'#skF_3','#skF_2','#skF_4',H_518))
      | ~ m1_connsp_2(H_518,'#skF_4',F_506)
      | ~ m1_connsp_2(G_514,'#skF_3',F_506)
      | ~ m1_subset_1(F_506,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_506,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_506,u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4')))
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_16,c_201])).

tff(c_208,plain,(
    ! [G_514,F_506,H_518] :
      ( ~ r1_tarski('#skF_1'(G_514,F_506,F_506,F_506,'#skF_3','#skF_2','#skF_4',H_518),k2_xboole_0('#skF_8','#skF_9'))
      | ~ r2_hidden('#skF_6','#skF_1'(G_514,F_506,F_506,F_506,'#skF_3','#skF_2','#skF_4',H_518))
      | ~ m1_connsp_2(H_518,'#skF_4',F_506)
      | ~ m1_connsp_2(G_514,'#skF_3',F_506)
      | ~ m1_subset_1(F_506,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_506,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_506,u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_40,c_205])).

tff(c_210,plain,(
    ! [G_1110,F_1111,H_1112] :
      ( ~ r1_tarski('#skF_1'(G_1110,F_1111,F_1111,F_1111,'#skF_3','#skF_2','#skF_4',H_1112),k2_xboole_0('#skF_8','#skF_9'))
      | ~ r2_hidden('#skF_6','#skF_1'(G_1110,F_1111,F_1111,F_1111,'#skF_3','#skF_2','#skF_4',H_1112))
      | ~ m1_connsp_2(H_1112,'#skF_4',F_1111)
      | ~ m1_connsp_2(G_1110,'#skF_3',F_1111)
      | ~ m1_subset_1(F_1111,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_1111,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_1111,u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_42,c_208])).

tff(c_214,plain,(
    ! [F_506] :
      ( ~ r2_hidden('#skF_6','#skF_1'('#skF_8',F_506,F_506,F_506,'#skF_3','#skF_2','#skF_4','#skF_9'))
      | ~ m1_connsp_2('#skF_9','#skF_4',F_506)
      | ~ m1_connsp_2('#skF_8','#skF_3',F_506)
      | ~ m1_subset_1(F_506,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_506,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_506,u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4')))
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_12,c_210])).

tff(c_217,plain,(
    ! [F_506] :
      ( ~ r2_hidden('#skF_6','#skF_1'('#skF_8',F_506,F_506,F_506,'#skF_3','#skF_2','#skF_4','#skF_9'))
      | ~ m1_connsp_2('#skF_9','#skF_4',F_506)
      | ~ m1_connsp_2('#skF_8','#skF_3',F_506)
      | ~ m1_subset_1(F_506,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_506,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_506,u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_40,c_214])).

tff(c_219,plain,(
    ! [F_1113] :
      ( ~ r2_hidden('#skF_6','#skF_1'('#skF_8',F_1113,F_1113,F_1113,'#skF_3','#skF_2','#skF_4','#skF_9'))
      | ~ m1_connsp_2('#skF_9','#skF_4',F_1113)
      | ~ m1_connsp_2('#skF_8','#skF_3',F_1113)
      | ~ m1_subset_1(F_1113,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_1113,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_1113,u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_42,c_217])).

tff(c_222,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4')))
    | ~ m1_connsp_2('#skF_9','#skF_4','#skF_6')
    | ~ m1_connsp_2('#skF_8','#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_173,c_219])).

tff(c_226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_56,c_53,c_36,c_55,c_222])).

%------------------------------------------------------------------------------
