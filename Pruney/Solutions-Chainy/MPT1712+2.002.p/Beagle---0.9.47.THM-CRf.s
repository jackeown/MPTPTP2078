%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:29 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 247 expanded)
%              Number of leaves         :   32 ( 111 expanded)
%              Depth                    :   18
%              Number of atoms          :  362 (1729 expanded)
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

tff(f_188,negated_conjecture,(
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

tff(f_144,axiom,(
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

tff(f_73,axiom,(
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

tff(f_32,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k1_tsep_1(A,B,C))
        & v1_pre_topc(k1_tsep_1(A,B,C))
        & v2_pre_topc(k1_tsep_1(A,B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tmap_1)).

tff(f_51,axiom,(
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

tff(c_30,plain,(
    m1_connsp_2('#skF_8','#skF_3','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_34,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_32,plain,(
    '#skF_7' = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_56,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32])).

tff(c_28,plain,(
    m1_connsp_2('#skF_9','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_58,plain,(
    m1_connsp_2('#skF_9','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_28])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_55,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_40])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_36,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_57,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_36])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_52,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_50,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_46,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_42,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_108,plain,(
    ! [F_1055,B_1053,G_1056,H_1054,A_1051,C_1052] :
      ( r2_hidden(F_1055,'#skF_1'(A_1051,C_1052,F_1055,F_1055,B_1053,H_1054,F_1055,G_1056))
      | ~ m1_connsp_2(H_1054,C_1052,F_1055)
      | ~ m1_connsp_2(G_1056,B_1053,F_1055)
      | ~ m1_subset_1(F_1055,u1_struct_0(C_1052))
      | ~ m1_subset_1(F_1055,u1_struct_0(B_1053))
      | ~ m1_subset_1(F_1055,u1_struct_0(k1_tsep_1(A_1051,B_1053,C_1052)))
      | ~ m1_pre_topc(C_1052,A_1051)
      | v2_struct_0(C_1052)
      | ~ m1_pre_topc(B_1053,A_1051)
      | v2_struct_0(B_1053)
      | ~ l1_pre_topc(A_1051)
      | ~ v2_pre_topc(A_1051)
      | v2_struct_0(A_1051) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_110,plain,(
    ! [H_1054,G_1056] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_2','#skF_4','#skF_6','#skF_6','#skF_3',H_1054,'#skF_6',G_1056))
      | ~ m1_connsp_2(H_1054,'#skF_4','#skF_6')
      | ~ m1_connsp_2(G_1056,'#skF_3','#skF_6')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_55,c_108])).

tff(c_113,plain,(
    ! [H_1054,G_1056] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_2','#skF_4','#skF_6','#skF_6','#skF_3',H_1054,'#skF_6',G_1056))
      | ~ m1_connsp_2(H_1054,'#skF_4','#skF_6')
      | ~ m1_connsp_2(G_1056,'#skF_3','#skF_6')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_42,c_38,c_57,c_110])).

tff(c_114,plain,(
    ! [H_1054,G_1056] :
      ( r2_hidden('#skF_6','#skF_1'('#skF_2','#skF_4','#skF_6','#skF_6','#skF_3',H_1054,'#skF_6',G_1056))
      | ~ m1_connsp_2(H_1054,'#skF_4','#skF_6')
      | ~ m1_connsp_2(G_1056,'#skF_3','#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_113])).

tff(c_18,plain,(
    ! [C_401,F_513,H_525,G_521,A_17,B_273] :
      ( r1_tarski('#skF_1'(A_17,C_401,F_513,F_513,B_273,H_525,F_513,G_521),k2_xboole_0(G_521,H_525))
      | ~ m1_connsp_2(H_525,C_401,F_513)
      | ~ m1_connsp_2(G_521,B_273,F_513)
      | ~ m1_subset_1(F_513,u1_struct_0(C_401))
      | ~ m1_subset_1(F_513,u1_struct_0(B_273))
      | ~ m1_subset_1(F_513,u1_struct_0(k1_tsep_1(A_17,B_273,C_401)))
      | ~ m1_pre_topc(C_401,A_17)
      | v2_struct_0(C_401)
      | ~ m1_pre_topc(B_273,A_17)
      | v2_struct_0(B_273)
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_22,plain,(
    ! [C_401,F_513,H_525,G_521,A_17,B_273] :
      ( v3_pre_topc('#skF_1'(A_17,C_401,F_513,F_513,B_273,H_525,F_513,G_521),k1_tsep_1(A_17,B_273,C_401))
      | ~ m1_connsp_2(H_525,C_401,F_513)
      | ~ m1_connsp_2(G_521,B_273,F_513)
      | ~ m1_subset_1(F_513,u1_struct_0(C_401))
      | ~ m1_subset_1(F_513,u1_struct_0(B_273))
      | ~ m1_subset_1(F_513,u1_struct_0(k1_tsep_1(A_17,B_273,C_401)))
      | ~ m1_pre_topc(C_401,A_17)
      | v2_struct_0(C_401)
      | ~ m1_pre_topc(B_273,A_17)
      | v2_struct_0(B_273)
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_153,plain,(
    ! [H_1075,A_1072,G_1077,C_1073,F_1076,B_1074] :
      ( m1_subset_1('#skF_1'(A_1072,C_1073,F_1076,F_1076,B_1074,H_1075,F_1076,G_1077),k1_zfmisc_1(u1_struct_0(k1_tsep_1(A_1072,B_1074,C_1073))))
      | ~ m1_connsp_2(H_1075,C_1073,F_1076)
      | ~ m1_connsp_2(G_1077,B_1074,F_1076)
      | ~ m1_subset_1(F_1076,u1_struct_0(C_1073))
      | ~ m1_subset_1(F_1076,u1_struct_0(B_1074))
      | ~ m1_subset_1(F_1076,u1_struct_0(k1_tsep_1(A_1072,B_1074,C_1073)))
      | ~ m1_pre_topc(C_1073,A_1072)
      | v2_struct_0(C_1073)
      | ~ m1_pre_topc(B_1074,A_1072)
      | v2_struct_0(B_1074)
      | ~ l1_pre_topc(A_1072)
      | ~ v2_pre_topc(A_1072)
      | v2_struct_0(A_1072) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_84,plain,(
    ! [A_1039,B_1040,C_1041] :
      ( m1_pre_topc(k1_tsep_1(A_1039,B_1040,C_1041),A_1039)
      | ~ m1_pre_topc(C_1041,A_1039)
      | v2_struct_0(C_1041)
      | ~ m1_pre_topc(B_1040,A_1039)
      | v2_struct_0(B_1040)
      | ~ l1_pre_topc(A_1039)
      | v2_struct_0(A_1039) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    ! [B_3,A_1] :
      ( l1_pre_topc(B_3)
      | ~ m1_pre_topc(B_3,A_1)
      | ~ l1_pre_topc(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_88,plain,(
    ! [A_1039,B_1040,C_1041] :
      ( l1_pre_topc(k1_tsep_1(A_1039,B_1040,C_1041))
      | ~ m1_pre_topc(C_1041,A_1039)
      | v2_struct_0(C_1041)
      | ~ m1_pre_topc(B_1040,A_1039)
      | v2_struct_0(B_1040)
      | ~ l1_pre_topc(A_1039)
      | v2_struct_0(A_1039) ) ),
    inference(resolution,[status(thm)],[c_84,c_2])).

tff(c_12,plain,(
    ! [A_14,B_15,C_16] :
      ( v2_pre_topc(k1_tsep_1(A_14,B_15,C_16))
      | ~ m1_pre_topc(C_16,A_14)
      | v2_struct_0(C_16)
      | ~ m1_pre_topc(B_15,A_14)
      | v2_struct_0(B_15)
      | ~ l1_pre_topc(A_14)
      | ~ v2_pre_topc(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_91,plain,(
    ! [B_1048,A_1049,C_1050] :
      ( m1_connsp_2(B_1048,A_1049,C_1050)
      | ~ r2_hidden(C_1050,B_1048)
      | ~ v3_pre_topc(B_1048,A_1049)
      | ~ m1_subset_1(C_1050,u1_struct_0(A_1049))
      | ~ m1_subset_1(B_1048,k1_zfmisc_1(u1_struct_0(A_1049)))
      | ~ l1_pre_topc(A_1049)
      | ~ v2_pre_topc(A_1049)
      | v2_struct_0(A_1049) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_98,plain,(
    ! [B_1048] :
      ( m1_connsp_2(B_1048,k1_tsep_1('#skF_2','#skF_3','#skF_4'),'#skF_6')
      | ~ r2_hidden('#skF_6',B_1048)
      | ~ v3_pre_topc(B_1048,k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(B_1048,k1_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4'))))
      | ~ l1_pre_topc(k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | ~ v2_pre_topc(k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | v2_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_55,c_91])).

tff(c_117,plain,(
    ~ v2_pre_topc(k1_tsep_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_98])).

tff(c_120,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_117])).

tff(c_123,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_42,c_120])).

tff(c_125,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_123])).

tff(c_126,plain,(
    ! [B_1048] :
      ( ~ l1_pre_topc(k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | v2_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | m1_connsp_2(B_1048,k1_tsep_1('#skF_2','#skF_3','#skF_4'),'#skF_6')
      | ~ r2_hidden('#skF_6',B_1048)
      | ~ v3_pre_topc(B_1048,k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(B_1048,k1_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4')))) ) ),
    inference(splitRight,[status(thm)],[c_98])).

tff(c_128,plain,(
    ~ l1_pre_topc(k1_tsep_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_131,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_88,c_128])).

tff(c_134,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_131])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_134])).

tff(c_137,plain,(
    ! [B_1048] :
      ( v2_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | m1_connsp_2(B_1048,k1_tsep_1('#skF_2','#skF_3','#skF_4'),'#skF_6')
      | ~ r2_hidden('#skF_6',B_1048)
      | ~ v3_pre_topc(B_1048,k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(B_1048,k1_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4')))) ) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_140,plain,(
    v2_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_10,plain,(
    ! [A_11,B_12,C_13] :
      ( ~ v2_struct_0(k1_tsep_1(A_11,B_12,C_13))
      | ~ m1_pre_topc(C_13,A_11)
      | v2_struct_0(C_13)
      | ~ m1_pre_topc(B_12,A_11)
      | v2_struct_0(B_12)
      | ~ l1_pre_topc(A_11)
      | v2_struct_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_143,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_140,c_10])).

tff(c_146,plain,
    ( v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_42,c_143])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_146])).

tff(c_149,plain,(
    ! [B_1048] :
      ( m1_connsp_2(B_1048,k1_tsep_1('#skF_2','#skF_3','#skF_4'),'#skF_6')
      | ~ r2_hidden('#skF_6',B_1048)
      | ~ v3_pre_topc(B_1048,k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(B_1048,k1_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4')))) ) ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_157,plain,(
    ! [F_1076,H_1075,G_1077] :
      ( m1_connsp_2('#skF_1'('#skF_2','#skF_4',F_1076,F_1076,'#skF_3',H_1075,F_1076,G_1077),k1_tsep_1('#skF_2','#skF_3','#skF_4'),'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_2','#skF_4',F_1076,F_1076,'#skF_3',H_1075,F_1076,G_1077))
      | ~ v3_pre_topc('#skF_1'('#skF_2','#skF_4',F_1076,F_1076,'#skF_3',H_1075,F_1076,G_1077),k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_connsp_2(H_1075,'#skF_4',F_1076)
      | ~ m1_connsp_2(G_1077,'#skF_3',F_1076)
      | ~ m1_subset_1(F_1076,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_1076,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_1076,u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4')))
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_153,c_149])).

tff(c_160,plain,(
    ! [F_1076,H_1075,G_1077] :
      ( m1_connsp_2('#skF_1'('#skF_2','#skF_4',F_1076,F_1076,'#skF_3',H_1075,F_1076,G_1077),k1_tsep_1('#skF_2','#skF_3','#skF_4'),'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_2','#skF_4',F_1076,F_1076,'#skF_3',H_1075,F_1076,G_1077))
      | ~ v3_pre_topc('#skF_1'('#skF_2','#skF_4',F_1076,F_1076,'#skF_3',H_1075,F_1076,G_1077),k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_connsp_2(H_1075,'#skF_4',F_1076)
      | ~ m1_connsp_2(G_1077,'#skF_3',F_1076)
      | ~ m1_subset_1(F_1076,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_1076,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_1076,u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_42,c_157])).

tff(c_162,plain,(
    ! [F_1078,H_1079,G_1080] :
      ( m1_connsp_2('#skF_1'('#skF_2','#skF_4',F_1078,F_1078,'#skF_3',H_1079,F_1078,G_1080),k1_tsep_1('#skF_2','#skF_3','#skF_4'),'#skF_6')
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_2','#skF_4',F_1078,F_1078,'#skF_3',H_1079,F_1078,G_1080))
      | ~ v3_pre_topc('#skF_1'('#skF_2','#skF_4',F_1078,F_1078,'#skF_3',H_1079,F_1078,G_1080),k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_connsp_2(H_1079,'#skF_4',F_1078)
      | ~ m1_connsp_2(G_1080,'#skF_3',F_1078)
      | ~ m1_subset_1(F_1078,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_1078,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_1078,u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_160])).

tff(c_26,plain,(
    ! [I_1029] :
      ( ~ r1_tarski(I_1029,k2_xboole_0('#skF_8','#skF_9'))
      | ~ m1_connsp_2(I_1029,k1_tsep_1('#skF_2','#skF_3','#skF_4'),'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_59,plain,(
    ! [I_1029] :
      ( ~ r1_tarski(I_1029,k2_xboole_0('#skF_8','#skF_9'))
      | ~ m1_connsp_2(I_1029,k1_tsep_1('#skF_2','#skF_3','#skF_4'),'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_26])).

tff(c_167,plain,(
    ! [F_1081,H_1082,G_1083] :
      ( ~ r1_tarski('#skF_1'('#skF_2','#skF_4',F_1081,F_1081,'#skF_3',H_1082,F_1081,G_1083),k2_xboole_0('#skF_8','#skF_9'))
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_2','#skF_4',F_1081,F_1081,'#skF_3',H_1082,F_1081,G_1083))
      | ~ v3_pre_topc('#skF_1'('#skF_2','#skF_4',F_1081,F_1081,'#skF_3',H_1082,F_1081,G_1083),k1_tsep_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_connsp_2(H_1082,'#skF_4',F_1081)
      | ~ m1_connsp_2(G_1083,'#skF_3',F_1081)
      | ~ m1_subset_1(F_1081,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_1081,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_1081,u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_162,c_59])).

tff(c_171,plain,(
    ! [F_513,H_525,G_521] :
      ( ~ r1_tarski('#skF_1'('#skF_2','#skF_4',F_513,F_513,'#skF_3',H_525,F_513,G_521),k2_xboole_0('#skF_8','#skF_9'))
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_2','#skF_4',F_513,F_513,'#skF_3',H_525,F_513,G_521))
      | ~ m1_connsp_2(H_525,'#skF_4',F_513)
      | ~ m1_connsp_2(G_521,'#skF_3',F_513)
      | ~ m1_subset_1(F_513,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_513,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_513,u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4')))
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_167])).

tff(c_174,plain,(
    ! [F_513,H_525,G_521] :
      ( ~ r1_tarski('#skF_1'('#skF_2','#skF_4',F_513,F_513,'#skF_3',H_525,F_513,G_521),k2_xboole_0('#skF_8','#skF_9'))
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_2','#skF_4',F_513,F_513,'#skF_3',H_525,F_513,G_521))
      | ~ m1_connsp_2(H_525,'#skF_4',F_513)
      | ~ m1_connsp_2(G_521,'#skF_3',F_513)
      | ~ m1_subset_1(F_513,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_513,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_513,u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_42,c_171])).

tff(c_176,plain,(
    ! [F_1084,H_1085,G_1086] :
      ( ~ r1_tarski('#skF_1'('#skF_2','#skF_4',F_1084,F_1084,'#skF_3',H_1085,F_1084,G_1086),k2_xboole_0('#skF_8','#skF_9'))
      | ~ r2_hidden('#skF_6','#skF_1'('#skF_2','#skF_4',F_1084,F_1084,'#skF_3',H_1085,F_1084,G_1086))
      | ~ m1_connsp_2(H_1085,'#skF_4',F_1084)
      | ~ m1_connsp_2(G_1086,'#skF_3',F_1084)
      | ~ m1_subset_1(F_1084,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_1084,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_1084,u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_174])).

tff(c_180,plain,(
    ! [F_513] :
      ( ~ r2_hidden('#skF_6','#skF_1'('#skF_2','#skF_4',F_513,F_513,'#skF_3','#skF_9',F_513,'#skF_8'))
      | ~ m1_connsp_2('#skF_9','#skF_4',F_513)
      | ~ m1_connsp_2('#skF_8','#skF_3',F_513)
      | ~ m1_subset_1(F_513,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_513,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_513,u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4')))
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_2')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_18,c_176])).

tff(c_183,plain,(
    ! [F_513] :
      ( ~ r2_hidden('#skF_6','#skF_1'('#skF_2','#skF_4',F_513,F_513,'#skF_3','#skF_9',F_513,'#skF_8'))
      | ~ m1_connsp_2('#skF_9','#skF_4',F_513)
      | ~ m1_connsp_2('#skF_8','#skF_3',F_513)
      | ~ m1_subset_1(F_513,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_513,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_513,u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_46,c_42,c_180])).

tff(c_185,plain,(
    ! [F_1087] :
      ( ~ r2_hidden('#skF_6','#skF_1'('#skF_2','#skF_4',F_1087,F_1087,'#skF_3','#skF_9',F_1087,'#skF_8'))
      | ~ m1_connsp_2('#skF_9','#skF_4',F_1087)
      | ~ m1_connsp_2('#skF_8','#skF_3',F_1087)
      | ~ m1_subset_1(F_1087,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_1087,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(F_1087,u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_48,c_44,c_183])).

tff(c_188,plain,
    ( ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0(k1_tsep_1('#skF_2','#skF_3','#skF_4')))
    | ~ m1_connsp_2('#skF_9','#skF_4','#skF_6')
    | ~ m1_connsp_2('#skF_8','#skF_3','#skF_6') ),
    inference(resolution,[status(thm)],[c_114,c_185])).

tff(c_192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_58,c_55,c_38,c_57,c_188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:26:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.54  
% 2.87/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.54  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k1_tsep_1 > k2_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4
% 2.87/1.54  
% 2.87/1.54  %Foreground sorts:
% 2.87/1.54  
% 2.87/1.54  
% 2.87/1.54  %Background operators:
% 2.87/1.54  
% 2.87/1.54  
% 2.87/1.54  %Foreground operators:
% 2.87/1.54  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.87/1.54  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.87/1.54  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 2.87/1.54  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 2.87/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.54  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.87/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.54  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.87/1.54  tff('#skF_7', type, '#skF_7': $i).
% 2.87/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.54  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.54  tff('#skF_6', type, '#skF_6': $i).
% 2.87/1.54  tff('#skF_2', type, '#skF_2': $i).
% 2.87/1.54  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.54  tff('#skF_9', type, '#skF_9': $i).
% 2.87/1.54  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 2.87/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.54  tff('#skF_8', type, '#skF_8': $i).
% 2.87/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.54  tff('#skF_4', type, '#skF_4': $i).
% 2.87/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.54  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.87/1.54  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.87/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.87/1.54  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.87/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.54  
% 2.98/1.57  tff(f_188, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (m1_subset_1(D, u1_struct_0(k1_tsep_1(A, B, C))) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (((E = D) & (F = D)) => (![G]: (m1_connsp_2(G, B, E) => (![H]: (m1_connsp_2(H, C, F) => (?[I]: (m1_connsp_2(I, k1_tsep_1(A, B, C), D) & r1_tarski(I, k2_xboole_0(G, H))))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_tmap_1)).
% 2.98/1.57  tff(f_144, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (m1_subset_1(D, u1_struct_0(k1_tsep_1(A, B, C))) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (((E = D) & (F = D)) => (![G]: (m1_connsp_2(G, B, E) => (![H]: (m1_connsp_2(H, C, F) => (?[I]: (((m1_subset_1(I, k1_zfmisc_1(u1_struct_0(k1_tsep_1(A, B, C)))) & v3_pre_topc(I, k1_tsep_1(A, B, C))) & r2_hidden(D, I)) & r1_tarski(I, k2_xboole_0(G, H))))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_tmap_1)).
% 2.98/1.57  tff(f_73, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & m1_pre_topc(k1_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 2.98/1.57  tff(f_32, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.98/1.57  tff(f_97, axiom, (![A, B, C]: (((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k1_tsep_1(A, B, C)) & v1_pre_topc(k1_tsep_1(A, B, C))) & v2_pre_topc(k1_tsep_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_tmap_1)).
% 2.98/1.57  tff(f_51, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 2.98/1.57  tff(c_30, plain, (m1_connsp_2('#skF_8', '#skF_3', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.98/1.57  tff(c_34, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.98/1.57  tff(c_32, plain, ('#skF_7'='#skF_5'), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.98/1.57  tff(c_56, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32])).
% 2.98/1.57  tff(c_28, plain, (m1_connsp_2('#skF_9', '#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.98/1.57  tff(c_58, plain, (m1_connsp_2('#skF_9', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_28])).
% 2.98/1.57  tff(c_40, plain, (m1_subset_1('#skF_5', u1_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.98/1.57  tff(c_55, plain, (m1_subset_1('#skF_6', u1_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_40])).
% 2.98/1.57  tff(c_38, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.98/1.57  tff(c_36, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.98/1.57  tff(c_57, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_36])).
% 2.98/1.57  tff(c_54, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.98/1.57  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.98/1.57  tff(c_44, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.98/1.57  tff(c_52, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.98/1.57  tff(c_50, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.98/1.57  tff(c_46, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.98/1.57  tff(c_42, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.98/1.57  tff(c_108, plain, (![F_1055, B_1053, G_1056, H_1054, A_1051, C_1052]: (r2_hidden(F_1055, '#skF_1'(A_1051, C_1052, F_1055, F_1055, B_1053, H_1054, F_1055, G_1056)) | ~m1_connsp_2(H_1054, C_1052, F_1055) | ~m1_connsp_2(G_1056, B_1053, F_1055) | ~m1_subset_1(F_1055, u1_struct_0(C_1052)) | ~m1_subset_1(F_1055, u1_struct_0(B_1053)) | ~m1_subset_1(F_1055, u1_struct_0(k1_tsep_1(A_1051, B_1053, C_1052))) | ~m1_pre_topc(C_1052, A_1051) | v2_struct_0(C_1052) | ~m1_pre_topc(B_1053, A_1051) | v2_struct_0(B_1053) | ~l1_pre_topc(A_1051) | ~v2_pre_topc(A_1051) | v2_struct_0(A_1051))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.98/1.57  tff(c_110, plain, (![H_1054, G_1056]: (r2_hidden('#skF_6', '#skF_1'('#skF_2', '#skF_4', '#skF_6', '#skF_6', '#skF_3', H_1054, '#skF_6', G_1056)) | ~m1_connsp_2(H_1054, '#skF_4', '#skF_6') | ~m1_connsp_2(G_1056, '#skF_3', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_55, c_108])).
% 2.98/1.57  tff(c_113, plain, (![H_1054, G_1056]: (r2_hidden('#skF_6', '#skF_1'('#skF_2', '#skF_4', '#skF_6', '#skF_6', '#skF_3', H_1054, '#skF_6', G_1056)) | ~m1_connsp_2(H_1054, '#skF_4', '#skF_6') | ~m1_connsp_2(G_1056, '#skF_3', '#skF_6') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_42, c_38, c_57, c_110])).
% 2.98/1.57  tff(c_114, plain, (![H_1054, G_1056]: (r2_hidden('#skF_6', '#skF_1'('#skF_2', '#skF_4', '#skF_6', '#skF_6', '#skF_3', H_1054, '#skF_6', G_1056)) | ~m1_connsp_2(H_1054, '#skF_4', '#skF_6') | ~m1_connsp_2(G_1056, '#skF_3', '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_44, c_113])).
% 2.98/1.57  tff(c_18, plain, (![C_401, F_513, H_525, G_521, A_17, B_273]: (r1_tarski('#skF_1'(A_17, C_401, F_513, F_513, B_273, H_525, F_513, G_521), k2_xboole_0(G_521, H_525)) | ~m1_connsp_2(H_525, C_401, F_513) | ~m1_connsp_2(G_521, B_273, F_513) | ~m1_subset_1(F_513, u1_struct_0(C_401)) | ~m1_subset_1(F_513, u1_struct_0(B_273)) | ~m1_subset_1(F_513, u1_struct_0(k1_tsep_1(A_17, B_273, C_401))) | ~m1_pre_topc(C_401, A_17) | v2_struct_0(C_401) | ~m1_pre_topc(B_273, A_17) | v2_struct_0(B_273) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.98/1.57  tff(c_22, plain, (![C_401, F_513, H_525, G_521, A_17, B_273]: (v3_pre_topc('#skF_1'(A_17, C_401, F_513, F_513, B_273, H_525, F_513, G_521), k1_tsep_1(A_17, B_273, C_401)) | ~m1_connsp_2(H_525, C_401, F_513) | ~m1_connsp_2(G_521, B_273, F_513) | ~m1_subset_1(F_513, u1_struct_0(C_401)) | ~m1_subset_1(F_513, u1_struct_0(B_273)) | ~m1_subset_1(F_513, u1_struct_0(k1_tsep_1(A_17, B_273, C_401))) | ~m1_pre_topc(C_401, A_17) | v2_struct_0(C_401) | ~m1_pre_topc(B_273, A_17) | v2_struct_0(B_273) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.98/1.57  tff(c_153, plain, (![H_1075, A_1072, G_1077, C_1073, F_1076, B_1074]: (m1_subset_1('#skF_1'(A_1072, C_1073, F_1076, F_1076, B_1074, H_1075, F_1076, G_1077), k1_zfmisc_1(u1_struct_0(k1_tsep_1(A_1072, B_1074, C_1073)))) | ~m1_connsp_2(H_1075, C_1073, F_1076) | ~m1_connsp_2(G_1077, B_1074, F_1076) | ~m1_subset_1(F_1076, u1_struct_0(C_1073)) | ~m1_subset_1(F_1076, u1_struct_0(B_1074)) | ~m1_subset_1(F_1076, u1_struct_0(k1_tsep_1(A_1072, B_1074, C_1073))) | ~m1_pre_topc(C_1073, A_1072) | v2_struct_0(C_1073) | ~m1_pre_topc(B_1074, A_1072) | v2_struct_0(B_1074) | ~l1_pre_topc(A_1072) | ~v2_pre_topc(A_1072) | v2_struct_0(A_1072))), inference(cnfTransformation, [status(thm)], [f_144])).
% 2.98/1.57  tff(c_84, plain, (![A_1039, B_1040, C_1041]: (m1_pre_topc(k1_tsep_1(A_1039, B_1040, C_1041), A_1039) | ~m1_pre_topc(C_1041, A_1039) | v2_struct_0(C_1041) | ~m1_pre_topc(B_1040, A_1039) | v2_struct_0(B_1040) | ~l1_pre_topc(A_1039) | v2_struct_0(A_1039))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.98/1.57  tff(c_2, plain, (![B_3, A_1]: (l1_pre_topc(B_3) | ~m1_pre_topc(B_3, A_1) | ~l1_pre_topc(A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.98/1.57  tff(c_88, plain, (![A_1039, B_1040, C_1041]: (l1_pre_topc(k1_tsep_1(A_1039, B_1040, C_1041)) | ~m1_pre_topc(C_1041, A_1039) | v2_struct_0(C_1041) | ~m1_pre_topc(B_1040, A_1039) | v2_struct_0(B_1040) | ~l1_pre_topc(A_1039) | v2_struct_0(A_1039))), inference(resolution, [status(thm)], [c_84, c_2])).
% 2.98/1.57  tff(c_12, plain, (![A_14, B_15, C_16]: (v2_pre_topc(k1_tsep_1(A_14, B_15, C_16)) | ~m1_pre_topc(C_16, A_14) | v2_struct_0(C_16) | ~m1_pre_topc(B_15, A_14) | v2_struct_0(B_15) | ~l1_pre_topc(A_14) | ~v2_pre_topc(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.98/1.57  tff(c_91, plain, (![B_1048, A_1049, C_1050]: (m1_connsp_2(B_1048, A_1049, C_1050) | ~r2_hidden(C_1050, B_1048) | ~v3_pre_topc(B_1048, A_1049) | ~m1_subset_1(C_1050, u1_struct_0(A_1049)) | ~m1_subset_1(B_1048, k1_zfmisc_1(u1_struct_0(A_1049))) | ~l1_pre_topc(A_1049) | ~v2_pre_topc(A_1049) | v2_struct_0(A_1049))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.98/1.57  tff(c_98, plain, (![B_1048]: (m1_connsp_2(B_1048, k1_tsep_1('#skF_2', '#skF_3', '#skF_4'), '#skF_6') | ~r2_hidden('#skF_6', B_1048) | ~v3_pre_topc(B_1048, k1_tsep_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(B_1048, k1_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_4')))) | ~l1_pre_topc(k1_tsep_1('#skF_2', '#skF_3', '#skF_4')) | ~v2_pre_topc(k1_tsep_1('#skF_2', '#skF_3', '#skF_4')) | v2_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_55, c_91])).
% 2.98/1.57  tff(c_117, plain, (~v2_pre_topc(k1_tsep_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_98])).
% 2.98/1.57  tff(c_120, plain, (~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_117])).
% 2.98/1.57  tff(c_123, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_42, c_120])).
% 2.98/1.57  tff(c_125, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_44, c_123])).
% 2.98/1.57  tff(c_126, plain, (![B_1048]: (~l1_pre_topc(k1_tsep_1('#skF_2', '#skF_3', '#skF_4')) | v2_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_4')) | m1_connsp_2(B_1048, k1_tsep_1('#skF_2', '#skF_3', '#skF_4'), '#skF_6') | ~r2_hidden('#skF_6', B_1048) | ~v3_pre_topc(B_1048, k1_tsep_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(B_1048, k1_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_4')))))), inference(splitRight, [status(thm)], [c_98])).
% 2.98/1.57  tff(c_128, plain, (~l1_pre_topc(k1_tsep_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_126])).
% 2.98/1.57  tff(c_131, plain, (~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_88, c_128])).
% 2.98/1.57  tff(c_134, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_42, c_131])).
% 2.98/1.57  tff(c_136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_44, c_134])).
% 2.98/1.57  tff(c_137, plain, (![B_1048]: (v2_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_4')) | m1_connsp_2(B_1048, k1_tsep_1('#skF_2', '#skF_3', '#skF_4'), '#skF_6') | ~r2_hidden('#skF_6', B_1048) | ~v3_pre_topc(B_1048, k1_tsep_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(B_1048, k1_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_4')))))), inference(splitRight, [status(thm)], [c_126])).
% 2.98/1.57  tff(c_140, plain, (v2_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_137])).
% 2.98/1.57  tff(c_10, plain, (![A_11, B_12, C_13]: (~v2_struct_0(k1_tsep_1(A_11, B_12, C_13)) | ~m1_pre_topc(C_13, A_11) | v2_struct_0(C_13) | ~m1_pre_topc(B_12, A_11) | v2_struct_0(B_12) | ~l1_pre_topc(A_11) | v2_struct_0(A_11))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.98/1.57  tff(c_143, plain, (~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_140, c_10])).
% 2.98/1.57  tff(c_146, plain, (v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_42, c_143])).
% 2.98/1.57  tff(c_148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_44, c_146])).
% 2.98/1.57  tff(c_149, plain, (![B_1048]: (m1_connsp_2(B_1048, k1_tsep_1('#skF_2', '#skF_3', '#skF_4'), '#skF_6') | ~r2_hidden('#skF_6', B_1048) | ~v3_pre_topc(B_1048, k1_tsep_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(B_1048, k1_zfmisc_1(u1_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_4')))))), inference(splitRight, [status(thm)], [c_137])).
% 2.98/1.57  tff(c_157, plain, (![F_1076, H_1075, G_1077]: (m1_connsp_2('#skF_1'('#skF_2', '#skF_4', F_1076, F_1076, '#skF_3', H_1075, F_1076, G_1077), k1_tsep_1('#skF_2', '#skF_3', '#skF_4'), '#skF_6') | ~r2_hidden('#skF_6', '#skF_1'('#skF_2', '#skF_4', F_1076, F_1076, '#skF_3', H_1075, F_1076, G_1077)) | ~v3_pre_topc('#skF_1'('#skF_2', '#skF_4', F_1076, F_1076, '#skF_3', H_1075, F_1076, G_1077), k1_tsep_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_connsp_2(H_1075, '#skF_4', F_1076) | ~m1_connsp_2(G_1077, '#skF_3', F_1076) | ~m1_subset_1(F_1076, u1_struct_0('#skF_4')) | ~m1_subset_1(F_1076, u1_struct_0('#skF_3')) | ~m1_subset_1(F_1076, u1_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_153, c_149])).
% 2.98/1.57  tff(c_160, plain, (![F_1076, H_1075, G_1077]: (m1_connsp_2('#skF_1'('#skF_2', '#skF_4', F_1076, F_1076, '#skF_3', H_1075, F_1076, G_1077), k1_tsep_1('#skF_2', '#skF_3', '#skF_4'), '#skF_6') | ~r2_hidden('#skF_6', '#skF_1'('#skF_2', '#skF_4', F_1076, F_1076, '#skF_3', H_1075, F_1076, G_1077)) | ~v3_pre_topc('#skF_1'('#skF_2', '#skF_4', F_1076, F_1076, '#skF_3', H_1075, F_1076, G_1077), k1_tsep_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_connsp_2(H_1075, '#skF_4', F_1076) | ~m1_connsp_2(G_1077, '#skF_3', F_1076) | ~m1_subset_1(F_1076, u1_struct_0('#skF_4')) | ~m1_subset_1(F_1076, u1_struct_0('#skF_3')) | ~m1_subset_1(F_1076, u1_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_42, c_157])).
% 2.98/1.57  tff(c_162, plain, (![F_1078, H_1079, G_1080]: (m1_connsp_2('#skF_1'('#skF_2', '#skF_4', F_1078, F_1078, '#skF_3', H_1079, F_1078, G_1080), k1_tsep_1('#skF_2', '#skF_3', '#skF_4'), '#skF_6') | ~r2_hidden('#skF_6', '#skF_1'('#skF_2', '#skF_4', F_1078, F_1078, '#skF_3', H_1079, F_1078, G_1080)) | ~v3_pre_topc('#skF_1'('#skF_2', '#skF_4', F_1078, F_1078, '#skF_3', H_1079, F_1078, G_1080), k1_tsep_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_connsp_2(H_1079, '#skF_4', F_1078) | ~m1_connsp_2(G_1080, '#skF_3', F_1078) | ~m1_subset_1(F_1078, u1_struct_0('#skF_4')) | ~m1_subset_1(F_1078, u1_struct_0('#skF_3')) | ~m1_subset_1(F_1078, u1_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_44, c_160])).
% 2.98/1.57  tff(c_26, plain, (![I_1029]: (~r1_tarski(I_1029, k2_xboole_0('#skF_8', '#skF_9')) | ~m1_connsp_2(I_1029, k1_tsep_1('#skF_2', '#skF_3', '#skF_4'), '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_188])).
% 2.98/1.57  tff(c_59, plain, (![I_1029]: (~r1_tarski(I_1029, k2_xboole_0('#skF_8', '#skF_9')) | ~m1_connsp_2(I_1029, k1_tsep_1('#skF_2', '#skF_3', '#skF_4'), '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_26])).
% 2.98/1.57  tff(c_167, plain, (![F_1081, H_1082, G_1083]: (~r1_tarski('#skF_1'('#skF_2', '#skF_4', F_1081, F_1081, '#skF_3', H_1082, F_1081, G_1083), k2_xboole_0('#skF_8', '#skF_9')) | ~r2_hidden('#skF_6', '#skF_1'('#skF_2', '#skF_4', F_1081, F_1081, '#skF_3', H_1082, F_1081, G_1083)) | ~v3_pre_topc('#skF_1'('#skF_2', '#skF_4', F_1081, F_1081, '#skF_3', H_1082, F_1081, G_1083), k1_tsep_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_connsp_2(H_1082, '#skF_4', F_1081) | ~m1_connsp_2(G_1083, '#skF_3', F_1081) | ~m1_subset_1(F_1081, u1_struct_0('#skF_4')) | ~m1_subset_1(F_1081, u1_struct_0('#skF_3')) | ~m1_subset_1(F_1081, u1_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_4'))))), inference(resolution, [status(thm)], [c_162, c_59])).
% 2.98/1.57  tff(c_171, plain, (![F_513, H_525, G_521]: (~r1_tarski('#skF_1'('#skF_2', '#skF_4', F_513, F_513, '#skF_3', H_525, F_513, G_521), k2_xboole_0('#skF_8', '#skF_9')) | ~r2_hidden('#skF_6', '#skF_1'('#skF_2', '#skF_4', F_513, F_513, '#skF_3', H_525, F_513, G_521)) | ~m1_connsp_2(H_525, '#skF_4', F_513) | ~m1_connsp_2(G_521, '#skF_3', F_513) | ~m1_subset_1(F_513, u1_struct_0('#skF_4')) | ~m1_subset_1(F_513, u1_struct_0('#skF_3')) | ~m1_subset_1(F_513, u1_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_22, c_167])).
% 2.98/1.57  tff(c_174, plain, (![F_513, H_525, G_521]: (~r1_tarski('#skF_1'('#skF_2', '#skF_4', F_513, F_513, '#skF_3', H_525, F_513, G_521), k2_xboole_0('#skF_8', '#skF_9')) | ~r2_hidden('#skF_6', '#skF_1'('#skF_2', '#skF_4', F_513, F_513, '#skF_3', H_525, F_513, G_521)) | ~m1_connsp_2(H_525, '#skF_4', F_513) | ~m1_connsp_2(G_521, '#skF_3', F_513) | ~m1_subset_1(F_513, u1_struct_0('#skF_4')) | ~m1_subset_1(F_513, u1_struct_0('#skF_3')) | ~m1_subset_1(F_513, u1_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_42, c_171])).
% 2.98/1.57  tff(c_176, plain, (![F_1084, H_1085, G_1086]: (~r1_tarski('#skF_1'('#skF_2', '#skF_4', F_1084, F_1084, '#skF_3', H_1085, F_1084, G_1086), k2_xboole_0('#skF_8', '#skF_9')) | ~r2_hidden('#skF_6', '#skF_1'('#skF_2', '#skF_4', F_1084, F_1084, '#skF_3', H_1085, F_1084, G_1086)) | ~m1_connsp_2(H_1085, '#skF_4', F_1084) | ~m1_connsp_2(G_1086, '#skF_3', F_1084) | ~m1_subset_1(F_1084, u1_struct_0('#skF_4')) | ~m1_subset_1(F_1084, u1_struct_0('#skF_3')) | ~m1_subset_1(F_1084, u1_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_44, c_174])).
% 2.98/1.57  tff(c_180, plain, (![F_513]: (~r2_hidden('#skF_6', '#skF_1'('#skF_2', '#skF_4', F_513, F_513, '#skF_3', '#skF_9', F_513, '#skF_8')) | ~m1_connsp_2('#skF_9', '#skF_4', F_513) | ~m1_connsp_2('#skF_8', '#skF_3', F_513) | ~m1_subset_1(F_513, u1_struct_0('#skF_4')) | ~m1_subset_1(F_513, u1_struct_0('#skF_3')) | ~m1_subset_1(F_513, u1_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_18, c_176])).
% 2.98/1.57  tff(c_183, plain, (![F_513]: (~r2_hidden('#skF_6', '#skF_1'('#skF_2', '#skF_4', F_513, F_513, '#skF_3', '#skF_9', F_513, '#skF_8')) | ~m1_connsp_2('#skF_9', '#skF_4', F_513) | ~m1_connsp_2('#skF_8', '#skF_3', F_513) | ~m1_subset_1(F_513, u1_struct_0('#skF_4')) | ~m1_subset_1(F_513, u1_struct_0('#skF_3')) | ~m1_subset_1(F_513, u1_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_46, c_42, c_180])).
% 2.98/1.57  tff(c_185, plain, (![F_1087]: (~r2_hidden('#skF_6', '#skF_1'('#skF_2', '#skF_4', F_1087, F_1087, '#skF_3', '#skF_9', F_1087, '#skF_8')) | ~m1_connsp_2('#skF_9', '#skF_4', F_1087) | ~m1_connsp_2('#skF_8', '#skF_3', F_1087) | ~m1_subset_1(F_1087, u1_struct_0('#skF_4')) | ~m1_subset_1(F_1087, u1_struct_0('#skF_3')) | ~m1_subset_1(F_1087, u1_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_48, c_44, c_183])).
% 2.98/1.57  tff(c_188, plain, (~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0(k1_tsep_1('#skF_2', '#skF_3', '#skF_4'))) | ~m1_connsp_2('#skF_9', '#skF_4', '#skF_6') | ~m1_connsp_2('#skF_8', '#skF_3', '#skF_6')), inference(resolution, [status(thm)], [c_114, c_185])).
% 2.98/1.57  tff(c_192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_58, c_55, c_38, c_57, c_188])).
% 2.98/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.57  
% 2.98/1.57  Inference rules
% 2.98/1.57  ----------------------
% 2.98/1.57  #Ref     : 0
% 2.98/1.57  #Sup     : 19
% 2.98/1.57  #Fact    : 0
% 2.98/1.57  #Define  : 0
% 2.98/1.57  #Split   : 5
% 2.98/1.57  #Chain   : 0
% 2.98/1.57  #Close   : 0
% 2.98/1.57  
% 2.98/1.57  Ordering : KBO
% 2.98/1.57  
% 2.98/1.57  Simplification rules
% 2.98/1.57  ----------------------
% 2.98/1.57  #Subsume      : 3
% 2.98/1.57  #Demod        : 42
% 2.98/1.57  #Tautology    : 4
% 2.98/1.57  #SimpNegUnit  : 9
% 2.98/1.57  #BackRed      : 0
% 2.98/1.57  
% 2.98/1.57  #Partial instantiations: 0
% 2.98/1.57  #Strategies tried      : 1
% 2.98/1.57  
% 2.98/1.57  Timing (in seconds)
% 2.98/1.57  ----------------------
% 2.98/1.57  Preprocessing        : 0.39
% 2.98/1.57  Parsing              : 0.20
% 2.98/1.57  CNF conversion       : 0.06
% 2.98/1.57  Main loop            : 0.23
% 2.98/1.57  Inferencing          : 0.09
% 2.98/1.57  Reduction            : 0.07
% 2.98/1.57  Demodulation         : 0.05
% 2.98/1.57  BG Simplification    : 0.02
% 2.98/1.57  Subsumption          : 0.05
% 2.98/1.57  Abstraction          : 0.01
% 2.98/1.57  MUC search           : 0.00
% 2.98/1.57  Cooper               : 0.00
% 2.98/1.57  Total                : 0.67
% 2.98/1.57  Index Insertion      : 0.00
% 2.98/1.57  Index Deletion       : 0.00
% 2.98/1.57  Index Matching       : 0.00
% 2.98/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
