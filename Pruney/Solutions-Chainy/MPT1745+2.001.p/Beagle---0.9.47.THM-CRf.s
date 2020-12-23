%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:48 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 228 expanded)
%              Number of leaves         :   35 ( 112 expanded)
%              Depth                    :   11
%              Number of atoms          :  251 (1867 expanded)
%              Number of equality atoms :    1 (   3 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k1_partfun1 > k3_funct_2 > k2_zfmisc_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_connsp_2,type,(
    k1_connsp_2: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v5_pre_topc,type,(
    v5_pre_topc: ( $i * $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_201,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v2_pre_topc(B)
              & l1_pre_topc(B) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & v2_pre_topc(C)
                  & l1_pre_topc(C) )
               => ! [D] :
                    ( ( v1_funct_1(D)
                      & v1_funct_2(D,u1_struct_0(C),u1_struct_0(A))
                      & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(A)))) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(A),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(C))
                           => ( ( r1_tmap_1(C,A,D,F)
                                & v5_pre_topc(E,A,B) )
                             => r1_tmap_1(C,B,k1_partfun1(u1_struct_0(C),u1_struct_0(A),u1_struct_0(A),u1_struct_0(B),D,E),F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tmap_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => r2_hidden(B,k1_connsp_2(A,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_connsp_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => m1_subset_1(k1_connsp_2(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_connsp_2)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => m1_subset_1(k3_funct_2(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_funct_2)).

tff(f_154,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & v2_pre_topc(C)
                & l1_pre_topc(C) )
             => ! [D] :
                  ( ( v1_funct_1(D)
                    & v1_funct_2(D,u1_struct_0(B),u1_struct_0(C))
                    & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(C)))) )
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(A))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(A)))) )
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(C))
                             => ( ( G = k3_funct_2(u1_struct_0(B),u1_struct_0(C),D,F)
                                  & r1_tmap_1(B,C,D,F)
                                  & r1_tmap_1(C,A,E,G) )
                               => r1_tmap_1(B,A,k1_partfun1(u1_struct_0(B),u1_struct_0(C),u1_struct_0(C),u1_struct_0(A),D,E),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tmap_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ( v5_pre_topc(C,B,A)
              <=> ! [D] :
                    ( m1_subset_1(D,u1_struct_0(B))
                   => r1_tmap_1(B,A,C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tmap_1)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_28,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_44,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_42,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_76,plain,(
    ! [B_228,A_229] :
      ( r2_hidden(B_228,k1_connsp_2(A_229,B_228))
      | ~ m1_subset_1(B_228,u1_struct_0(A_229))
      | ~ l1_pre_topc(A_229)
      | ~ v2_pre_topc(A_229)
      | v2_struct_0(A_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [A_230,B_231] :
      ( ~ v1_xboole_0(k1_connsp_2(A_230,B_231))
      | ~ m1_subset_1(B_231,u1_struct_0(A_230))
      | ~ l1_pre_topc(A_230)
      | ~ v2_pre_topc(A_230)
      | v2_struct_0(A_230) ) ),
    inference(resolution,[status(thm)],[c_76,c_2])).

tff(c_84,plain,
    ( ~ v1_xboole_0(k1_connsp_2('#skF_5','#skF_8'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_81])).

tff(c_87,plain,
    ( ~ v1_xboole_0(k1_connsp_2('#skF_5','#skF_8'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_84])).

tff(c_88,plain,(
    ~ v1_xboole_0(k1_connsp_2('#skF_5','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_87])).

tff(c_89,plain,(
    ! [A_232,B_233] :
      ( m1_subset_1(k1_connsp_2(A_232,B_233),k1_zfmisc_1(u1_struct_0(A_232)))
      | ~ m1_subset_1(B_233,u1_struct_0(A_232))
      | ~ l1_pre_topc(A_232)
      | ~ v2_pre_topc(A_232)
      | v2_struct_0(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [B_7,A_5] :
      ( v1_xboole_0(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_94,plain,(
    ! [A_234,B_235] :
      ( v1_xboole_0(k1_connsp_2(A_234,B_235))
      | ~ v1_xboole_0(u1_struct_0(A_234))
      | ~ m1_subset_1(B_235,u1_struct_0(A_234))
      | ~ l1_pre_topc(A_234)
      | ~ v2_pre_topc(A_234)
      | v2_struct_0(A_234) ) ),
    inference(resolution,[status(thm)],[c_89,c_6])).

tff(c_97,plain,
    ( v1_xboole_0(k1_connsp_2('#skF_5','#skF_8'))
    | ~ v1_xboole_0(u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_94])).

tff(c_100,plain,
    ( v1_xboole_0(k1_connsp_2('#skF_5','#skF_8'))
    | ~ v1_xboole_0(u1_struct_0('#skF_5'))
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_97])).

tff(c_101,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_88,c_100])).

tff(c_40,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_38,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_102,plain,(
    ! [A_236,B_237,C_238,D_239] :
      ( m1_subset_1(k3_funct_2(A_236,B_237,C_238,D_239),B_237)
      | ~ m1_subset_1(D_239,A_236)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_236,B_237)))
      | ~ v1_funct_2(C_238,A_236,B_237)
      | ~ v1_funct_1(C_238)
      | v1_xboole_0(A_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_106,plain,(
    ! [D_239] :
      ( m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_239),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_239,u1_struct_0('#skF_5'))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_36,c_102])).

tff(c_112,plain,(
    ! [D_239] :
      ( m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_239),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_239,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_106])).

tff(c_113,plain,(
    ! [D_239] :
      ( m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6',D_239),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(D_239,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_112])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_50,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_48,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_56,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_54,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_34,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_32,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_30,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_26,plain,(
    r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_198,plain,(
    ! [A_258,F_261,D_259,E_260,B_263,C_262] :
      ( r1_tmap_1(B_263,A_258,k1_partfun1(u1_struct_0(B_263),u1_struct_0(C_262),u1_struct_0(C_262),u1_struct_0(A_258),D_259,E_260),F_261)
      | ~ r1_tmap_1(C_262,A_258,E_260,k3_funct_2(u1_struct_0(B_263),u1_struct_0(C_262),D_259,F_261))
      | ~ r1_tmap_1(B_263,C_262,D_259,F_261)
      | ~ m1_subset_1(k3_funct_2(u1_struct_0(B_263),u1_struct_0(C_262),D_259,F_261),u1_struct_0(C_262))
      | ~ m1_subset_1(F_261,u1_struct_0(B_263))
      | ~ m1_subset_1(E_260,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_262),u1_struct_0(A_258))))
      | ~ v1_funct_2(E_260,u1_struct_0(C_262),u1_struct_0(A_258))
      | ~ v1_funct_1(E_260)
      | ~ m1_subset_1(D_259,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_263),u1_struct_0(C_262))))
      | ~ v1_funct_2(D_259,u1_struct_0(B_263),u1_struct_0(C_262))
      | ~ v1_funct_1(D_259)
      | ~ l1_pre_topc(C_262)
      | ~ v2_pre_topc(C_262)
      | v2_struct_0(C_262)
      | ~ l1_pre_topc(B_263)
      | ~ v2_pre_topc(B_263)
      | v2_struct_0(B_263)
      | ~ l1_pre_topc(A_258)
      | ~ v2_pre_topc(A_258)
      | v2_struct_0(A_258) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_22,plain,(
    ~ r1_tmap_1('#skF_5','#skF_4',k1_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),u1_struct_0('#skF_3'),u1_struct_0('#skF_4'),'#skF_6','#skF_7'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_204,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_4','#skF_7',k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'))
    | ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
    | ~ m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'),u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_198,c_22])).

tff(c_208,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_4','#skF_7',k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'),u1_struct_0('#skF_3'))
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_44,c_42,c_56,c_54,c_40,c_38,c_36,c_34,c_32,c_30,c_28,c_26,c_204])).

tff(c_209,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_4','#skF_7',k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'))
    | ~ m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_58,c_208])).

tff(c_210,plain,(
    ~ m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_213,plain,(
    ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_113,c_210])).

tff(c_217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_213])).

tff(c_218,plain,(
    ~ r1_tmap_1('#skF_3','#skF_4','#skF_7',k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_24,plain,(
    v5_pre_topc('#skF_7','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_219,plain,(
    m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'),u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_14,plain,(
    ! [B_29,A_17,C_35,D_38] :
      ( r1_tmap_1(B_29,A_17,C_35,D_38)
      | ~ m1_subset_1(D_38,u1_struct_0(B_29))
      | ~ v5_pre_topc(C_35,B_29,A_17)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_29),u1_struct_0(A_17))))
      | ~ v1_funct_2(C_35,u1_struct_0(B_29),u1_struct_0(A_17))
      | ~ v1_funct_1(C_35)
      | ~ l1_pre_topc(B_29)
      | ~ v2_pre_topc(B_29)
      | v2_struct_0(B_29)
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_221,plain,(
    ! [A_17,C_35] :
      ( r1_tmap_1('#skF_3',A_17,C_35,k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'))
      | ~ v5_pre_topc(C_35,'#skF_3',A_17)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(A_17))))
      | ~ v1_funct_2(C_35,u1_struct_0('#skF_3'),u1_struct_0(A_17))
      | ~ v1_funct_1(C_35)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(resolution,[status(thm)],[c_219,c_14])).

tff(c_230,plain,(
    ! [A_17,C_35] :
      ( r1_tmap_1('#skF_3',A_17,C_35,k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'))
      | ~ v5_pre_topc(C_35,'#skF_3',A_17)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(A_17))))
      | ~ v1_funct_2(C_35,u1_struct_0('#skF_3'),u1_struct_0(A_17))
      | ~ v1_funct_1(C_35)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_221])).

tff(c_248,plain,(
    ! [A_266,C_267] :
      ( r1_tmap_1('#skF_3',A_266,C_267,k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'))
      | ~ v5_pre_topc(C_267,'#skF_3',A_266)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'),u1_struct_0(A_266))))
      | ~ v1_funct_2(C_267,u1_struct_0('#skF_3'),u1_struct_0(A_266))
      | ~ v1_funct_1(C_267)
      | ~ l1_pre_topc(A_266)
      | ~ v2_pre_topc(A_266)
      | v2_struct_0(A_266) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_230])).

tff(c_251,plain,
    ( r1_tmap_1('#skF_3','#skF_4','#skF_7',k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'))
    | ~ v5_pre_topc('#skF_7','#skF_3','#skF_4')
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_3'),u1_struct_0('#skF_4'))
    | ~ v1_funct_1('#skF_7')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_248])).

tff(c_254,plain,
    ( r1_tmap_1('#skF_3','#skF_4','#skF_7',k3_funct_2(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'),'#skF_6','#skF_8'))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_34,c_32,c_24,c_251])).

tff(c_256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_218,c_254])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:49:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.38  
% 2.74/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.39  %$ r1_tmap_1 > v5_pre_topc > v1_funct_2 > r2_hidden > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k1_partfun1 > k3_funct_2 > k2_zfmisc_1 > k1_connsp_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4
% 2.74/1.39  
% 2.74/1.39  %Foreground sorts:
% 2.74/1.39  
% 2.74/1.39  
% 2.74/1.39  %Background operators:
% 2.74/1.39  
% 2.74/1.39  
% 2.74/1.39  %Foreground operators:
% 2.74/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.74/1.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.74/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.74/1.39  tff(k1_connsp_2, type, k1_connsp_2: ($i * $i) > $i).
% 2.74/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.74/1.39  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 2.74/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.74/1.39  tff('#skF_7', type, '#skF_7': $i).
% 2.74/1.39  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.74/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.74/1.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.74/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.74/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.74/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.74/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.74/1.39  tff('#skF_8', type, '#skF_8': $i).
% 2.74/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.74/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.74/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.39  tff(v5_pre_topc, type, v5_pre_topc: ($i * $i * $i) > $o).
% 2.74/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.74/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.74/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.74/1.39  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 2.74/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.39  
% 2.74/1.40  tff(f_201, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => ((r1_tmap_1(C, A, D, F) & v5_pre_topc(E, A, B)) => r1_tmap_1(C, B, k1_partfun1(u1_struct_0(C), u1_struct_0(A), u1_struct_0(A), u1_struct_0(B), D, E), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t54_tmap_1)).
% 2.74/1.40  tff(f_74, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => r2_hidden(B, k1_connsp_2(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_connsp_2)).
% 2.74/1.40  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.74/1.40  tff(f_62, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => m1_subset_1(k1_connsp_2(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_connsp_2)).
% 2.74/1.40  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 2.74/1.40  tff(f_51, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => m1_subset_1(k3_funct_2(A, B, C, D), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_funct_2)).
% 2.74/1.40  tff(f_154, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((~v2_struct_0(C) & v2_pre_topc(C)) & l1_pre_topc(C)) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, u1_struct_0(B), u1_struct_0(C))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(C))))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(A))))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((((G = k3_funct_2(u1_struct_0(B), u1_struct_0(C), D, F)) & r1_tmap_1(B, C, D, F)) & r1_tmap_1(C, A, E, G)) => r1_tmap_1(B, A, k1_partfun1(u1_struct_0(B), u1_struct_0(C), u1_struct_0(C), u1_struct_0(A), D, E), F)))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_tmap_1)).
% 2.74/1.40  tff(f_103, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (v5_pre_topc(C, B, A) <=> (![D]: (m1_subset_1(D, u1_struct_0(B)) => r1_tmap_1(B, A, C, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_tmap_1)).
% 2.74/1.40  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.74/1.40  tff(c_28, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.74/1.40  tff(c_46, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.74/1.40  tff(c_44, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.74/1.40  tff(c_42, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.74/1.40  tff(c_76, plain, (![B_228, A_229]: (r2_hidden(B_228, k1_connsp_2(A_229, B_228)) | ~m1_subset_1(B_228, u1_struct_0(A_229)) | ~l1_pre_topc(A_229) | ~v2_pre_topc(A_229) | v2_struct_0(A_229))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.74/1.40  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.41  tff(c_81, plain, (![A_230, B_231]: (~v1_xboole_0(k1_connsp_2(A_230, B_231)) | ~m1_subset_1(B_231, u1_struct_0(A_230)) | ~l1_pre_topc(A_230) | ~v2_pre_topc(A_230) | v2_struct_0(A_230))), inference(resolution, [status(thm)], [c_76, c_2])).
% 2.74/1.41  tff(c_84, plain, (~v1_xboole_0(k1_connsp_2('#skF_5', '#skF_8')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_28, c_81])).
% 2.74/1.41  tff(c_87, plain, (~v1_xboole_0(k1_connsp_2('#skF_5', '#skF_8')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_84])).
% 2.74/1.41  tff(c_88, plain, (~v1_xboole_0(k1_connsp_2('#skF_5', '#skF_8'))), inference(negUnitSimplification, [status(thm)], [c_46, c_87])).
% 2.74/1.41  tff(c_89, plain, (![A_232, B_233]: (m1_subset_1(k1_connsp_2(A_232, B_233), k1_zfmisc_1(u1_struct_0(A_232))) | ~m1_subset_1(B_233, u1_struct_0(A_232)) | ~l1_pre_topc(A_232) | ~v2_pre_topc(A_232) | v2_struct_0(A_232))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.74/1.41  tff(c_6, plain, (![B_7, A_5]: (v1_xboole_0(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.74/1.41  tff(c_94, plain, (![A_234, B_235]: (v1_xboole_0(k1_connsp_2(A_234, B_235)) | ~v1_xboole_0(u1_struct_0(A_234)) | ~m1_subset_1(B_235, u1_struct_0(A_234)) | ~l1_pre_topc(A_234) | ~v2_pre_topc(A_234) | v2_struct_0(A_234))), inference(resolution, [status(thm)], [c_89, c_6])).
% 2.74/1.41  tff(c_97, plain, (v1_xboole_0(k1_connsp_2('#skF_5', '#skF_8')) | ~v1_xboole_0(u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_28, c_94])).
% 2.74/1.41  tff(c_100, plain, (v1_xboole_0(k1_connsp_2('#skF_5', '#skF_8')) | ~v1_xboole_0(u1_struct_0('#skF_5')) | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_97])).
% 2.74/1.41  tff(c_101, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_46, c_88, c_100])).
% 2.74/1.41  tff(c_40, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.74/1.41  tff(c_38, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.74/1.41  tff(c_36, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.74/1.41  tff(c_102, plain, (![A_236, B_237, C_238, D_239]: (m1_subset_1(k3_funct_2(A_236, B_237, C_238, D_239), B_237) | ~m1_subset_1(D_239, A_236) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_236, B_237))) | ~v1_funct_2(C_238, A_236, B_237) | ~v1_funct_1(C_238) | v1_xboole_0(A_236))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.74/1.41  tff(c_106, plain, (![D_239]: (m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_239), u1_struct_0('#skF_3')) | ~m1_subset_1(D_239, u1_struct_0('#skF_5')) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | v1_xboole_0(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_36, c_102])).
% 2.74/1.41  tff(c_112, plain, (![D_239]: (m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_239), u1_struct_0('#skF_3')) | ~m1_subset_1(D_239, u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_106])).
% 2.74/1.41  tff(c_113, plain, (![D_239]: (m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', D_239), u1_struct_0('#skF_3')) | ~m1_subset_1(D_239, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_101, c_112])).
% 2.74/1.41  tff(c_58, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.74/1.41  tff(c_50, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.74/1.41  tff(c_48, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.74/1.41  tff(c_56, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.74/1.41  tff(c_54, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.74/1.41  tff(c_34, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.74/1.41  tff(c_32, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.74/1.41  tff(c_30, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.74/1.41  tff(c_26, plain, (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.74/1.41  tff(c_198, plain, (![A_258, F_261, D_259, E_260, B_263, C_262]: (r1_tmap_1(B_263, A_258, k1_partfun1(u1_struct_0(B_263), u1_struct_0(C_262), u1_struct_0(C_262), u1_struct_0(A_258), D_259, E_260), F_261) | ~r1_tmap_1(C_262, A_258, E_260, k3_funct_2(u1_struct_0(B_263), u1_struct_0(C_262), D_259, F_261)) | ~r1_tmap_1(B_263, C_262, D_259, F_261) | ~m1_subset_1(k3_funct_2(u1_struct_0(B_263), u1_struct_0(C_262), D_259, F_261), u1_struct_0(C_262)) | ~m1_subset_1(F_261, u1_struct_0(B_263)) | ~m1_subset_1(E_260, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_262), u1_struct_0(A_258)))) | ~v1_funct_2(E_260, u1_struct_0(C_262), u1_struct_0(A_258)) | ~v1_funct_1(E_260) | ~m1_subset_1(D_259, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_263), u1_struct_0(C_262)))) | ~v1_funct_2(D_259, u1_struct_0(B_263), u1_struct_0(C_262)) | ~v1_funct_1(D_259) | ~l1_pre_topc(C_262) | ~v2_pre_topc(C_262) | v2_struct_0(C_262) | ~l1_pre_topc(B_263) | ~v2_pre_topc(B_263) | v2_struct_0(B_263) | ~l1_pre_topc(A_258) | ~v2_pre_topc(A_258) | v2_struct_0(A_258))), inference(cnfTransformation, [status(thm)], [f_154])).
% 2.74/1.41  tff(c_22, plain, (~r1_tmap_1('#skF_5', '#skF_4', k1_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), u1_struct_0('#skF_3'), u1_struct_0('#skF_4'), '#skF_6', '#skF_7'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.74/1.41  tff(c_204, plain, (~r1_tmap_1('#skF_3', '#skF_4', '#skF_7', k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')) | ~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8'), u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_198, c_22])).
% 2.74/1.41  tff(c_208, plain, (~r1_tmap_1('#skF_3', '#skF_4', '#skF_7', k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')) | ~m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8'), u1_struct_0('#skF_3')) | v2_struct_0('#skF_3') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_44, c_42, c_56, c_54, c_40, c_38, c_36, c_34, c_32, c_30, c_28, c_26, c_204])).
% 2.74/1.41  tff(c_209, plain, (~r1_tmap_1('#skF_3', '#skF_4', '#skF_7', k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')) | ~m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8'), u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_58, c_208])).
% 2.74/1.41  tff(c_210, plain, (~m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8'), u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_209])).
% 2.74/1.41  tff(c_213, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_113, c_210])).
% 2.74/1.41  tff(c_217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_213])).
% 2.74/1.41  tff(c_218, plain, (~r1_tmap_1('#skF_3', '#skF_4', '#skF_7', k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8'))), inference(splitRight, [status(thm)], [c_209])).
% 2.74/1.41  tff(c_24, plain, (v5_pre_topc('#skF_7', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_201])).
% 2.74/1.41  tff(c_219, plain, (m1_subset_1(k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8'), u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_209])).
% 2.74/1.41  tff(c_14, plain, (![B_29, A_17, C_35, D_38]: (r1_tmap_1(B_29, A_17, C_35, D_38) | ~m1_subset_1(D_38, u1_struct_0(B_29)) | ~v5_pre_topc(C_35, B_29, A_17) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_29), u1_struct_0(A_17)))) | ~v1_funct_2(C_35, u1_struct_0(B_29), u1_struct_0(A_17)) | ~v1_funct_1(C_35) | ~l1_pre_topc(B_29) | ~v2_pre_topc(B_29) | v2_struct_0(B_29) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.74/1.41  tff(c_221, plain, (![A_17, C_35]: (r1_tmap_1('#skF_3', A_17, C_35, k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')) | ~v5_pre_topc(C_35, '#skF_3', A_17) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(A_17)))) | ~v1_funct_2(C_35, u1_struct_0('#skF_3'), u1_struct_0(A_17)) | ~v1_funct_1(C_35) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17) | v2_struct_0(A_17))), inference(resolution, [status(thm)], [c_219, c_14])).
% 2.74/1.41  tff(c_230, plain, (![A_17, C_35]: (r1_tmap_1('#skF_3', A_17, C_35, k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')) | ~v5_pre_topc(C_35, '#skF_3', A_17) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(A_17)))) | ~v1_funct_2(C_35, u1_struct_0('#skF_3'), u1_struct_0(A_17)) | ~v1_funct_1(C_35) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17) | v2_struct_0(A_17))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_221])).
% 2.74/1.41  tff(c_248, plain, (![A_266, C_267]: (r1_tmap_1('#skF_3', A_266, C_267, k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')) | ~v5_pre_topc(C_267, '#skF_3', A_266) | ~m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_3'), u1_struct_0(A_266)))) | ~v1_funct_2(C_267, u1_struct_0('#skF_3'), u1_struct_0(A_266)) | ~v1_funct_1(C_267) | ~l1_pre_topc(A_266) | ~v2_pre_topc(A_266) | v2_struct_0(A_266))), inference(negUnitSimplification, [status(thm)], [c_58, c_230])).
% 2.74/1.41  tff(c_251, plain, (r1_tmap_1('#skF_3', '#skF_4', '#skF_7', k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')) | ~v5_pre_topc('#skF_7', '#skF_3', '#skF_4') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_3'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_30, c_248])).
% 2.74/1.41  tff(c_254, plain, (r1_tmap_1('#skF_3', '#skF_4', '#skF_7', k3_funct_2(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'), '#skF_6', '#skF_8')) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_34, c_32, c_24, c_251])).
% 2.74/1.41  tff(c_256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_218, c_254])).
% 2.74/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.41  
% 2.74/1.41  Inference rules
% 2.74/1.41  ----------------------
% 2.74/1.41  #Ref     : 0
% 2.74/1.41  #Sup     : 27
% 2.74/1.41  #Fact    : 0
% 2.74/1.41  #Define  : 0
% 2.74/1.41  #Split   : 7
% 2.74/1.41  #Chain   : 0
% 2.74/1.41  #Close   : 0
% 2.74/1.41  
% 2.74/1.41  Ordering : KBO
% 2.74/1.41  
% 2.74/1.41  Simplification rules
% 2.74/1.41  ----------------------
% 2.74/1.41  #Subsume      : 5
% 2.74/1.41  #Demod        : 69
% 2.74/1.41  #Tautology    : 4
% 2.74/1.41  #SimpNegUnit  : 19
% 2.74/1.41  #BackRed      : 1
% 2.74/1.41  
% 2.74/1.41  #Partial instantiations: 0
% 2.74/1.41  #Strategies tried      : 1
% 2.74/1.41  
% 2.74/1.41  Timing (in seconds)
% 2.74/1.41  ----------------------
% 2.74/1.41  Preprocessing        : 0.37
% 2.74/1.41  Parsing              : 0.20
% 2.74/1.41  CNF conversion       : 0.05
% 2.74/1.41  Main loop            : 0.24
% 2.74/1.41  Inferencing          : 0.09
% 2.74/1.41  Reduction            : 0.08
% 2.74/1.41  Demodulation         : 0.05
% 2.74/1.41  BG Simplification    : 0.02
% 2.74/1.41  Subsumption          : 0.04
% 2.74/1.41  Abstraction          : 0.01
% 2.74/1.41  MUC search           : 0.00
% 2.74/1.41  Cooper               : 0.00
% 2.74/1.41  Total                : 0.64
% 2.74/1.41  Index Insertion      : 0.00
% 2.74/1.41  Index Deletion       : 0.00
% 2.74/1.41  Index Matching       : 0.00
% 2.74/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
